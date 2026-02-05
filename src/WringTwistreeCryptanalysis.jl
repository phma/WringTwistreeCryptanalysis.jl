module WringTwistreeCryptanalysis

using WringTwistree,Base.Threads,OffsetArrays,CairoMakie
using JSON3,SpecialFunctions,Roots,CpuId,Printf
using WringTwistree.Sboxes.Permute
import OffsetArrays:Origin
import WringTwistree:encryptN2!,encryptN!,findMaxOrder
export big3Power,big5Power,rotations1,rotations256,clutch1,match,clutch,plotClutch
export clutchDiffGrow1,clutchDiffGrow,probRotateTogether,clutch3Lengths
export invProbRotateTogether,extrapolate
export measureSpeedWring,measureSpeedTwistree
export Bucket3,ins!,powerSpectrum,nonlinearity,listLinearPermutations
export roundCompress1,roundCompress256,round2Compress1,round2Compress256,round2Stats
export pairdiffs,cumulate!,diffTwistreeLen,diffTwistreeLen2

# clutchMsgLen is the message length for clutch cryptanalysis.
# Three values are used: 7776, 8192, and 10000.
# They have 0, 2, and 1 bytes untouched by mix3 in each round.

const clutchRounds=8

key96_0 = "Водворетраванатраведрова.Нерубидрованатраведвора!"
key96_1 = "Водворетраванатраведрова.Нерубидрованатраведвора "
key96_2 = "Водворетраванатраведрова,Нерубидрованатраведвора!"
key96_3 = "Водворетраванатраведрова,Нерубидрованатраведвора "
# Russian tongue twister
# In the yard is grass, on the grass is wood.
# Do not chop the wood on the grass of yard.
# 96 bytes in UTF-8 with single bit changes.

key30_0 = "Παντοτε χαιρετε!"
key30_1 = "Πάντοτε χαιρετε!"
key30_2 = "Παντοτε χαίρετε!"
key30_3 = "Πάντοτε χαίρετε!"
# Always rejoice! 1 Thess. 5:16.

key6_0 = "aerate"
key6_1 = "berate"
key6_2 = "cerate"
key6_3 = "derate"

wring96_0 = keyedWring(key96_0)
wring96_1 = keyedWring(key96_1)
wring96_2 = keyedWring(key96_2)
wring96_3 = keyedWring(key96_3)
wring30_0 = keyedWring(key30_0)
wring30_1 = keyedWring(key30_1)
wring30_2 = keyedWring(key30_2)
wring30_3 = keyedWring(key30_3)
wring6_0 = keyedWring(key6_0)
wring6_1 = keyedWring(key6_1)
wring6_2 = keyedWring(key6_2)
wring6_3 = keyedWring(key6_3)

tw96_0 = keyedTwistree(key96_0)
tw96_1 = keyedTwistree(key96_1)
tw96_2 = keyedTwistree(key96_2)
tw96_3 = keyedTwistree(key96_3)
tw30_0 = keyedTwistree(key30_0)
tw30_1 = keyedTwistree(key30_1)
tw30_2 = keyedTwistree(key30_2)
tw30_3 = keyedTwistree(key30_3)
tw6_0 = keyedTwistree(key6_0)
tw6_1 = keyedTwistree(key6_1)
tw6_2 = keyedTwistree(key6_2)
tw6_3 = keyedTwistree(key6_3)

function big3Power(n::Integer)
  big(3)^(n*53÷84)
end

function big5Power(n::Integer)
  big(5)^(n*146÷339)
end

function measureSpeedWring(numBytes::Integer,parseq::Symbol=:default)
  wring=keyedWring("")
  if numBytes>0 && numBytes<1048576
    numTimes=2097152÷numBytes
  else
    numTimes=1
  end
  buf=rand(UInt8,numBytes)
  startcc=cpucycle()
  startns=time_ns()
  for i in 1:numTimes
    encrypt!(wring,buf,parseq)
  end
  finishcc=cpucycle()
  finishns=time_ns()
  (finishcc-startcc)/numBytes/numTimes,(finishns-startns)/numBytes/numTimes
end

function measureSpeedTwistree(numBytes::Integer,parseq::Symbol=:default)
  tw=keyedTwistree("")
  if numBytes>0 && numBytes<16777216
    numTimes=33554432÷(numBytes+256)
  else
    numTimes=1
  end
  buf=rand(UInt8,numBytes)
  startcc=cpucycle()
  startns=time_ns()
  for i in 1:numTimes
    hash!(tw,buf,parseq)
  end
  finishcc=cpucycle()
  finishns=time_ns()
  (finishcc-startcc)/numBytes/numTimes,(finishns-startns)/numBytes/numTimes
end

function match(as::Vector{UInt8},bs::Vector{UInt8})
  mapreduce(x->4-count_ones(x),+,as.⊻bs,init=0)
end

function messageArray(pt::Integer,clutchMsgLen::Integer)
  ret=Vector{UInt8}(undef,clutchMsgLen)
  for i in 1:clutchMsgLen
    ret[i]=UInt8(pt&0xff)
    pt>>=8
  end
  ret
end

"""
    powerTransform(buf::OffsetVector{<:Integer})

Takes a vector Boolean function and transforms it so that the constant term
is in [0], the linear terms are in [1],[2],[4],[8],..., the quadratic terms
are in [3],[5],[6],[9],[10],[12],..., and so on. I don't know what this is
called. It seems to be a variant of the pseudo-Hadamard transform.
"""
function powerTransform(buf::OffsetVector{<:Integer})
  tmp0=copy(buf)
  tmp1=copy(buf)
  sz=length(buf)
  h=sz÷2
  if ispow2(sz) && Origin(buf)==Origin((0,))
    while h>0
      for i in 0:sz-1
	j=i⊻h
	if i>j
	  @inbounds tmp1[i]=tmp0[j]⊻tmp0[i]
	else
	  @inbounds tmp1[i]=tmp0[i]
	end
      end
      tmp0,tmp1=tmp1,tmp0
      h÷=2
    end
  end
  tmp0
end

function powerSpectrum(buf::OffsetVector{<:Integer})
  # "power" means exponentiation, not energy per time.
  spectrum=OffsetVector(fill(0,count_ones(length(buf)-1)+1),-1)
  pt=powerTransform(buf)
  for i in eachindex(pt)
    if pt[i]!=0
      spectrum[count_ones(i)]+=1
    end
  end
  spectrum
end

nonlinearity(buf)=sum(powerSpectrum(buf)[2:end])

#####################################
# Cryptanalysis of the key schedule #
#####################################

"""
    listLinearPermutations()

Lists the indices of linear permutations that `permut8!` can do. There are 1083
out of 1344 linear permutations of 8 things, which is between 3.3% and 1/30 of all
32768 permutations that `permut8!` can do.
"""
function listLinearPermutations()
  ret=OffsetVector(Int16[],-1)
  for i in 0:32767
    ys=OffsetVector([0,1,2,3,4,5,6,7],-1)
    permut8!(ys,0,i)
    if nonlinearity(ys)==0
      push!(ret,i)
    end
  end
  ret
end

linearIndices=listLinearPermutations()

"""
    mixedLinear(inds::Vector{<:Integer})

Compute how nonlinear is a permutation composed of 96 linear permutations.
The answer is, about as nonlinear as a permutation composed of arbitrary
permutations of eight (around 240). The argument is a vector of up to
96 integers in [0,1083).
"""
function mixedLinear(inds::Vector{<:Integer})
  key=OffsetVector(UInt16[],-1)
  for i in inds
    push!(key,linearIndices[i])
  end
  while length(key)<96
    push!(key,linearIndices[0])
  end
  nonlinearity(permute256(key))
end

#################################
# Clutch cryptanalysis of Wring #
#################################

struct Bucket3 # Holds up to 3 distinct integers
  cont::Vector{Int}
end

function ins!(b::Bucket3,n::Int)
  if length(b.cont)<3 && n∉b.cont
    push!(b.cont,n)
  end
  b
end

function incomplete(b::Bucket3)
  length(b.cont)>0 && length(b.cont)<3
end

function countPairs(ns)
  nsort=sort(ns) # assumed to start at 1
  sum=0
  cnt=0
  for i in eachindex(nsort)
    if i>1 && nsort[i]==nsort[i-1]
      cnt+=1
    else
      cnt=0
    end
    sum+=cnt
  end
  sum
end

function rotations1(wring::Wring,pt::Integer,clutchMsgLen::Integer)
  buf=messageArray(pt,clutchMsgLen)
  rots=encryptN!(wring,clutchRounds,buf)
  acc=zero(rots[1])
  for i in eachindex(rots)
    acc=(acc+rots[i])%(8*clutchMsgLen)
    rots[i]=acc
  end
  rots
end

function rotations256(wring::Wring,pt::Integer,n::Integer,clutchMsgLen::Integer)
  ret=OffsetArray(Vector{Vector{Int64}}(undef,256),0:255)
  @threads for j in [0,128]
    for i in j:j+127
      ret[i]=rotations1(wring,pt⊻(big(i)<<(8*n)),clutchMsgLen)
    end
  end
  ret
end

struct Jiggle
  val0	::UInt8
  val1	::UInt8
end

struct Sidematch
  sideways  ::Int
  matches   ::Int
end

function jiggleC2(wring,pt,n,val,clutchMsgLen::Integer)
  buf=messageArray(pt⊻(big(val)<<(8*n)),clutchMsgLen)
  rot=encryptN!(wring,2,buf)
  (buf,rot[1])
end

function clutch1(wring::Wring,pt::Integer,n::Integer,clutchMsgLen::Integer)
  rotations=rotations256(wring,pt,n,clutchMsgLen)
  totalRotStats=Float64[]
  togetherRotStats=Float64[]
  jiggle=Jiggle[]
  bar0=0
  ciphertext2=OffsetArray(fill((UInt8[],0),256),0:255)
  for i in 1:clutchRounds
    push!(totalRotStats,countPairs(map(x->x[i],rotations))/(128*255))
    push!(togetherRotStats,countPairs(map(x->x[1:i],rotations))/(128*255))
  end
  for i in 0:255
    for j in 0:i-1
      if rotations[i][2]==rotations[j][2] && 
	 rotations[i][1]!=rotations[j][1]
	push!(jiggle,Jiggle(i,j))
      end
      if rotations[i][2]==rotations[j][2] && 
	 rotations[i][1]==rotations[j][1]
	bar0+=1
      end
    end
  end
  for i in eachindex(jiggle)
    if length(ciphertext2[jiggle[i].val0][1])==0
      ciphertext2[jiggle[i].val0]=([0x0],0)
    end
    if length(ciphertext2[jiggle[i].val1][1])==0
      ciphertext2[jiggle[i].val1]=([0x0],0)
    end
  end
  @threads for i in eachindex(ciphertext2)
    if length(ciphertext2[i][1])==1
      ciphertext2[i]=jiggleC2(wring,pt,n,i,clutchMsgLen)
    end
  end
  sidematch=Sidematch[]
  for j in jiggle
    push!(sidematch,
	  Sidematch(ciphertext2[j.val1][2]-ciphertext2[j.val0][2],
		    match(ciphertext2[j.val1][1],ciphertext2[j.val0][1])))
  end
  (totalRotStats,togetherRotStats,sidematch,bar0)
end

function clutchDiffGrow1(wring,pt,n,clutchMsgLen::Integer)
  rotations=rotations256(wring,pt,n,clutchMsgLen)
  diffs=fill(Int[],255*128)
  sum0=fill(0,clutchRounds) # count
  sum1=fill(0,clutchRounds) # total
  mean=fill(0.0,clutchRounds)
  sum2=fill(0.0,clutchRounds) # second moment about mean, so float
  @threads for m in 1:(255*128)
    i=round(Int,√(2*m))
    j=m-(i*(i-1)÷2)-1
    r=0
    while r<clutchRounds && rotations[i][r+1]==rotations[j][r+1]
      r+=1
    end
    if (r>1)
      buf0=messageArray(pt⊻(big(i)<<(8*n)),clutchMsgLen)
      buf1=messageArray(pt⊻(big(j)<<(8*n)),clutchMsgLen)
      diffs[m]=encryptN2!(wring,r,buf0,buf1)
    end
  end
  for m in 1:(255*128)
    for i in eachindex(diffs[m])
      sum0[i]+=1
      sum1[i]+=diffs[m][i]
    end
  end
  for i in 1:clutchRounds
    if sum0[i]>0
      mean[i]=sum1[i]/sum0[i]
    end
  end
  for m in 1:(255*128)
    for i in eachindex(diffs[m])
      sum2[i]+=(diffs[m][i]-mean[i])^2
    end
  end
  (sum0,sum1,sum2,mean)
end

function clutch(wring::Wring,wringName::String,clutchMsgLen::Integer)
  #wringName is the short name of the Wring; it will be part of the filename
  pt1=big3Power(clutchMsgLen*8)
  statsTotal=fill(0.0,clutchRounds)
  statsTogether=fill(0.0,clutchRounds)
  bar0Total=0
  sideways=Int[]
  matches=Int[]
  buckets=Dict{Int,Bucket3}()
  h=findMaxOrder(clutchMsgLen)
  n=0
  cont=true
  while cont
    n+=1
    (tot,tog,smatch,bar0)=clutch1(wring,pt1*n,(h*n)%clutchMsgLen,clutchMsgLen)
    statsTotal=statsTotal.+tot
    statsTogether=statsTogether.+tog
    bar0Total+=bar0
    GC.gc()
    for sm in smatch
      push!(sideways,sm.sideways)
      push!(matches,sm.matches)
      if !haskey(buckets,sm.sideways)
	buckets[sm.sideways]=Bucket3([])
      end
      ins!(buckets[sm.sideways],sm.matches)
    end
    print('\r',n,' ',length(buckets),' ',length(sideways),' ',bar0Total)
    cont=n<16 || length(buckets)<21 || statsTogether[5]==0
    sumsw=0
    for (s,b) in buckets
      if incomplete(b)
	cont=true
      end
      sumsw+=s
      if s==0
	error("Zero bucket")
      end
    end
    if sumsw!=0
      cont=true
    end
    if n>2048
      cont=false
    end
  end
  println()
  statsTotal/=n
  statsTogether/=n
  file=open("clutch-"*wringName*"-"*string(clutchMsgLen)*".dat",write=true)
  println(file,statsTotal)
  println(file,statsTogether)
  println(file,length(sideways))
  println(file,n)
  for i in eachindex(sideways)
    println(file,[sideways[i],matches[i]])
  end
  close(file)
  (statsTotal,statsTogether,buckets)
end

function clutch3Lengths(wring::Wring,wringName::String)
  tasks=Task[]
  push!(tasks,@spawn clutch(wring,wringName,7776))
  push!(tasks,@spawn clutch(wring,wringName,8192))
  push!(tasks,@spawn clutch(wring,wringName,10000))
  for t in tasks
    wait(t)
  end
end

function plotClutch(wringName::String,bytes::Int)
  file=open("clutch-"*wringName*"-"*string(bytes)*".dat",read=true)
  sub="wring"*wringName*" "*string(bytes)*" bytes"
  statsTotalJ=JSON3.read(readline(file))
  statsTogetherJ=JSON3.read(readline(file))
  n=JSON3.read(readline(file))
  println(JSON3.read(readline(file))," iterations")
  sidewaysJ=Int[]
  matchesJ=Int[]
  sideways=Int[]
  matches=Int[]
  buckets=Dict{Int,Bucket3}()
  barData=Dict{Int,Int}()
  barKeys=Int[]
  barValues=Int[]
  for i in 1:n
    line=JSON3.read(readline(file))
    push!(sidewaysJ,line[1])
    push!(matchesJ,line[2])
    if !haskey(buckets,line[1])
      buckets[line[1]]=Bucket3([])
    end
    ins!(buckets[line[1]],line[2])
    if !haskey(barData,line[1])
      barData[line[1]]=0
    end
    barData[line[1]]+=1
  end
  for (k,v) in barData
    push!(barKeys,k)
    push!(barValues,v)
  end
  statsTotal=Float64[]
  statsTogether=Float64[]
  for i in 1:clutchRounds
    if statsTotalJ[i]>0
      push!(statsTotal,statsTotalJ[i])
    end
    if statsTogetherJ[i]>0
      push!(statsTogether,statsTogetherJ[i])
    end
  end
  for i in eachindex(sidewaysJ)
    if !incomplete(buckets[sidewaysJ[i]])
      push!(sideways,sidewaysJ[i])
      push!(matches,matchesJ[i])
    end
  end
  sm=Figure(size=(1189,841))
  smax=Axis(sm[1,1],
    title="Clutch Cryptanalysis Jiggle",
    subtitle=sub,
    xlabel="Difference of bits rotated",
    ylabel="Bits matched")
  violin!(smax,sideways,matches)
  bg=Figure(size=(1189,841))
  bgax=Axis(bg[1,1],
    title="Clutch Cryptanalysis Jiggle",
    subtitle=sub,
    xlabel="Difference of bits rotated",
    ylabel="Frequency")
  barplot!(bgax,barKeys,barValues,bar_labels=[string(i) for i in barValues])
  dk=Figure(size=(1189,841))
  dkax=Axis(dk[1,1],
    title="Clutch Cryptanalysis Decay",
    subtitle=sub,
    xlabel="Rounds",
    xticks=1:clutchRounds,
    ylabel="Fraction that rotate together",
    yscale=log10)
  lines!(dkax,eachindex(statsTotal),statsTotal,label="Total")
  lines!(dkax,eachindex(statsTogether),statsTogether,label="Together")
  axislegend(dkax)
  save("clutch-jiggle-"*wringName*"-"*string(bytes)*".svg",sm)
  save("clutch-bar-"*wringName*"-"*string(bytes)*".svg",bg)
  save("clutch-decay-"*wringName*"-"*string(bytes)*".svg",dk)
end

function clutchDiffGrow(wring::Wring,iters::Int,clutchMsgLen::Integer)
  pt1=big3Power(clutchMsgLen*8)
  sum0s=Vector{Int}[]
  sum1s=Vector{Int}[]
  mean=Float64[]
  h=findMaxOrder(clutchMsgLen)
  for n in 1:iters
    (sum0,sum1,sum2,mean1)=clutchDiffGrow1(wring,pt1*n,(h*n)%clutchMsgLen)
    print('\r',n)
    push!(sum0s,sum0)
    push!(sum1s,sum1)
  end
  sum0=fill(0,clutchRounds)
  sum1=fill(0,clutchRounds)
  for n in 1:iters
    sum0.+=sum0s[n]
    sum1.+=sum1s[n]
  end
  for i in 1:clutchRounds
    if sum0[i]>0
      push!(mean,sum1[i]/sum0[i])
    end
  end
  (mean,sum0)
end

# Computes the probability that two messages rotate together in a round, given
# the number of bytes different after the mix3 step. Since clutchDiffGrow
# computes how many bytes are different before mix3, this involves some guesswork.
function probRotateTogether(bytesDiff::Float64)
  #gamma(bytesDiff*16+1)/gamma(bytesDiff*8+1)^2/2^(bytesDiff*16)
  #the above overflows between 10 and 11 bytes.
  exp(loggamma(bytesDiff*16+1)-2*loggamma(bytesDiff*8+1)-log(2)*bytesDiff*16)
end

function invProbRotateTogether(prob::Float64)
  f(x)=probRotateTogether(x)-prob
  find_zero(f,0)
end

const remaining=
  [ 0.12432304600402871		# These are averages of the fraction of pairs
  , 0.008628181400061255	# of messages that remain rotating together in
  , 0.00035145559108221895	# the 10kB messages with 8 of the keys. The sixth
  , 9.077912826916976e-6	# number is 1.8690370242777442e-9, but is omitted
  , 1.5139199896649726e-7	# because it's only one pair out of >535 million.
  ]

function extrapolate()
  frac=1.0
  bytesDiff=1.0
  for i in 1:5
    roundLeft=remaining[i]/frac
    bytesDiff=invProbRotateTogether(roundLeft)
    frac=remaining[i]
    println(i,' ',bytesDiff,' ',roundLeft,' ',frac)
  end
  for i in 6:16
    bytesDiff*=2
    roundLeft=probRotateTogether(bytesDiff)
    frac*=roundLeft
    println(i,' ',bytesDiff,' ',roundLeft,' ',frac)
  end
end

###########################################################
# Differential cryptanalysis of Wring with small messages #
###########################################################

# Small messages range from 3 to 27 bytes. It is pointless to cryptanalyze Wring
# with a one-byte message, as there are almost as many distinct keys (2^1536) as
# invertible functions from a byte to a byte (256!≈2^1684). The smallest message
# on which mix3 operates is 3 bytes, so that's where I start. This range
# includes 8 and 16 bytes, which are common block sizes of block ciphers.

const smallDiffsIters=1048576

"""
    mutable struct Diff1

Used in cryptanalysis of both small-message Wring and Twistree. `count` is the
number of differences accumulated; `ones`, which starts at [0], has as many
elements as there are bits in the differences. So if you have accumulated 513
differences of three bytes, `count` would be 513, and `ones` would be a vector
with indices from 0 to 23.
"""
mutable struct Diff1
  count	::Int32
  ones	::OffsetVector{Int32}
end

"""
    normalize(d::Diff1)

Turn the counts in `d` into numbers in [-1,1], where 1 means always the same,
0 means different half the time, and -1 means always different.
"""
function normalize(d::Diff1)
  map(x->1-2*x/d.count,d.ones)
end

function smallDiffsOneBit(wring::Wring,nrond::Integer,bytes::Integer,bit::Integer)
  pt1=big3Power(8*bytes)
  diff=Diff1(smallDiffsIters,OffsetVector(fill(0,bytes*8),-1))
  for n in 1:diff.count
    buf0=messageArray(pt1*n,bytes)
    buf1=messageArray(pt1*n⊻(big(1)<<bit),bytes)
    encryptN!(wring,nrond,buf0)
    encryptN!(wring,nrond,buf1)
    buf0=buf0.⊻buf1
    for i in eachindex(diff.ones)
      diff.ones[i]+=(buf0[i÷8+1]>>(i%8))&1
    end
  end
  diff
end

function smallDiffsTwoBits(wring::Wring,nrond::Integer,bytes::Integer,bit0::Integer,bit1::Integer)
  pt1=big3Power(8*bytes)
  diff=Diff1(smallDiffsIters,OffsetVector(fill(0,bytes*8),-1))
  for n in 1:diff.count
    buf0=messageArray(pt1*n⊻(big(1)<<bit0),bytes)
    buf1=messageArray(pt1*n⊻(big(1)<<bit1),bytes)
    encryptN!(wring,nrond,buf0)
    encryptN!(wring,nrond,buf1)
    buf0=buf0.⊻buf1
    for i in eachindex(diff.ones)
      diff.ones[i]+=(buf0[i÷8+1]>>(i%8))&1
    end
  end
  diff
end

#############################
# Cryptanalysis of Twistree #
#############################

function roundCompress!(tw::Twistree,buf::Vector{UInt8},sboxalt::Integer)
  WringTwistree.Compress.roundCompress!(tw.sbox,buf,sboxalt)
end

function roundCompress1(tw::Twistree,pt::Integer,blockLen::Integer,sboxalt::Integer)
  buf=messageArray(pt,blockLen)
  nOnes=roundCompress!(tw,buf,sboxalt)
  (nOnes,buf)
end

function round2Compress1(tw::Twistree,pt::Integer,blockLen::Integer,sboxalt::Integer)
  buf=messageArray(pt,blockLen)
  nOnes1=roundCompress!(tw,buf,sboxalt)
  nOnes2=roundCompress!(tw,buf,sboxalt)
  (nOnes1,nOnes2,buf)
end

function roundCompress256(tw::Twistree,pt::Integer,n::Integer,
			  blockLen::Integer,sboxalt::Integer)
  ret=OffsetArray(fill((0,[0x0]),256),0:255)
  @threads for i in 0:255
    ret[i]=roundCompress1(tw,pt⊻(big(i)<<(8*n)),blockLen,sboxalt)
  end
  ret
end

function round2Compress256(tw::Twistree,pt::Integer,n::Integer,
			   blockLen::Integer,sboxalt::Integer)
  ret=OffsetArray(fill((0,0,[0x0]),256),0:255)
  @threads for i in 0:255
    ret[i]=round2Compress1(tw,pt⊻(big(i)<<(8*n)),blockLen,sboxalt)
  end
  ret
end

function pairdiffs(comps::OffsetVector{Tuple{Int,Vector{UInt8}}})
  diffs=Tuple{UInt8,Vector{UInt8}}[]
  for i in eachindex(comps)
    for j in eachindex(comps)
      if i<j && comps[i][1]==comps[j][1]
        push!(diffs,(UInt8((i⊻j)&255),comps[i][2].⊻comps[j][2]))
      end
    end
  end
  diffs
end

function pairdiffs(comps::OffsetVector{Tuple{Int,Int,Vector{UInt8}}})
  diffs=Tuple{UInt8,Vector{UInt8}}[]
  for i in eachindex(comps)
    for j in eachindex(comps)
      if i<j && comps[i][1]==comps[j][1] && comps[i][2]==comps[j][2]
        push!(diffs,(UInt8((i⊻j)&255),comps[i][3].⊻comps[j][3]))
      end
    end
  end
  diffs
end

"""
    round2Stats(comps::OffsetVector{Tuple{Int,Int,Vector{UInt8}}})

Estimate from the output of `round2Compress256` the probability that two blocks
that differ in one byte and are passed through two rounds are rotated by the
same amount in the first round and in both rounds.
"""
function round2Stats(comps::OffsetVector{Tuple{Int,Int,Vector{UInt8}}})
  round1same=round2same=0
  for i in eachindex(comps)
    for j in eachindex(comps)
      if i<j
	round1same+=comps[i][1]==comps[j][1]
	round2same+=comps[i][1]==comps[j][1] && comps[i][2]==comps[j][2]
      end
    end
  end
  totalPairs=length(comps)*(length(comps)-1)÷2
  (round1same/totalPairs,round2same/totalPairs)
end

CumDiffs=Vector{Vector{Diff1}}
# First index is the byte index within the input block (1-96)
# Second index is the difference at that byte (1-255)
# Int is the count of pairs with that difference at that byte
# Third index is the bit index, and Int is the total difference

function cumulate!(cd::CumDiffs,byteIndex::Integer,diffs::Vector{Tuple{UInt8,Vector{UInt8}}})
  while length(cd)<byteIndex
    push!(cd,Diff1[])
  end
  while length(cd[byteIndex])<255
    push!(cd[byteIndex],Diff1(0,OffsetVector(Int[],-1)))
  end
  for d in diffs
    indif=d[1] # indif is never 0
    cd[byteIndex][indif].count+=1
    while length(cd[byteIndex][indif].ones)<8*length(d[2])
      push!(cd[byteIndex][indif].ones,0)
    end
    for i in 0:length(d[2])*8-1
      cd[byteIndex][indif].ones[i]+=(d[2][i÷8+1]>>(i%8))&1
    end
  end
end

"""
    normalize(cd::CumDiffs)

Normalize all the `Diff1`s in `cd`.
"""
function normalize(cd::CumDiffs)
  nd=Vector{OffsetVector{Float64}}[]
  for i in cd
    push!(nd,OffsetVector{Float64}[])
    for j in i
      push!(nd[end],normalize(j))
    end
  end
  nd
end

"""
    diffTwistreeLen(tw::Twistree,len::Integer)

Differentially cryptanalyzes one round of Twistree, with the input being of the
specified length, which must be a multiple of 4 in the interval (32,96].
"""
function diffTwistreeLen(tw::Twistree,len::Integer)
  @assert len>32 && len<=96 && len%4==0
  pt1=big3Power(len*8)
  cd0=CumDiffs()
  cd1=CumDiffs()
  h=findMaxOrder(len)
  for i in 1:2048
    pt=i*pt1
    byteIndex=(i*h)%len
    cumulate!(cd0,byteIndex+1,pairdiffs(roundCompress256(tw,pt,byteIndex,len,0)))
    cumulate!(cd1,byteIndex+1,pairdiffs(roundCompress256(tw,pt,byteIndex,len,1)))
    @printf "%d  \r" i
    flush(stdout)
  end
  cd0,cd1
end

"""
    diffTwistreeLen2(tw::Twistree,len::Integer)

Differentially cryptanalyzes two rounds of Twistree, with the input being of the
specified length, which must be a multiple of 4 in the interval (36,96].
"""
function diffTwistreeLen2(tw::Twistree,len::Integer)
  @assert len>36 && len<=96 && len%4==0
  pt1a=big3Power(len*8)
  pt1b=big5Power(len*8)
  cd0a=CumDiffs()
  cd1a=CumDiffs()
  cd0b=CumDiffs()
  cd1b=CumDiffs()
  h=findMaxOrder(len)
  round1same0=round1same1=round2same0=round2same1=0
  iters=16384
  for i in 1:iters
    pta=i*pt1a		# 0x9669 is so that the two plaintexts
    ptb=(i+0x9669)*pt1b # don't end in many zeros at the same time
    byteIndex=(i*h)%len
    rc=round2Compress256(tw,pta,byteIndex,len,0)
    cumulate!(cd0a,byteIndex+1,pairdiffs(rc))
    r1s,r2s=round2Stats(rc)
    round1same0+=r1s
    round2same0+=r2s
    rc=round2Compress256(tw,ptb,byteIndex,len,0)
    cumulate!(cd0b,byteIndex+1,pairdiffs(rc))
    r1s,r2s=round2Stats(rc)
    round1same0+=r1s
    round2same0+=r2s
    rc=round2Compress256(tw,pta,byteIndex,len,1)
    cumulate!(cd1a,byteIndex+1,pairdiffs(rc))
    r1s,r2s=round2Stats(rc)
    round1same1+=r1s
    round2same1+=r2s
    rc=round2Compress256(tw,ptb,byteIndex,len,1)
    cumulate!(cd1b,byteIndex+1,pairdiffs(rc))
    r1s,r2s=round2Stats(rc)
    round1same1+=r1s
    round2same1+=r2s
    @printf "%d  \r" i
    flush(stdout)
  end
  ([round1same0,round2same0,round1same1,round2same1]./(2*iters),
   reshape([normalize(cd0a),normalize(cd1a),normalize(cd0b),normalize(cd1b)],2,2))
  #normalize(cd0a)
end

end # module WringTwistreeCryptanalysis
