module WringTwistreeCryptanalysis

using WringTwistree,Base.Threads,OffsetArrays,CairoMakie
using JSON3,SpecialFunctions,Roots,CpuId
export big3Power,rotations1,rotations256,clutch1,match,clutch,plotClutch
export clutchDiffGrow1,clutchDiffGrow,probRotateTogether
export invProbRotateTogether,extrapolate
export measureSpeedWring,measureSpeedTwistree
export Bucket3,ins!

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

function measureSpeedWring(numBytes::Integer,parseq::Symbol=:default)
  wring=keyedWring("")
  buf=rand(UInt8,numBytes)
  startcc=cpucycle()
  startns=time_ns()
  encrypt!(wring,buf,parseq)
  finishcc=cpucycle()
  finishns=time_ns()
  (finishcc-startcc)/numBytes,(finishns-startns)/numBytes
end

function measureSpeedTwistree(numBytes::Integer,parseq::Symbol=:default)
  tw=keyedTwistree("")
  buf=rand(UInt8,numBytes)
  startcc=cpucycle()
  startns=time_ns()
  hash!(tw,buf,parseq)
  finishcc=cpucycle()
  finishns=time_ns()
  (finishcc-startcc)/numBytes,(finishns-startns)/numBytes
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

function big3Power(n::Integer)
  big(3)^(n*53÷84)
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

function rotations1(wring,pt::Integer,clutchMsgLen::Integer)
  buf=messageArray(pt,clutchMsgLen)
  rots=WringTwistree.encryptN!(wring,clutchRounds,buf)
  acc=zero(rots[1])
  for i in eachindex(rots)
    acc=(acc+rots[i])%(8*clutchMsgLen)
    rots[i]=acc
  end
  rots
end

function rotations256(wring,pt,n::Integer,clutchMsgLen::Integer)
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
  rot=WringTwistree.encryptN!(wring,2,buf)
  (buf,rot[1])
end

function clutch1(wring,pt,n,clutchMsgLen::Integer)
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
      diffs[m]=WringTwistree.encryptN2!(wring,r,buf0,buf1)
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
  h=WringTwistree.findMaxOrder(clutchMsgLen)
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
  h=WringTwistree.findMaxOrder(clutchMsgLen)
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

end # module WringTwistreeCryptanalysis
