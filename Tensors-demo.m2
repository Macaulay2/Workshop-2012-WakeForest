restart
debug loadPackage("Tensors")
R=QQ[a,b,c]

--making modules of tensors:
M=tensorModule(R,{3,3,4})
N=tensorModule(R,{2,4,3})
M_7
M_(0,1,3)

--making tensors that know where they live:
T=tensor'{{a,b},{-b,a}}
U=tensor'{{b,c},{-c,b}}

--Basic operations on tensors:
3*T+U
T**U
entries oo

--higher order transpositions of a single tensor:
tcomp({{T**T,i,j,k,l}})
T**T
tcomp({{T**T,j,i,k,l}})

--Symbolic composition of tensors
--using index notation:
tcomp({{T,i,j},{U,j,k}},{j})
tcomp({{T,i,j},{U,j,k}},{})
tcomp({{T,i,j},{U,j,k}})

--changing index names changes the output:
tcomp({{T,j,i},{U,i,k}})

--Einstein summation:
--repeated indices are
--automatically summed over
esum({{T,i,j},{U,j,k}})

 (tensors,indicesByTensor,summationIndices)=
 ({r,r},{{i,j},{j,k}},{j})
s=exprn
expressionFunction
summationList_0


R=QQ[x]
m=map(R^1,R^1,matrix{{2_R}})
M=R^1
N=image m
M==N--true
M===N--false
peek M
peek N
M===prune N
peek prune N

isFreeModule N
isFreeModule M

x=new MutableHashTable
k=2--user, outside
x.k = 5--inside
x#k
x.k--user, works

M.factors

factors=7
M.factors

e=(hold i+i)*(hold (2+2))
dse(e,{i=>5})
tis(e,{i=>5})

R=QQ[x]
a=tm(R,{2,2})
b=tm(R,{4})
a==b
a===b

gs=getSymbol

R=QQ[x]



a=(tensorArray t)


T=it(t,{i,j})

dimensions T.tensor

     val#(gs"name")  = toString(sym);
     val#sv    = noinput -> vector val#sl;
     val#sm    = noinput -> stateMatrix (val#sl);
     val#dm    = noinput -> matrix {val#dl};
     globalAssignFunction(sym,val);
     )
DRV.GlobalReleaseHook = globalReleaseFunction

smus{legend,name,sl,dl,sv,sm,dm}

want:

A.name
A.array
A.tensor
A.indices
A.dimensions



a = new CacheTable from {1=>2}
b = new CacheTable from {3=>4}
a==b
a===b

ita=indexedTensorArray=method()



----

----




m=matrix{{1,2},{3,4}}
m#((keys m)#3)

a=tensorArray({4,4},(i,j)->i^2+j^2)
t = tensor' a
time tt=t^4;--0.002 secs
time aa=tensorArray tt;--3.2 secs
time tt'=tensor' aa;--0.76 secs--cache not working
tt'==tt
tt'===tt
time aa=tensorArray tt;--0.76 secs



time tt_(4,4,3,2,1,0)
time aa_(4,,3,,,0)
time te

time aa_(1,2,1,2,1,2)
time 


R=QQ[x]
A=ta{{1,2,3},{4,5,6},{7,8,9}}
B=ta{{11,12,x},{14,15,16},{17,18,19}}
C=ta{{21,22,23},{24,25,26},{27,28,29}}
C'=ta{{21,22,23},{24,25,26}}

--works with dsub, fails with dse
tac({{A,i,j},{A,i,j}},{i,j})

--works:
time tac(for l in 1..1000 list {A,i,j},{i,j});
--2.3 secs with dsub
--5.9 secs with dse
time D=ta({10,10},(i,j)->i^2+j^2);

time tac({{D,i,j},{D,i,j}},{i,j});

time fold(for i in 0..5 list toList (1..10),(i,j)->i**j);
--0.3 secs
time fold(for i in 0..5 list toList (1..10),(i,j)->i**j);

--with list: 0.7 t0 1.3

--want to sum over stuff
--want to product stuff

holder

arraysum({i,j,k},array,expression)



--works:
tac({{A,1,j},{B,j,k},{C,j,l}},{j})
--should return error:
tac({{A,1,j},{B,j,k},{C',j,l}},{j})
--works:
tac({{A,1,j},{B,j,k},{C',l,j}},{j})
tac({{A,1,j},{B,j,k},{C',l,j}},{})
time 
tac(for t in 0..10 list {A,i,j},{i,j})


time sum flatten for i in 0..1000 list for j in 0..1000 list j

time value dsub(sum for i in 0..10000 list (hold j)^2,{j=>3})
time dse(sum for i in 0..10000 list (hold j)^2,{j=>3})


