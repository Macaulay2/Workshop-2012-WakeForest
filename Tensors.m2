newPackage(
	"Tensors",
    	Version => "0.01", 
    	Date => "August 5, 2012",
    	Authors => {
	     {Name => "Andrew Critch"},
	     {Name => "Luke Oeding"},
	     {Name => "Claudiu Raicu", Email => "claudiu@math.berkeley.edu", HomePage => "http://math.berkeley.edu/~claudiu/"},
	     {Name => "Amelia Taylor"}
	     },
    	Headline => "tensors"
    	)
--ToDo:
--1)new type and methods for tensors
--on creation of new tensor space
--e.g. t_(1,0,0) should work.
--2)tensor' to make tensors
--3)equality testing of tensor spaces

export {TensorArray, tensorArray, nestedListAccess}
exportMutable {TemporaryTensorList, TemporaryIndexList}
--
nA = nestedListAccess = method()
nA(Thing,Sequence) := (x,l) -> (
     if l === () then return x else error: "too many indices?")
nA(VisibleList,Sequence) := (N,l) -> (
     if l === () then return N;
     if l_0 === null then return apply(N,i->nA(i,take(l,{1,-1+#l})));
     return nA(N#(l#0),take(l,{1,-1+#l})))
---

export{associativeCartesianProduct,isRectangular}

List**List := (L,M) -> flatten for l in L list for m in M list (l,m)
Sequence**Sequence := (L,M) -> toSequence flatten for l in L list for m in M list (l,m)
acp=associativeCartesianProduct=method()
acp VisibleList := L -> fold((i,j)->(i**j)/splice,L)
---
isRectangular=method()
isRectangular VisibleList := L -> (d:=dimensions ta L;
     inds:=associativeCartesianProduct(d/(i->0..<i));
     for i in inds do try L_i else return false;
     return true)

--assert isRectangular ta {{1,2},{3,4,5}} == false


-----
TensorArray  = new Type of List
net TensorArray  := T -> netList new List from T
TensorArray_ZZ := (N,n) -> N_(1:n)
-----
TensorArray_Sequence:=(N,s) -> (
     if not all(s,i->instance(i,ZZ) or instance(i,Symbol)) then error "expected a list of integers or symbols";
     if not all(s,i->instance(i,ZZ)) then return (hold N)_(hold s);
     return ta nA(N,s);
     )
-----dimensions=method()
dimensions TensorArray := L -> (d:={};
     while class L === TensorArray do (d=d|{#L},L=L_0);
     return d)
---


ta=tensorArray=method()
tensorArray List := L -> new TensorArray from L

--need to test rectangularity
--tensorArray Thing := x -> x
--TensorArray_Sequence:=(N,s) -> ta nA(N,s)

----
----

export{nestedList}
nestedList=method()
nestedList(List,List):=(dims,L) -> (
     if not product dims == #L then error "dimension mismatch in nestedList";
     while #dims>1 do (
	  d:=last dims;
	  L = for i in 0..<round(#L/d) list take(L,{i*d,(i+1)*d-1});
	  dims = take(dims,{0,-2+#dims}));
     return L)

--
tensorArray Vector := v -> ta nestedList (dimensions v,entries v);
--

export{einsteinSummation}
einsteinSummation = method()
einsteinSummation (List,List) := (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     allIndices:=sort toList set splice indicesByTensor;
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k==i));
     repeatedIndices:=select(allIndices,i->1<#flatten indexLocations i);
     singleIndices:=toList((allIndices - (set repeatedIndices)));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (dimensions(tensors_t))_l);
     TemporaryTensorList=tensors;
     TemporaryIndexList=indicesByTensor;
     sumCommand:=concatenate for r in repeatedIndices list "sum for i"|toString(r)|" in 0..<"|toString(indexRange r)|" list ";
     plugInSequence:= seq -> for ind in indicesByTensor list (
	  toSequence for i in ind list if member(i,singleIndices) then seq_0 else getSymbol("i"|toString i)
	       do if member(i,singleIndices) then seq=remove(seq,0));
     summand:=seq->(
	  TemporaryIndexList=plugInSequence(seq);
	  return "(TemporaryTensorList_0)_"|toString(TemporaryIndexList_0)|(
     	       concatenate for tensorNumber in 1..<numberOfTensors list "*(TemporaryTensorList_"|toString(tensorNumber)|")_"|toString(TemporaryIndexList_tensorNumber)));
     listCommand:=concatenate for s in singleIndices list "for i"|toString(s)|" in 0..<"|toString(indexRange s)|" list ";
     return ta value(listCommand|sumCommand|summand ((singleIndices)/(j->getSymbol("i"|toString(j))))))
einsteinSummation List := L -> einsteinSummation(L/first,L/(i->toSequence remove(i,0)))
es=einsteinSummation

export{sumOut}
sumOut=method()
sumOut (List,List) := (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     summationIndices:= toList set select(splice indicesByTensor,i->not class i === ZZ);
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k===i));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (dimensions(tensors_t))_l);
     TemporaryTensorList=tensors;
     TemporaryIndexList=indicesByTensor;
     sumCommand:= concatenate for r in summationIndices list "sum for "|toString(r)|" in 0..<"|toString(indexRange r)|" list ";
     summand:= "(TemporaryTensorList_0)_"|toString(indicesByTensor_0)|(
     concatenate for tensorNumber in 1..<numberOfTensors list "*(TemporaryTensorList_"|toString(tensorNumber)|")_"|toString(TemporaryIndexList_tensorNumber));
     return value(sumCommand|summand))
sumOut List := L -> sumOut(L/first,L/(i->toSequence remove(i,0)))

----------------
--Tensor Modules
----------------
export{Tensor,TensorModule}
Tensor=new Type of Vector
TensorModule = new Type of Module
TensorModule.synonym="tensor module"
tm=tensorModule = method()
tm Module := M -> (
     Q:=newClass(TensorModule,Tensor,M);
     Q.cache.dimensions = {numgens M};
--     Q.cache.factors = {M};
     Q
     )
tm Module := M -> (
     Q:=newClass(TensorModule,Tensor,M);
     Q.cache.dimensions = {numgens M};
--     Q.cache.factors = {M};
     Q
     )
tm (Ring,List) := (R,L) -> (
     d:=product L;
     Q:=newClass(TensorModule,Tensor,R^d);
     Q.cache.dimensions = L;
--     Q.cache.factors = {M};
     Q
     )
tm (Module,List) := (M,L) -> (
     d:=product L;
     if not numgens M == d then error "dimension mismatch";
     tm(ring M,L)
     )
net TensorModule := M -> (net new Module from M)|", "|"tensor of order "|toString(#M.cache.dimensions)|", dimensions "|toString(M.cache.dimensions)
TensorModule#{Standard,AfterPrint} = M -> (
     << endl;				  -- double space
     n := rank ambient M;
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << ring M
     << "-TensorModule";
{*
     if M.?generators then
     if M.?relations then << ", subquotient of " << ambient M
     else << ", submodule of " << ambient M
     else if M.?relations then << ", quotient of " << ambient M
     else if n > 0 then (
	  << ", free";
	  if not all(degrees M, d -> all(d, zero)) 
	  then << ", degrees " << if degreeLength M === 1 then flatten degrees M else degrees M;
	  );
*}
     << endl;
     )
module TensorModule := M -> new Module from M
dimensions TensorModule := M -> M.cache.dimensions
dimensions Tensor := v -> (
--     if not instance(class v,TensorModule) then error "'dimensions' expected an element of a TensorModule";
     dimensions class v
     )
export{toTensor,isTensor}
tt=toTensor=method()
toTensor (List,TensorModule) := (L,M) -> (
     t:=tensorArray L;
     if not dimensions t == dimensions M then error "dimension mismatch";
     new M from vector ultimate(flatten,L)
     )
toTensor (List) := L -> (
     t:=tensorArray L;
     dims:=dimensions t;
     f:=ultimate(flatten,L);
     R:=commonRing f;
     M:=tensorModule(R,dims);
     new M from vector f
     )
isTensor=method()
isTensor Thing := x -> instance(class x,TensorModule)

--
TensorModule**TensorModule := (M,N) -> (
     P:=(module M) ** (module N);
     P=tensorModule P;
     P.cache.dimensions=M.cache.dimensions|N.cache.dimensions;
--     P.cache.factors=M.cache.factors|N.cache.factors;
     P
     )
TensorModule^ZZ := (M,n) -> (
     P:=(module M)^n;
     P=tensorModule P;
     P.cache.dimensions=toList flatten (n:M.cache.dimensions);
--     P.cache.factors=toList flatten (n:M.cache.factors);
     P
     )
TensorModule++TensorModule := (M,N) -> (
     if not #dimensions M == #dimensions N then error "dimension mismatch in TensorModule++TensorModule";
     P:=(module M)++(module N);
     P=tensorModule P;
     P.cache.dimensions=M.cache.dimensions + N.cache.dimensions;
--     P.cache.factors=M.cache.factors ++ N.cache.factors;
     P
     )


----PICK UP HERE


--
beginDocumentation()

TEST ///
///

TEST  ///
///

end


restart
debug loadPackage"Tensors"

R=QQ[x]
f=map(R^2,R^2,{{0,1},{1,0}})
M=tm R^2
f=map(M,M,{{0,1},{1,0}})
ta ((f**f)*((M_0)**(M_1)))
f**f
t=(M_0)**(M_1)
instance(M,Module)
g=f**f**f
g*t

--check rectangular in tel

L={{1,2},{3,4}}
toTensor(ta toTensor({L,L,L},M++M++M),M)
t=toTensor({L,L+L,L+L+L+L},((tm R^3)**M))
toTensor(ta t,((tm R^3)**M))==t


while not all(L,i->not class i == List)

new Function from flatten



L=nestedList({2,2,2},{1,2,3,4,5,6,7,8})

L={{{1,2,3},{4,5,6}},{{5,6,7},{8,9,10}}}
--entry:
nA(L,(1,1,2))

--slices:
nA(L,(1,))
nA(L,(1,,))
nA(L,(,1,))
nA(L,(,,1))
nA(L,(,1,1))
nA(L,(1,,1))

ta {{1,2},{3,4}}
ta {L,L}

T = ta L
dimensions T

R=QQ[x]
M=tm R^2
P=M**M**M
t=sum for i in 0..7 list i*P_i
dimensions t
t=(M_0)**(M_1)**(M_0)
ta t
dimensions t

(1,2,3)**(4,5,6)

L={{1,2},{3,4},{5,6}}
acp L

isRectangular {{1,2},{3}}
isRectangular T

----
x=symbol x
R=QQ[x_1..x_27]
m0=ta entries genericMatrix(R,3,3)
m1=ta entries genericMatrix(R,x_10,3,3)
m2=ta entries genericMatrix(R,x_19,3,3)

isRectangular m1

A=tel{{1,2,3},{4,5,6},{7,8,9}}
B=tel{{11,12,x_1},{14,15,16},{17,18,19}}
C=tel{{21,22,23},{24,25,26},{27,28,29}}

printWidth=1000
es({{A,i,j},{B,j,k},{C,j,l}})


----
sumOut({m0,m1,m2},{(2,i),(i,1),(i,0)})
sumOut{{m0,2,i},{m1,i,1},{m2,i,0}}
sumOut({m0,m0,m0},{(0,i),(i,1),(j,0)})

-----
R=QQ[x]
M=tm R^2
module M

M.cache.dimensions
keys M.cache
N=(M**M)++(M**M)
((M**M**M)**(M**M**M)).cache.dimensions

(M_1) ** (M_0)


--TRYING TO IMPROVE EINSTEIN SUMMATION

ESUM=EinsteinSummationMethodFunction=new Type of MethodFunction
esum=new ESUM from method(Dispatch=>Thing)
ESUM_List := (esum,inds) -> (
     if not all(inds,i->instance(i,Symbol)) then error "expected a list of Symbols";
     f = i->1;
     r
     )
esum_{i,j}
getParsing (hold 1+2)
(expression 1+2)+(expression 1+2)
hold 1+2

hold' = method(Dispatch => Thing, TypicalValue => Expression)
hold' Expression := identity
hold' Thing := x -> ((new Holder from {x})+(new Holder from {x}))
hold' 1+2+3

test=new Keyword from abc
test
f = method(Dispatch=>Thing)
f Thing:= x -> (Holder{x}+Holder{x})
f 1
f 1+2
f(hold 1+2)
f hold 1+2
(hold 1) ..< (hold 5)
value ((hold M)_0)
Holder{1}

new Sum from {hold 1+2,hold 1+2}


(new Expression from {3})+(new Expression from {3})
new Sum from {hold (M_0)_j,M_0}


f=method()
f Thing:= x -> new Holder from {hold x+hold x}
f(hold 1+2)

es(A_(2,3) * B_(j,k))
A

f hold i
i=hold i
(hold symbol M)_(hold symbol i)
hold a_k
hold m_k

(f 1+2)
(f 1)+2
f(1+2)
--     return (hold x)+(hold x);
     return s+s;
     )
f(hold 1+2)
f 1+2

g=f@@hold
g 1+2
f hold 1+2
code hold
f(hold i*j)
(hold 1+2)+(hold 3+4)

KeyWord 
class(for)

f (hold i*j)
g=hold
g i*j

(hold i*j) + (hold i*j)
s= hold i*j
s+s





