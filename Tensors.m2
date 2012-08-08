newPackage(
	"Tensors",
    	Version => "0.01", 
    	Date => "August 5, 2012",
    	Authors => {
	     {Name => "Andrew Critch"},
	     {Name => "Luke Oeding"},
	     {Name => "Claudiu Raicu", Email => "claudiu@math.berkeley.edu", HomePage => "http://math.berkeley.edu/~claudiu/"},
	     },
    	Headline => "tensors"
    	)
 --Macaulay2-1.4/share/Macaulay2/Core/matrix1.m2 
 --needs to replaced
 --for this package to work  
   
--ToDo:
--3) Tensor#net ... 
--4) command for dropping 1's in dimension list
--5) TensorArray afterprint
--6) Make multiplication faster

exportMutable {TemporaryTensorList, TemporaryIndexList}

export{associativeCartesianProduct,
     nestedListAccess,isRectangular,rectangularNestedList,
     tryHashApplication,deepSubstitution,
     tensorIndexSubstitution}
export{TensorArray, tensorArray}
export{einsteinSummation}
export{Tensor,TensorModule}
export{tensor',isTensor}
export{sumOut}


--
---------------------------
--Methods for nested lists
---------------------------
{*The following cartesian product lists have sequences
as their entries, rather than lists.  this is intentional, 
both for consistency with Set**Set, and for planned later 
use of nested lists of sequences of indices.
*}

List**List := (L,M) -> flatten for l in L list for m in M list (l,m)
Sequence**Sequence := (L,M) -> join apply(L,l->apply(M,m->(l,m)))

acp=--INTERNAL ABBREVIATION
associativeCartesianProduct = method()
associativeCartesianProduct VisibleList := L -> (
     p:=fold((i,j)->(i**j)/splice,L);
     if not class p_0 === Sequence then p=p/(i->1:i);
     p
     )


--Compute the initial dimensions of a list;
--if the list is nested and rectangular
--this equals its array dimension:
--INTERNAL METHOD:
initialDimensions=method()
initialDimensions List := L -> (d:={};
     while instance(L,List) do (d=d|{#L},L=L_0);
     return d)

--A recursive function for access to 
--elements of nested lists:
nla=--INTERNAL ABBREVIATION
nestedListAccess = method()
nla(Thing,Sequence) := (x,l) -> (
     if l === () then return x else error: "nestedListAccess: too many indices?")
nla(VisibleList,Sequence) := (N,l) -> (
     if l === () then return N;
     if l_0 === null then return apply(N,i->nla(i,take(l,{1,-1+#l})));
     return nla(N#(l#0),take(l,{1,-1+#l})))

---Recursive function to test if a nested list is rectangular
---
isrect=--INTERNAL ABBREVIATION
isRectangular = method()
isrect(Thing) := (x) -> true
isrect(List) := (L) -> (
     if not instance(L_0,List) then return all(L,i->not instance(i,List));
     all(L,i->instance(i,List) and isrect(i) and #i==#L_0)
     )

--Function to make a rectangular nested list
--from a list
rnl=--INTERNAL ABBREVIATION
rectangularNestedList = method()
rnl(List,List):=(dims,L) -> (
     if not product dims == #L then error "rectangularNestedList: dimension mismatch";
     while #dims>1 do (
	  d:=last dims;
	  L = for i in 0..<round(#L/d) list take(L,{i*d,(i+1)*d-1});
	  dims = take(dims,{0,-2+#dims}));
     return L)

-------------------------------------------
--Summing expresions over symbolic indices
------------------------------------------
--Turning a hash table into a function
--that acts like the identity on missing keys:
tha=--INTERNAL ABBREVIATION
tryHashApplication = method()
tha HashTable := h -> (i -> try h#i else i)
tha List := L -> tha hashTable L

--Turning a hash table into a function
--that modifies expressions.  The function
--recurses into everything except types 
--listed in Stops=>{...}
exportMutable{Stops}
dsub=--INTERNAL ABBREVIATION
deepSubstitution=method(Options=>{Stops=>{Thing}})
dsub HashTable := opts -> h -> (
     f:=method(Dispatch=>Thing);
     for T in opts.Stops do f T := x -> (tha h)x;
     f BasicList := e -> apply(e,f);
     f
     )
dsub List := opts -> L -> dsub hashTable L
dsub Option := opts -> o -> dsub {o}
dsub (Thing,HashTable) := opts -> (x,subs) -> (dsub subs) x
dsub (Thing,List) := opts -> (x,subs) -> (dsub subs) x
dsub (Thing,Option) := opts -> (x,subs) -> (dsub subs) x

--Same as above, except this routine
--tries to evaluate expressions when possible,
--otherwise leaving them as holders
dse=--INTERNAL ABBREVIATION
deepSubstitutionEvaluation=method(Options=>{Stops=>{Thing}})
dse HashTable := opts -> h -> (
     f:=method(Dispatch=>Thing);
     for T in opts.Stops do f T := x -> (
	  r:=(tha h)x;
	  try value r else r
	  );
     f BasicList := e -> (
	  ev:=apply(e,f);
	  try value ev else ev
	  );
     f
     )
dse List := opts -> L -> dse hashTable L
dse Option := opts -> o -> dse {o}
dse (Thing,HashTable) := opts -> (x,subs) -> (dse subs) x
dse (Thing,List) := opts -> (x,subs) -> (dse subs) x
dse (Thing,Option) := opts -> (x,subs) -> (dse subs) x

--###############
--I expected dse to be much faster than
--dsub for tensor arrays, but it turns out
--to be about 50 times slowed for multiplying
--9x9 matrices
--###############


tis=--INTERNAL ABBREVIATION
tensorIndexSubstitution = method()
tis Thing := x -> dsub(x,Stops=>{TensorArray})
tis (Thing,HashTable) := (x,subs) -> (tis subs) x
tis (Thing,List) := (x,subs) -> (tis subs) x
tis (Thing,Option) := (x,subs) -> (tis subs) x

--Removal from BasicList objects
--delete'=deleteFromBasicList=method()
--delete' (Thing,BasicList) := (x,v) -> new class v from delete(x,new List from v)

rea=removeEmptyAdjacencies=method()
rea Expression := exprn -> (
     exprn=new class exprn from delete((),new List from exprn);
     if #exprn==1 then exprn=(exprn#0);
     exprn
     )
rea Thing := x -> x

--Turning an expression including certain symbols
--into a function that takes those symbols
--as arguments, recursing only into sequences
ef=expressionFunction=method()
ef (Expression,List) := (exprn,args) -> (
     exprn=rea exprn;
     if not all(args,i->instance(i,Symbol)) then error "expressionFunction expected a list of symbols";
     if #args == 0 then return value(exprn);
     subber:=method(Dispatch=>Thing);
     subber Sequence := s -> tis for i in 0..<#s list (args_i => s_i);
     subber Thing := x -> tis{args_0 => x};
     f:=method(Dispatch=>Thing);
     f Thing := x -> (
	  ev:=((subber x) exprn);
	  try value ev else ev
	  );
     f
     )
ef (Thing,List) := (const,args) -> (x -> const)

----Test expressions:
TEST ///
(0..5)/(i->value((dsub{j=>i}) (hold 2)^j))
(0..5)/(i->value((tis{j=>i}) (hold 2)^j))
f=ef((hold i)^j+k,{i,j,k})
f(4,5,6)
///
----


----------------------------
--Tensor Arrays
----------------------------
TensorArray  = new Type of List
net TensorArray  := T -> netList new List from T
TensorArray.cache = new CacheTable
TensorArray_ZZ := (N,n) -> N_(1:n)
-----
TensorArray_Sequence:=(N,s) -> (
     if not all(s,i->instance(i,ZZ) or instance(i,Symbol) or instance(i,Nothing)) then error "TensorArray_Sequence: expected a list of integers or symbols";
     if not all(s,i->instance(i,ZZ) or instance(i,Nothing)) then return (hold N)_(hold s);
     l:= nla(N,s);
     if instance(l,List) then return ta l;
     l
     )
-----
dimensions=method()
--This method assumes the tensor array is rectangular,
--which will be tested when the array is built
--with tensorArray()
dimensions TensorArray := L -> (d:={};
     while instance(L,TensorArray) do (d=d|{#L},L=L_0);
     return d)
---
ta=
tensorArray=method()
tensorArray Thing := x -> x
tensorArray List := L -> (
     if not isrect(L) then return "error: nested list is not rectangular";
     new TensorArray from L
     )
tensorArray (List,List) := (dims,L) -> new TensorArray from rnl(dims,L)

tensorArray (List,Vector) := (dims,v) -> new TensorArray from rnl(dims,entries v);

--
--deep application of functions
deepApply =method()
deepApply(Thing,Function):=(x,f) -> f x
deepApply(List,Function):=(L,f) -> apply(L,(i->deepApply(i,f)))
TensorArray / Function := (t,f) -> deepApply(t,f)
Function \ TensorArray := (f,t) -> deepApply(t,f)

--The canonical tensor array, whose entry at
--position I is I
tpl=tensorPositionList = method()
tpl List := dims -> toList((#dims:0)..toSequence(dims/(i->i-1)))

cta=canonicalTensorArray = method()
cta List := dims -> ta rnl(dims,(tpl dims))

--Building a TensorArray using a function which
--takes position sequences to values:
tensorArray (List,Function) := (dims,f) -> (cta dims)/f


--Test expressions:
TEST///
R=QQ[x]
A=ta{{1,2,3},{4,5,6},{7,8,9}}
B=ta{{11,12,x},{14,15,16},{17,18,19}}
C=ta{{21,22,23},{24,25,26},{27,28,29}}
C'=ta{{21,22,23},{24,25,26}}
D=ta({3,3,3},(i,j,k)->i^2+j^2+k^2)
e=A_(2,j) * B_(j,k) * C_(k,1)
///


-------------------------------
--Composition of tensor arrays
-------------------------------
tac=
tensorArrayComposition = method()
tensorArrayComposition (List,List,List) := (tensors,indicesByTensor,summationIndices) -> (
     if not all(summationIndices,i->instance(i,Symbol)) then error "expected summation indices to be a list of symbols";
     numberOfTensors:=#tensors;
     indicesByTensor=indicesByTensor/toSequence;
     allIndices:=toList set splice indicesByTensor;
     ZZindices:=(select(allIndices,i->class i === ZZ));
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k===i));
     outputIndices:=toList(((allIndices - (set summationIndices)))-(set ZZindices));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     dimTensorAtIndex:=(t,l)->(dimensions(tensors_t))_l;
     variableIndices:=allIndices-set(ZZindices);
     --check dimensions match
     for i in variableIndices do (
	  idims:=flatten for t in tensorsWithIndex i list (
	       for l in ((indexLocations i)_t) list dimTensorAtIndex(t,l)
	       );
	  if not # set idims == 1 then error("dimension mismatch for index "|toString(i));
	  );
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  dimTensorAtIndex(t,l));
     outputDimensions:=outputIndices/indexRange;   
     summationDimensions:=summationIndices/indexRange;
     summationList:=toList((#summationIndices:0)..toSequence(summationDimensions/(i->i-1)));
     exprn:=product for i in 0..<#tensors list (tensors#i)_(indicesByTensor#i);
     --need to sum over summation indices:
     tensorFunction:=s->(
	  exprn's:=(expressionFunction(exprn,outputIndices)) s;
	  sum apply(summationList,expressionFunction(exprn's,summationIndices))
	  );
     tensorArray(outputDimensions,tensorFunction)
     )
tensorArrayComposition (List,List) := (L,summationIndices) -> (
     tensorArrayComposition(L/first,L/(i->toSequence remove(i,0)),summationIndices)
     )

--Einstein summation
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

{* Deprecated:
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
*}

----------------
--Tensor Modules
----------------
Tensor=new Type of Vector
Tensor.cache = new CacheTable

TensorModule = new Type of Module
module TensorModule := M -> new Module from M

--Printing TensorModules:
TensorModule.synonym="tensor module"
net TensorModule := M -> (net new Module from M)|
     ", "|
     "tensor order "|toString(#M.cache.dimensions)|
     ", dimensions "|toString(M.cache.dimensions)
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

-------------------------------------
--Method for building tensor modules:
-------------------------------------

--Copy an ImmutableHashTable with a CacheTable:
cacheCopy = method()
cacheCopy Thing := M -> hashTable ((pairs M)|{symbol cache => new CacheTable from M.cache})

--Copy a module into a TensorModule
--without the new cache table entries:
tm'=method()
tm' Module := M -> new TensorModule of Tensor from cacheCopy M;

--Build tensor modules:
tm=tensorModule = method()
tm Module := M -> (
     Q:=tm' M;
     Q.cache.dimensions = {numgens M};
     Q
     )
tm (Ring,List) := (R,L) -> (
     d:=product L;
--     Q:=newClass(TensorModule,Tensor, (R^d));
     Q:=tm'(R^d);
     Q.cache.dimensions = L;
     Q
     )
tm (Module,List) := (M,L) -> (
     d:=product L;
     if not numgens M == d then error "dimension mismatch";
     Q:=tm' M;
     Q.cache.dimensions = L;
     Q
     )
tm Vector := v -> class v;

------
--Using dimensions method previously defined for
--TensorArrays now for...
dimensions TensorModule := M -> M.cache.dimensions
dimensions Tensor := v -> (
     dimensions class v
     )

----------------------------
--Equality of tensor modules
----------------------------
TensorModule == TensorModule := (M,N) -> (
     module N == module N
     and M.cache.dimensions == N.cache.dimensions)
--note this is stornger than "===", which
--ignores the cache!

----------------------------
--TensorModule combinations
----------------------------
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


----------------------------------------------
--Conversions between Tensors and TensorArrays
----------------------------------------------
------
tensor' = method()
tensor' (List,TensorModule) := (L,M) -> (
     a:=tensorArray L;
     if not dimensions a == dimensions M then error "tensor' (List,TensorModule): dimension mismatch";
     t:=new M from vector ultimate(flatten,L);
     TensorArray.cache#t = a;
     Tensor.cache#a = t;
     t
     )
--cache not working
tensor' TensorArray := a -> (
     if Tensor.cache#?a then return Tensor.cache#a;     
     dims:=dimensions a;
     f:=ultimate(flatten,a);
     R:=commonRing f;
     M:=tensorModule(R,dims);
     t:=new M from vector f;
     TensorArray.cache#t = a;
     Tensor.cache#a = t;
     t     
     )

tensor' List := L -> tensor' tensorArray L;


------

------
isTensor=method()
isTensor Thing := x -> instance(class x,TensorModule)
------
tensorArray Tensor := t -> (
     if TensorArray.cache#?t then return TensorArray.cache#t;
     a := new TensorArray from rnl (dimensions t,entries t);
     TensorArray.cache#t = a;
--     Tensor.cache#a = t; the array does not retain the base ring!
     a
     )
net Tensor := t -> net tensorArray t;
------

------
vector Tensor := t -> new (module t) from t
Tensor+Tensor := (v,w) -> (
     if not tm v == tm w then error "Tensor+Tensor not from the same TensorModule";
     new (tm v) from (vector v)+(vector w)
     )
Tensor-Tensor := (v,w) -> (
     if not tm v == tm w then error "Tensor-Tensor not from the same TensorModule";
     new (tm v) from (vector v)-(vector w)
     )
RingElement*Tensor := (r,w) -> (
     if not ring r == ring w then error "RingElement*Tensor not over the same ring";
     new (tm w) from r*(vector w)
     )
Tensor*RingElement := (w,r) -> r*w
Tensor**Tensor := (v,w) -> (
     M:=(tm v)**(tm w);
     new M from (vector v)**(vector w)
     )

     
Tensor _ Sequence := (v,L) -> (
     M := tensorModule v;
     dims := M.cache.dimensions;
     if not #L == #dims then error "dimension mismatch";
     ind := L#0;
     for i from 0 to #L-2 do ind = ind*dims#i + L#(i+1);
     v_ind
     )


Tensor ^ ZZ := (t,n) -> fold(for i in 0..<n list t,(i,j)->i**j)

--
beginDocumentation()

TEST ///
///

TEST  ///
///

end


restart
debug loadPackage"Tensors"

--comparison with matrix multiplication:
n=20
me=for i in 1..n list for j in 1..n list i^2+j^2;
m=matrix me;
t=ta me;
--3.6 secs with ds, n=9
--0.09 secs with dsub, n=9
time tt=tac({{t,i,j},{t,j,k}},{j});
--0.000043 secs:
time (m*m);


A
B
C'

printWidth=1000


A
B
C

x=tac({{A,i,j},{B,i,k},{C,i,l}},{})
toList x


x=sum entries tac({{A,i,0},{B,i,1},{C,i,1}},{})

x_(0,1,1)

es({{A,i,j},{B,i,k},{C,i,l}})
tac({{A,i,j},{B,i,k},{C,i,l}})

IndexedTensorArray

A_(0,1)
A(row=1,col=0)


R=QQ[x]

ta({2,2,2},(i,j,k)->i+j+k)


M = tensorModule(R^8,{2,2,2})
vec = vector{1,2,3,4,5,6,7,8}
v = new M from vec

v_{0,0,1}
v_(1,1,0)

tav = tensorArray v
tav_(0,0,1)


--the following works okay:
N=tm(R,{1,1})
O=tm(R,{1,1,1})
N
O
N_0
O_0
--

--this works:
M=tm(R,{1})
N=tm(R,{1,1})
M**N
M
N
--

--this does not work:
N=tm(R,{1,1})
N**N
N
--


M=tm R^2
f=map(tm R^1,M,{{1,1}})
f=map(tm R^3,M,{{1,1},{2,3},{4,5}})
t=(M_0)**(M_1)**(M_0)
g=f**f**(id_(M))
g*t

N = tm R^1
N**N**N**N

--check rectangular in tel

L={{1,2},{3,4}}
tensor'(ta tensor'({L,L,L},M++M++M),M)
t=tensor'({L,L+L,L+L+L+L},((tm R^3)**M))
tensor'(ta t,((tm R^3)**M))==t


while not all(L,i->not class i == List)

new Function from flatten



L=rectangularNestedList({2,2,2},{1,2,3,4,5,6,7,8})

L={{{1,2,3},{4,5,6}},{{5,6,7},{8,9,10}}}
--entry:
nla(L,(1,1,2))

--slices:
nla(L,(1,))
nla(L,(1,,))
nla(L,(,1,))
nla(L,(,,1))
nla(L,(,1,1))
nla(L,(1,,1))

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





