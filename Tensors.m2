newPackage(
	"Tensors",
    	Version => "0.01", 
    	Date => "August 5, 2012",
    	Authors => {
	     {Name => "Andrew Critch", Email => "critch@math.berkeley.edu", HomePage => "http://www.acritch.com/"},
	     {Name => "Claudiu Raicu", Email => "claudiu@math.berkeley.edu", HomePage => "http://math.berkeley.edu/~claudiu/"}
	     },
    	Headline => "tensors",
	AuxiliaryFiles => true
    	)
 --Macaulay2-1.4/share/Macaulay2/Core/matrix1.m2 
 --needs to replaced for this package to work 

--searchable tag for problems:
--a.c. problem!
   
--protect Symbol makes something a symbol
--within the scope of the package
   
--ToDo:(plan to mostly ditch tensor arrays);
--1)IndexedTensorArrays, made of tensors, 
--NOT arrays... convert to and from arrays 
--for now; do faster and mostly ditch
--arrays except for printing later.
--2)fix tm R^3
--3) change printing of non-free tensor modules
--4)make a tensor DIRECTLY from a function 
--5)make a tensor DIRECTLY from a list
--6) command for dropping 1's in dimension list

--Luke wants:
--to identify deg 1 part of the 
--coordinate ring of a tensor space with the
--dual to the space, and
--wants pieces of a resolution to be R-TensorModules


--consider eliminating TensorArrays?

export{TensorArray, tensorArray, dimensions,
     tensorArrayContraction,einsteinSummation,
     Tensor,TensorModule,
     tensor',tensorModule}

--factors = getSymbol "factors"
gs = getSymbol --causing a problem!!!!!
--do not apply to existing non-symbols, e.g. module

--these are currently used for einstein summation,
--which needs to be rewritten
protect TemporaryTensorList
protect TemporaryIndexList
protect Stops

-----------------------
--Error methods
-----------------------
assertClasses=method()
assertClasses (List,Type) := (L,T) -> if not all(L,i->instance(i,T)) then (
     error ("expected list entries of type "|toString(T)|"s"))
assertClasses (List,Type,String) := (L,T,context) -> if not all(L,i->instance(i,T)) then (
     error (context|" expected list entries of type "|toString(T)|"s"))

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
     assertClasses(args,Symbol,"expressionFunction(Expression,List)");
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
TensorArray**TensorArray := (a,b) -> error "not implemented yet"
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
vector Tensor := t -> new Vector from t

TensorModule = new Type of Module
TensorModule.cache = new CacheTable
module TensorModule := M -> M.module
module Module := identity
------
--Using dimensions method previously defined for
--TensorArrays now for...
dimensions Module := M -> numgens M
dimensions TensorModule := M -> M#(gs"dimensions")

--Printing TensorModules:
TensorModule.synonym="tensor module"
net TensorModule := M -> (net module M)|
     "{"|(fold(M#(gs"dimensions")/toString,(i,j)->i|"x"|j))|"}";
TensorModule#{Standard,AfterPrint} = M -> (
     << endl;				  -- double space
     n := rank ambient M;
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << ring M
     << "-TensorModule of order "|toString(#M#(gs"dimensions"))|
     ", dimensions "|toString(M#(gs"dimensions"));
     << endl;
     )
-------------------------------------
--Method for building tensor modules:
-------------------------------------

--Copy an ImmutableHashTable with a CacheTable:
cacheCopy = method()
cacheCopy Thing := M -> hashTable ((pairs M)|{symbol cache => new CacheTable from M.cache})
symbol module
--Build tensor modules:
tm=tensorModule = method()

--make a free module into a tensor module:
tm (Ring,List) := (R,dims) -> (
     d:=product dims;
     new TensorModule of Tensor from (
	  new HashTable from (pairs R^d)|{
      	       gs"factors" =>  {R^d},
     	       gs"dimensions" =>  dims,
	       symbol module => R^d}
     	  )
     )


--make a possibly non-free module into an order 1 tensor module, 
--for tensoring with other such modules to build higher-order
--non-free tensor modules:
tm Module := M -> (
      new TensorModule of Tensor from (
       	   new HashTable from (pairs M)|{
		gs"factors" =>  {M},
       	   	gs"dimensions" =>  {numgens M},
	        symbol module => M}
	   );
     )
tm TensorModule := identity

--this is conceptually weird if M is not free and #L>1
tm (Module,List) := (M,dims) -> (
     d:=product dims;
     if not numgens M == d then error "dimension mismatch";
      new TensorModule of Tensor from (
	   new HashTable from (pairs M)|{
	   	gs"factors" =>  {M},
       	   	gs"dimensions" =>  dims,
	        symbol module => M});
     )

--Get the ambient tensor module of a tensor:
tm Tensor := t -> class t;
module Tensor := t -> module class t;


--perhaps this should instead be
--t-> (classes := ancestors class t;
--     return classes#(position(classes,i->class i===TensorModule))
--     )
tmf=--[INTERNAL]
tensorModuleFactors=method()
tmf TensorModule := T -> T#(gs"factors")
tmf Module := M -> {M}

dimensions Tensor := t -> dimensions tm t
--Tensor module from a list of modules to tensor product,
--which themselves may be tensor modules
tm List := (fctrs) -> (
     assertClasses(fctrs,Module,"tensorModule(List)");
     dims:=flatten(fctrs/dimensions);
     f:=flatten(fctrs/tmf);
     M:=fold(fctrs/module,(i,j)->i**j);
      new TensorModule of Tensor from (
	   new HashTable from (pairs M)|{
	   	gs"factors" => f,
       	   	gs"dimensions" => dims,
	        symbol module => M})
     )

----------------------------
--Old: Equality of tensor modules
----------------------------
--TensorModule == TensorModule := (M,N) -> (
--     module N == module N
--     and M.cache#(gs"dimensions") == N.cache#(gs"dimensions"))
--note this is stornger than "===", which
--ignores the cache!

----------------------------
--TensorModule combinations
----------------------------
TensorModule^ZZ := (M,n) -> tm toList (n:M)

TensorModule++TensorModule := (M,N) -> (
     if not #M#(gs"dimensions") == #N#(gs"dimensions") then error "dimension mismatch in TensorModule++TensorModule";
     P:=(module M)++(module N);
     tm(P,M#(gs"dimensions") + N#(gs"dimensions"))
     )

TensorModule**TensorModule := (M,N) -> tm{M,N}

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
tensorArray Tensor := t -> (
     if TensorArray.cache#?t then return TensorArray.cache#t;
     a := new TensorArray from rnl (dimensions t,entries t);
     TensorArray.cache#t = a;
--     Tensor.cache#a = t; the array does not retain the base ring!
     a
     )
net Tensor := t -> net tensorArray t;
------

------FIXED:
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
     dims := M#(gs"dimensions");
     if not #L == #dims then error "dimension mismatch";
     ind := L#0;
     for i from 0 to #L-2 do ind = ind*dims#i + L#(i+1);
     v_ind
     )


Tensor ^ ZZ := (t,n) -> fold(for i in 0..<n list t,(i,j)->i**j)


TEST ///
R=QQ[x]
M=tm(R,{2,2})
N=tm(R,{4})
assert(M==R^4)--they are equal as modules
assert(not M===R^4)
assert(not M==N)
M===N--unfortunately; can't change this.
h=new MutableHashTable
h#M=1
h#N==1--unfortunately
///
M=
--
beginDocumentation()
{*     doc ///
        Key
	  TensorArray
        Headline
	  The class of all tensor arrays
        Usage
        Inputs
        Outputs
        Consequences
         Item
        Description
         Text
         Code
         Pre
         Example
        Subnodes
        Caveat
        SeeAlso
     ///
*}

doc ///
Key
  TensorArray
  (symbol _,TensorArray,ZZ)
Headline
  The class of all tensor arrays
Description
  Text
   Tensor arrays are cool
   
  Example
   2*3
    
///


doc///
Key
  (symbol **,TensorArray,TensorArray)
Headline
  tensor product of arrays
Caveat
  not yet implemented
///

TEST  ///
assert(1 === 1)
///
end

restart
uninstallPackage"Tensors"
installPackage"Tensors"
viewHelp"Tensors"
