newPackage(
	"Tensors",
    	Version => "0.02", 
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

----------------------------------------
--Searchable comment legend:
--a.c. : andrew critch

   
--ToDo:eventually ditch tensor arrays 
--except for printing
--1) tensorContraction for tensors, for now
--by converting to and from arrays --for now; do faster and mostly ditch
--arrays except for printing later.
--2)fix tm R^3
--fix M++M
--3) change printing of non-free tensor modules
--4)Exclude contraction for non-free modules
--4)make a tensor DIRECTLY from a function 
--5)make a tensor DIRECTLY from a list
--6) command for dropping 1's in dimension list

--Luke wants:
--to identify deg 1 part of the 
--coordinate ring of a tensor space with the
--dual to the space, and
--wants pieces of a resolution to be R-TensorModules

export{Tensor,TensorModule,tensor',tensorModule,
     tensorDimensions,tensorComposition,
     einsteinSummation}

gs = getSymbol

--these are currently used for einstein summation,
--which needs to be rewritten
protect Stops

-----------------------
--Error methods
-----------------------
assertClasses=method()
assertClasses (List,Type) := (L,T) -> if not all(L,i->instance(i,T)) then (
     error ("expected list entries of type "|toString(T)|"s"))
assertClasses (List,Type,String) := (L,T,context) -> if not all(L,i->instance(i,T)) then (
     error (context|" expected list entries of type "|toString(T)|"s"))

--------------------------------------------
--Load part 1 (minimize dependence on this)
--------------------------------------------
--load "./tensors/tensorarrays.m2"
load "./tensors/rectangularnestedlists.m2"

----------------------------------
--Part 2 of 3:
--Tensors and Tensor Modules
--(define methods here which
--can be made self-sufficient
--later)
----------------------------------

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
if not class tensorDimensions === MethodFunction then (
     tensorDimensions = method())
tensorDimensions Module := M -> {numgens M}
tensorDimensions TensorModule := M -> M#(gs"dimensions")

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
--Building tensor modules:
-------------------------------------
tm=tensorModule = method()

--make a free module into a tensor module:
tm (Ring,List) := (R,dims) -> (
     d:=product dims;
     new TensorModule of Tensor from (
	  new HashTable from (pairs R^d)|{
      	       gs"factors" =>  apply(dims,i->R^i),
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

--perhaps this should instead be
--t-> (classes := ancestors class t;
--     return classes#(position(classes,i->class i===TensorModule))
--     )
tmf=--[INTERNAL]
tensorModuleFactors=method()
tmf TensorModule := T -> T#(gs"factors")
tmf Module := M -> {M}

tensorDimensions Tensor := t -> tensorDimensions tm t
--Tensor module from a list of modules to tensor product,
--which themselves may be tensor modules
tm List := (fctrs) -> (
     assertClasses(fctrs,Module,"tensorModule(List)");
     dims:=flatten(fctrs/tensorDimensions);
     f:=flatten(fctrs/tmf);
     M:=fold(fctrs/module,(i,j)->i**j);
      new TensorModule of Tensor from (
	   new HashTable from (pairs M)|{
	   	gs"factors" => f,
       	   	gs"dimensions" => dims,
	        symbol module => M})
     )

----------------------------
--TensorModule combinations
----------------------------
TensorModule^ZZ := (M,n) -> tm toList (n:M)

--a.c. bug for ++ below
TensorModule++TensorModule := (M,N) -> (
     if not #M#(gs"dimensions") == #N#(gs"dimensions") then error "dimension mismatch in TensorModule++TensorModule";
     P:=(module M)++(module N);
     tm(P,M#(gs"dimensions") + N#(gs"dimensions"))
     )

TensorModule**TensorModule := (M,N) -> tm{M,N}


-----------------------------
--Basic tensor methods
-----------------------------
--Get the ambient tensor module of a tensor:
tensorModule Tensor := t -> class t;

--Get the ambient module of a tensor
module Tensor := t -> module class t;

--Convert a tensor back into a vector
vector Tensor := t -> new (module t) from t

--Extract an entry of a tensor
--by a multi-index
Tensor _ Sequence := (v,L) -> (
     M := tensorModule v;
     dims := M#(gs"dimensions");
     if not #L == #dims then error "dimension mismatch";
     ind := L#0;
     for i from 0 to #L-2 do ind = ind*dims#i + L#(i+1);
     v_ind
     )


------------------------------------------
--Making tensors without RNLs (previously TensorArrays)
------------------------------------------
tensor' = method()
tensor'(TensorModule,List):=(M,ents)-> new M from vector ents
tensor'(List,List):=(dims,ents)->(
     R:=commonRing ents;
     M:=tensorModule(R,dims);
     tensor'(M,ents)
     )
Ring**Tensor := (r,t) -> error "not implemented yet"

----------------------------------------------
--Conversions between Tensors and TensorArrays
----------------------------------------------
------MINIMIZE DEPENDENCE ON TENSOR ARRAYS
----------------------------------------------
T=tensor' List := L -> (
     dims:=rnlDimensions rnl L;--check rectangularity and get dimensions
     ents:=ultimate(flatten,L);
     tensor'(dims,ents)
     )



------
tensorArray Tensor := t -> (
     if TensorArray.cache#?t then return TensorArray.cache#t;
     a := new TensorArray from rnl (tensorDimensions t,entries t);
     TensorArray.cache#t = a;
--     Tensor.cache#a = t; the array does not retain the base ring!
     a
     )
net Tensor := t -> net tensorArray t;
------

---------------------------
--Tensor combinations
---------------------------
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
Tensor ^ ZZ := (t,n) -> fold(for i in 0..<n list t,(i,j)->i**j)

-------------------------
--Tensor Compositions
-------------------------
--REWRITE THESE FROM SCRATCH!!

tcomp=
tensorComposition=method()
tcomp (List,List,List) := 
  (tensors,indicesByTensor,summationIndices) -> 
  tensor' rnlComposition(tensors/rnl,indicesByTensor,summationIndices)

tcomp (List,List) := (L,summationIndices) -> (
    tensorComposition(L/first,L/(i->toSequence remove(i,0)),summationIndices)
     )

tcomp (List) := L -> tcomp(L,{})

esum=
einsteinSummation=method()
esum (List,List) := 
  (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     indicesByTensor=indicesByTensor/toSequence;
     allIndices:=toList set splice indicesByTensor;
     ZZindices:=(select(allIndices,i->class i === ZZ));
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k===i));
     repeatedIndices:=select(allIndices,i->1<#flatten indexLocations i);
     summationIndices:=repeatedIndices-set(ZZindices);
     tcomp(tensors,indicesByTensor,summationIndices)
     )

esum(List) := (L) ->
     esum(L/first,L/(i->toSequence remove(i,0)))

TEST ///
R=QQ[x 1]
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


--a.c. SORT THIS UPWARD:
tensor'(List,Function):=(L,f) -> tensor' rnl(L,f)
TensorModule _ Sequence := (M,s) -> (
     if not #tensorDimensions M == #s then error "dimension mismatch";
     f:=method(Dispatch=>Thing);
     f Sequence := i -> if i==s then 1 else 0;
     new M from tensor'(tensorDimensions M,f)
     )
Tensor/Function := (t,f) -> new class t from tensor' ((entries t)/f)
diff(Tensor,RingElement) := (t,r) -> t/(i->diff(i,r))


---------------------
--Load part 3
---------------------
load "./tensors/indexedtensors.m2"

--

TEST  ///
T=tm(R,{3,3});
T.factors
t=T_0
T**T
module t
vector t
t+t
t**t
t+t
a=ta t
tac({{a,i,j},{a,i,k},{a,i,l}},{i})
T=tm(t**t**t)
T.factors

///

load "./tensors/tensors-documentation.m2"
end

restart
debug loadPackage"Tensors"

restart
debug loadPackage("Tensors",DebuggingMode=>true)

restart
uninstallPackage"Tensors"
installPackage"Tensors"
viewHelp"TensorModule"