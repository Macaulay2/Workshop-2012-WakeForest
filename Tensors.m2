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
--4)Exclude contraction for non-free modules
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

load "./tensors/tensorarrays.m2"

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
