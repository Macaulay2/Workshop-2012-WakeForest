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
--fix "new M from ..." somehow
--flattenings (after learning to make module elements)
--2)fix tm R^3
--fix M++M
--4)Exclude contraction for non-free modules
--6) command for dropping 1's in dimension list


--Luke wants:
--to identify deg 1 part of the 
--coordinate ring of a tensor space with the
--dual to the space, and
--wants pieces of a resolution to be R-TensorModules

export{Tensor,TensorModule,FreeTensorModule,
     makeTensor,tensorModule,
     tensorDimensions,tensorComposition,
     einsteinSummation}

gs = getSymbol

cs=coreSymbol = method()     
cs String := nam -> (
     getGlobalSymbol(Core#"private dictionary",nam))
cs"RawRing"

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

inserts=method()
inserts(VisibleList,VisibleList,VisibleList):=(locs,things,host)->(
     if not #locs===#things then error "#locations =!= #things to insert";
     for i in 0..<#locs do host=insert(locs#i,things#i,host);
     host
     )

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
--RNLs now for...
if not class tensorDimensions === MethodFunction then (
     tensorDimensions = method())
tensorDimensions Module := M -> {numgens M}
tensorDimensions TensorModule := M -> M#(gs"dimensions")

--Printing TensorModules:
moduleSummary=M->(
     n := rank ambient M;
     if M.?generators then
     if M.?relations then << ", subquotient of " << ambient M
     else << ", submodule of " << ambient M
     else if M.?relations then << ", quotient of " << ambient M
     else if n > 0 then (
	  if not all(degrees M, d -> all(d, zero)) 
	  then << ", degrees " << if degreeLength M === 1 then flatten degrees M else degrees M;
	  );
     )



TensorModule.synonym="tensor module"
net TensorModule := M -> fold(apply(M#(gs"factors"),net@@module),(i,j)->i|" ** "|j)
TensorModule#{Standard,AfterPrint} = M -> (
     << endl;				  -- double space
     n := rank ambient M;
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << ring M
     << "-TensorModule of order "|toString(#M#(gs"dimensions"))|
     ", dimensions "|toString(M#(gs"dimensions"));
     moduleSummary M;
     << endl;
     )

-------------------------------------
--Free Tensor Modules
-------------------------------------
FreeTensorModule = new Type of TensorModule
net FreeTensorModule := M -> (net module M)|
     "{"|(fold(M#(gs"dimensions")/toString,(i,j)->i|"x"|j))|"}";
FreeTensorModule#{Standard,AfterPrint} = M -> (
     << endl;				  -- double space
     n := numgens M;
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "Free "
     << ring M
     << "-TensorModule of order "|toString(#M#(gs"dimensions"))|
     ", dimensions "|toString(M#(gs"dimensions"));
     moduleSummary M;
     << endl;
     )

-------------------------------------
--Building tensor modules:
-------------------------------------
tm=tensorModule = method()

--make a free module into a tensor module:
tm (Ring,List) := (R,dims) -> (
     d:=product dims;
     new FreeTensorModule of Tensor from (
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
     T:=if isFreeModule M then FreeTensorModule else TensorModule;
      new T of Tensor from (
       	   new HashTable from (pairs M)|{
		gs"factors" =>  {M},
       	   	gs"dimensions" =>  {numgens M},
	        symbol module => M}
	   )
     )
tm TensorModule := identity

--this is conceptually weird if M is not free and #L>1
tm (Module,List) := (M,dims) -> (
     d:=product dims;
     if not numgens M == d then error "dimension mismatch";
     if not isFreeModule M then error "expected a free module";
     new FreeTensorModule of Tensor from (
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
     T:=if all(fctrs,isFreeModule) then FreeTensorModule else TensorModule;
      new T of Tensor from (
	   new HashTable from (pairs M)|{
	   	gs"factors" => f,
       	   	gs"dimensions" => dims,
	        symbol module => M})
     )

----------------------------
--Comparing tensor modules
----------------------------
TensorModule == TensorModule := (M,N) -> (M#(gs"factors") / module)==(N#(gs"factors") / module)

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

--fast access without error checking
tensorAccess = method()
tensorAccess (Tensor,Sequence) := (t,s) -> (
     dims := tensorDimensions t;
     if not #s == #dims then error "dimension mismatch";
     if not all(0..<#s,i->s#i<dims#i) then error "index out of range";
     ind := s#0;
     for i in 1..<#s do ind = ind*(dims#i) + s#i;
     t_ind
     )

Tensor _ Sequence := tensorAccess

fta=
fastTensorAccess = method()
fta (Tensor,Sequence) := (t,s) -> (
     dims := tensorDimensions t;
     ind := s#0;
     for i in 1..<#s do ind = ind*(dims#i) + s#i;
     t_ind
     )


------------------------------------------
--Making tensors without RNLs (previously TensorArrays)
------------------------------------------
tensor(TensorModule,Vector):=opts->(M,v)-> new M from v
tensor(TensorModule,List):=opts->(M,l) -> (
     new M from map(M,(ring M)^1,for i in l list {i}))
--
makeTensor=method()
--a.c. fix "new M from" here...
makeTensor (List,List):=(dims,ents)->(
     R:=commonRing ents;
     M:=tensorModule(R,dims);
     tensor(M,ents)
     )
makeTensor (List,Function):=(dims,f)->(
     inds:=acp apply(dims,i->0..<i);
     ents:=toList apply(inds,f);
     makeTensor(dims,ents))

Ring**Tensor := (r,t) -> error "not implemented yet"

Tensor/Function := (t,f) -> tensor(class t,apply(entries t,f))


----------------------------
--Access to basis elements
--by multi-index
----------------------------
TensorModule _ Sequence := (M,s) -> (
     dims := M#(gs"dimensions");
     if not #s == #dims then error "dimension mismatch";
     if not all(0..<#s,i->s#i<dims#i) then error "index out of range";
     ind := s#0;
     for i in 1..<#s do ind = ind*(dims#i) + s#i;
     M_ind
     )

----------------------------------------------
--Conversions between Tensors
--and RectangularRestedLists
----------------------------------------------
------MINIMIZE DEPENDENCE ON TENSOR ARRAYS
----------------------------------------------
makeTensor List := L -> (
     dims:=rnlDimensions rnl L;--check rectangularity and get dimensions
     ents:=ultimate(flatten,L);
     makeTensor(dims,ents)
     )

------
rnl Tensor := t -> (
     if RNL.cache#?t then return RNL.cache#t;
     a := new RNL from rnl (tensorDimensions t,entries t);
     RNL.cache#t = a;
--     Tensor.cache#a = t; the array does not retain the base ring!
     a
     )
net Tensor := t -> net rnl t;
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

--------------------------------------
--Turn a free tensor into a function that
--accesses its entries
--------------------------------------
assertFreeTensor=method()
assertFreeTensor Tensor := t -> if not isFreeModule tensorModule t then error "expected a tensor in a free tensor module"

tensorFunction = method()
tensorFunction Tensor := t -> (
     f:=method(Dispatch=>Thing);
     f Sequence := s -> t_s;
     f
     )

----------------------------------
--Turn a BasicList into a function
--which plugs things into null
--or symbolic entries
----------------------------------
isSymbolic = x -> instance(x,Symbol) or instance(x,IndexedVariable)

naf=nullArgumentFunction = method(Dispatch=>Thing)
naf BasicList := l -> (
     nulls:=positions(l,i->i===null);
     n:=#nulls;
     toPositions:=hashTable toList apply(0..<n,i->nulls_i=>i);
     f:=method(Dispatch=>Thing);
     f Sequence := s -> if not #s===n then error("expected "|toString n|" arguments") else
          apply(0..<#l,i->if 
	  not l#i===null then l#i else
	  s#(toPositions#i));
     f Thing := x -> f (1:x);
     f
     )
nasf=
nullArgumentSequenceFunction=x->toSequence@@(naf x)

saf=symbolicArgumentFunction = method(Dispatch=>Thing)
saf BasicList := l -> (
     uniqueSymbols:=unique sort toList select(l,isSymbolic);
     n:=#uniqueSymbols;
     toPositions:=hashTable toList apply(0..<n,i->uniqueSymbols_i=>i);
     f:=method(Dispatch=>Thing);
     f Sequence := s -> if not #s===n then error("expected "|toString n|" arguments") else
	  apply(l,i->if 
	  not isSymbolic i then i else
	  s#(toPositions#i));
     f Thing := x -> f (1:x);
     f
     )
sasf=
symbolicArgumentSequenceFunction=x->toSequence@@(saf x)

---------------------
--Tensor slices
---------------------
--use inserts function here!
Tensor_List := (t,l) -> (
     l':=toSequence select(l,i->not i===null);
     if #l'==#l then return t_(toSequence l);
     assertFreeTensor t;
     dims:=tensorDimensions t;
     blanks:=positions(l,i->i===null);
     odims:=dims_blanks;
     M:=class t;
     M':=tensorModule((M#(gs"factors"))_blanks);
     inds:=toList \ acp apply(odims,i->0..<i);
     ents:=toList apply(inds,i->t_(inserts(blanks,i,l')));
     tensor(M',ents)
     )
--------
TEST///


///

-------------------
--Tensor marginals
--------------------

-------------------------
--Tensor Compositions
-------------------------
--REWRITE THESE FROM SCRATCH!!

tman=
tensorComposition=method()
tman (List,List,List) := 
  (tensors,indicesByTensor,summationIndices) -> 
  makeTensor rnlComposition(tensors/rnl,indicesByTensor,summationIndices)

tman (List,List) := (L,summationIndices) -> (
    tensorComposition(L/first,L/(i->toSequence remove(i,0)),summationIndices)
     )

tman (List) := L -> tman(L,{})

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
     tman(tensors,indicesByTensor,summationIndices)
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
assert(not M===N)
h=new MutableHashTable
h#M=1
h#N==1--unfortunately
///


--a.c. SORT THIS UPWARD:
diff(Tensor,RingElement) := (t,r) -> t/(i->diff(i,r))




---------------------
--Load part 3
---------------------
load "./tensors/gentensors.m2"

load "./tensors/indexedtensors.m2"

--

TEST  ///


///

load "./tensors/tensors-documentation.m2"

end


--wait to learn to make module elements
--from here
makeTensor Matrix := m -> (
     M:=(tm target m)**(tm dual source m);
          
     )

restart
debug loadPackage"Tensors"

restart
debug loadPackage("Tensors",DebuggingMode=>true)

