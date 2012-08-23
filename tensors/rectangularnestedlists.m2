-----------------------------------------------
--PART 1 of 3:
--Methods for nested lists...
--MINIMIZE dependence on this 
--section in future versions
------------------------------------------------
--Currently being used for einsteinsummation:
protect TemporaryTensorList
protect TemporaryIndexList

exportMutable{Stops}

{*The following cartesian product lists have sequences
as their entries, rather than lists.  this is intentional, 
both for consistency with Set**Set, and for planned later 
use of nested lists of sequences of indices.
*}

List**List := (L,M) -> flatten for l in L list for m in M list (l,m)
Sequence**Sequence := (L,M) -> join apply(L,l->apply(M,m->(l,m)))

acp=--INTERNAL ABBREVIATION
associativeCartesianProduct = method(Dispatch=>Thing)
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


----------------------------
--Rectangular Nested Lists
----------------------------
TensorArray=--deprecated
RNL=--internal
RectangularNestedList  = new Type of List
RNL**RNL := (a,b) -> (
     error "not implemented; probably shouldn't be")
RNL+RNL := (a,b) -> (
     error "not implemented; probably shouldn't be")
RNL-RNL := (a,b) -> (
     error "not implemented; probably shouldn't be")

net RNL  := T -> netList toList T
RNL.cache = new CacheTable
RNL_ZZ := (N,n) -> N_(1:n)
-----


ta=
tensorArray=--deprecated
rnl=--INTERNAL ABBREVIATION
rectangularNestedList = method()

--Function to make a rectangular nested list
--from a nested list
rnl List := L -> (
     if not isrect(L) then return "error: nested list is not rectangular";
     new RectangularNestedList from L
     )

--from a list, given dimensions
rnl(List,List):=(dims,L) -> (
     if not product dims == #L then error "rectangularNestedList: dimension mismatch";
     while #dims>1 do (
	  d:=last dims;
	  L = for i in 0..<round(#L/d) list take(L,{i*d,(i+1)*d-1});
	  dims = take(dims,{0,-2+#dims}));
     return new RNL from L)

--from a vector, given dimensions
rnl (List,Vector) := (dims,v) -> rnl(dims,entries v);

--a.c. unnecessary?
rnl Thing := x -> x


-----
rnlDimensions=method()
--This method assumes the tensor array is rectangular,
--which will be tested when the array is built
--with tensorArray()
rnlDimensions RNL := L -> (d:={};
     while instance(L,RectangularNestedList) do (d=d|{#L},L=L_0);
     return d)
---

--
--deep application of functions
deepApply =method()
deepApply(Thing,Function):=(x,f) -> f x
deepApply(List,Function):=(L,f) -> apply(L,(i->deepApply(i,f)))
RNL / Function := (t,f) -> deepApply(t,f)
Function \ RNL := (f,t) -> deepApply(t,f)

--The canonical RNL, whose entry at
--position I is I
tpl=tensorPositionList = method()
tpl List := dims -> toList((#dims:0)..toSequence(dims/(i->i-1)))

cta=canonicalTensorArray = method()
cta List := dims -> rnl(dims,(tpl dims))

--Building a TensorArray using a function which
--takes position sequences to values:
rnl (List,Function) := (dims,f) -> rnl (cta dims)/f


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

------------------------------------
--Substitution methods,
--pretty but inefficient;
--should eventually use sparingly,
--only to convert an expression input
-- into a more efficient form
------------------------------------


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


-------------------------------------------
--Tensor index substitution
--(eliminate dependence)
------------------------------------------

tis=--INTERNAL ABBREVIATION
tensorIndexSubstitution = method()
tis Thing := x -> dsub(x,Stops=>{RNL})
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

----Test expressions:
TEST ///
(0..5)/(i->value((dsub{j=>i}) (hold 2)^j))
(0..5)/(i->value((tis{j=>i}) (hold 2)^j))
f=ef((hold i)^j+k,{i,j,k})
f(4,5,6)
///
----

-------------------------------
--Composition of tensor arrays,
--inefficient AND unnecessary;
--rewrite more efficiently 
--directly for tensors
-------------------------------
-----No longer necessary:
RNL _ Sequence:=(N,s) -> (
     if not all(s,i->instance(i,ZZ) or 
	  instance(i,Symbol) or 
	  instance(i,Nothing)) then 
     error "RectangularNestedList_Sequence: expected a list of integers or symbols";
     if not all(s,i->instance(i,ZZ) or instance(i,Nothing)) then return (hold N)_(hold s);
     l:= nla(N,s);
     if instance(l,List) then return rnl l;
     l
     )

tac=
tensorArrayComposition=--soon replaced by tensorComposition
rnlcomp=
rnlComposition = method()
rnlComposition (List,List,List) := 
  (tensors,indicesByTensor,summationIndices) -> (
     if not all(summationIndices,i->instance(i,Symbol)) then error "expected summation indices to be a list of symbols";
     numberOfTensors:=#tensors;
     indicesByTensor=indicesByTensor/toSequence;
     allIndices:=toList set splice indicesByTensor;
     ZZindices:=(select(allIndices,i->class i === ZZ));
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k===i));
     outputIndices:=sort toList(((allIndices - (set summationIndices)))-(set ZZindices));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     dimTensorAtIndex:=(t,l)->(rnlDimensions(tensors_t))_l;
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
     s:=exprn;
     tensorFunction:=s->(
	  exprn's:=(expressionFunction(exprn,outputIndices)) s;
	  sum apply(summationList,expressionFunction(exprn's,summationIndices))
	  );
     rnl(outputDimensions,tensorFunction)
     )
rnlComposition (List,List) := (L,summationIndices) -> (
     tensorArrayComposition(L/first,L/(i->toSequence remove(i,0)),summationIndices)
     )

--Einstein summation
{*
einsteinSummation = method()
einsteinSummation (List,List) := (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     allIndices:=toList set splice indicesByTensor;
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k==i));
     repeatedIndices:=select(allIndices,i->1<#flatten indexLocations i);
     singleIndices:=toList((allIndices - (set repeatedIndices)));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (rnlDimensions(tensors_t))_l);
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
     return rnl value(listCommand|sumCommand|summand ((singleIndices)/(j->getSymbol("i"|toString(j))))))
einsteinSummation List := L -> einsteinSummation(L/first,L/(i->toSequence remove(i,0)))
es=einsteinSummation
*}

end

restart
debug loadPackage"Tensors"

restart
debug loadPackage("Tensors",DebuggingMode=>true)

restart
uninstallPackage"Tensors"
installPackage"Tensors"
viewHelp"Tensors"