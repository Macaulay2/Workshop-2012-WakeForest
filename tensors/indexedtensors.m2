----------------------------
--Part 3: Indexed Tensors
--should only depend on part 2
----------------------------
--needsPackage"Tensors"
export{IndexedTensor,indexedTensor}
IndexedTensor = new Type of HashTable
subscriptFormat :=method()
subscriptFormat List := inds -> toString(inds_0)|concatenate(
     (take(inds,{1,#inds}))/(i->","|toString(i)))
net IndexedTensor := A -> net (hold A.cache#(gs"name"))_(subscriptFormat A#(cs"indices"))
noname="[unnamed IndexedTensor]"
it=
indexedTensor=method()
it (Tensor,List) := (t,inds) -> (
     c:=new CacheTable from {(gs"name") => noname};
     new IndexedTensor from hashTable{
     	  cache => c,
       	  symbol indices => inds,
     	  symbol tensor => t}
     )

tensor IndexedTensor := opts -> t -> t.tensor
indices IndexedTensor := t -> t.indices

IndexedTensor.GlobalAssignHook = (sym,val) -> (
     if val.cache#(gs"name") === noname then val.cache#(gs"name") = sym;
     )
IndexedTensor#{Standard,AfterPrint} = T -> (
     << endl;				  -- double space
     t:= T.tensor;
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << net class t
     << "-IndexedTensor with indices "
     << net indices T
     << endl
     )

rit=
renameIndexedTensor=method()
rit (IndexedTensor,Symbol) := (t,s) -> t.cache#(gs"name") = s

---------------------------------------
--"Hadamard" products of indexed tensors
---------------------------------------
itprod=
indexedTensorProduct = method()
itprod List := its -> (
     --a.c. eliminate dependency on tman
     T:=tman apply(its,t->{t.tensor}|t.indices);
     indexedTensor(T,sort unique flatten apply(its,t->t.indices))
     )
IndexedTensor*IndexedTensor := (t,u) -> itprod{t,u}
--note that itprod is faster than * iterated by folding

end

--desired behavior:

IndexedTensor _ SequenceOfIntegers = entry
IndexedTensor _ SequenceOfIntegers = entry



restart
debug loadPackage"Tensors"

restart
debug loadPackage("Tensors",DebuggingMode=>true)

restart
uninstallPackage"Tensors"
installPackage"Tensors"
viewHelp"Tensors"