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
net IndexedTensor := A -> net (hold A.cache#(gs"name"))_(subscriptFormat A#(gs"indices"))
noname="[unnamed IndexedTensor]"
it=
indexedTensor=method()
it (Tensor,List) := (t,inds) -> (
     c:=new CacheTable from {(gs"name") => noname};
     new IndexedTensor from hashTable{
     	  gs"tensor" => t,
     	  gs"indices" => inds,
     	  cache => c,     
     	  gs"name" => () -> c#(gs"name")}
     )
IndexedTensor.GlobalAssignHook = (sym,val) -> (
     if val.cache#(gs"name") === noname then val.cache#(gs"name") = sym;
     )
IndexedTensor#{Standard,AfterPrint} = T -> (
     << endl;				  -- double space
     t:= T#(gs"tensor");
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << ring t
     << "-IndexedTensor of order "|toString(#tensorDimensions t)|
     ", dimensions "|toString(tensorDimensions t);
     << endl;
     )


end


restart
debug loadPackage"Tensors"

restart
debug loadPackage("Tensors",DebuggingMode=>true)

restart
uninstallPackage"Tensors"
installPackage"Tensors"
viewHelp"Tensors"