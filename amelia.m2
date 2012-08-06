elemsize = (k,Li) -> for m in Li do (if member(k,m) then return #m)

dims = (L) -> (
     K := flatten L#0;  -- keys of the hash table
     P := for k in K list ( 
	    k => for Li in L list elemsize(k,Li)
	  );
     new HashTable from P
     )

end

restart
load "amelia.m2"
L1 = {{1,2,3},{4,5},{6}}
L2 = {{1,2},{3,5},{4,6}}
L3 = {{1},{2},{3},{5},{6,4}}
L = {L1,L2,L3}
flatten L#0
dims L
netList L
