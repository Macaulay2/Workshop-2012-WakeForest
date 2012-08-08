elemsize = (k,Li) -> for m in Li do (if member(k,m) then return #m)

dims = (L) -> (
     K := flatten L#0;  -- keys of the hash table
     P := for k in K list ( 
	    k => for Li in L list elemsize(k,Li)
	  );
     new HashTable from P
     )

prods = T -> (
     K := keys T;
     P := for k in K list (
	  k => f T#k
	  );
     new HashTable from P
     )

varProdPairs = H -> (
     apply(keys H, i -> apply(H#i, j -> {x_(toSequence j), product apply(#j, k ->
     (vars k)_(i, j#k))})))

matrixFun = T -> (
     n := #(T#1);
     bigList = for j in keys T list (
	  for k to n-1 list (
	       for i to T#j#k-1 list (vars k)_(j,i)));
--     R := QQ[flatten flatten bigList];
--     bigList = apply(bigList, j -> applyTable(j, i -> value i))
 )


--listSize = L -> (
 --    if #L === 1 then return (#L_0)
  --   else (
--	  p = (#L_0)*listSize(drop(L, 1))
--	  ))

f = (L) -> (
     if #L === 0 then return {{}};
     a := L#0;
     L = drop(L,1);
     flatten for i from 0 to a-1 list (
	  M := f L;
	  M/(m -> prepend(i,m))
	  )
     )


makeDets  = (str,mu) -> (
     -- mu is a list of a filled tableau
     Ind :=  apply(mu, m -> apply(#m, i-> apply(#m,j -> (m_i, j))) );
     R := QQ[(flatten flatten Ind)/(v -> str_v)];
     Ma := apply(Ind, k ->  applyTable(k, j -> value str_j));
     product apply(Ma, ma ->( det matrix ma ))
     )

makeUnsymmetric = L -> (
     Dets := apply(#L, i x -> makeDets(vars i, L_i));
     rings := apply(Dets, i -> ring i);
     uberring := QQ[flatten apply(rings, r->gens r)];
     maps :=apply(rings, r -> map(uberring,r));
     --product apply(#Dets, i -> maps_i(Dets_i));
--     T := dims L;
--     H := prods T;
--     apply(keys H, i -> apply(H#i, j -> {x_(toSequence j), product apply(#j, k ->
--     			 (vars k)_(i, j#k))}))
     )

end

matList = apply(bigList, l -> l/(v -> matrix{v}));
     m = 1;
     endList = {};
     for L in matList do(
	  for i in L do m = m**i;
	  endList = append(endList, m);    
	  m = 1;
	  );
     endList

for k to #(o10_2)-1 list for j to #(o10_1)-1 list for i to #(o10_0)-1 list
{(o10_0_i)*(o10_1_j)*(o10_2_k), u_(i,j,k)}
u

restart
load "amelia.m2"
L1 = {{1,2,3},{4,5},{6}}
L2 = {{1,2},{3,5},{4,6}}
L3 = {{1},{2},{3},{5},{6,4}}
L = {L1,L2,L3}
T = dims L
U = makeUnsymmetric {L1};
R = ring U;
matrixFun T
listSize L
helper(T#1)


end

restart
load "amelia-list.m2"
 L = {2,3,1}

f {}
f{3}
f{3,2}
f L
