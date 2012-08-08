newPackage(
     "TableauToPolynomial",
     Version => "0.1",
     Date => "August 8, 2012",
     Authors => {{Name => "Luke Oeding",
	       Email => "oeding@math.berkeley.edu",
	       HomePage => "http://www.math.berkeley.edu/~oeding/"}},
     Headline => "Compute the polynomial correspoinding to a set of
     filled tableau.",
     DebuggingMode => true
     )
needsPackage"SimpleDoc"


export {tableauToPoly}

protect a  -- needed to make intermediate rings. 

tableauToPoly = method(TypicalValue => RingElement, Options => {Variable => "w"})
tableauToPoly List := RingElement => o -> L -> (
     -- L is a nested list giving a set of filled tableau.
     -- Return in the corresponding polynomial. 
     F := makeUnsymmetric(L);
     unfactor(L, F, o.Variable)
     )

makeDets = (b,mu) -> (
     -- mu is a list giving a filled tableau and a is a symbol intended
     -- to be a new indexexed variable.  The return is a product of
     -- the determinants of matrices built from the variables
     -- according to the tableau.  
     Ind := dims {mu}; 
     --- a hash table giving the entries of the
     --- Tableau as keys and the size of the column it is in as the
     --- value as a list. 
     R := QQ(monoid[flatten apply( #(flatten mu) ,p->apply(Ind#(p+1)#0 , 
	  i->  (first b)_(last b,p+1,i) )) ]);
     Ma :=apply( mu, m->apply(m,  p->apply(Ind#(p)#0 , i-> R_((first b)_(last b,p,i)) ))); 
     --- Ma is the matrix of new vars from which we make the determinants. 
     product apply(Ma, ma -> det matrix ma)
     )

makeUnsymmetric = L ->(
     -- L is a nested list giving filled tableau.  
     -- Return in a product of the results form makeDets applied to
     -- each tableau.  
--     a := local a;
     Dets := apply(#L, i -> makeDets(a_i, L_i));
     rings := apply(Dets, i -> ring i);
     uberRing := bigRing(rings);
     --- a ring of all the rings corresponding to the determinants. 
     maps :=apply(rings, r -> map(uberRing,r)); 
     product apply(#Dets, i -> maps_i(Dets_i))
     )

unfactor = (L, F, v) -> (
     -- L is a nested list giving filled tableau corresponding to the
     -- output, F, of makeUnsymmetric.  
     -- Returns the polynomial for the tableau L.  
     Fring := ring F;
     T := prods dims L;
     H := apply(keys T, i -> apply(T#i, j -> { product apply(#j, k ->
		    	 Fring_(a_(k,i,j#k))), (getSymbol v)_(toSequence j)}));
     --- a nested list of pairs, the product of vars from the det
     --- rings with first index the same, and the new corresponding
     --- indexed variable with index corresponding to the second
     --- indices in the product.  
     Hring := QQ[toList set((flatten H)/last)];
     uberRing := Fring**Hring;
     --- Ring of all the vars from the dets and the new vars.  
     G1 := map(uberRing, Fring);  --- G1, G2 map to the big ring and
     G2 := map(uberRing, Hring); 
     H = applyTable(H, i-> {G1 i#0, G2 value i#1});
     tmp := G1 F;
     for h in H do tmp = sum for u in h list ((value u#1)*contract(u#0,tmp));
     mapList := join(apply(#gens Fring, i -> 0), gens Hring);
     G3 := map(Hring, uberRing, mapList);
     G3 tmp
     )

---- Below is a set of helper functions for building hash tables and
---- lists of indices to facilitate the previous functions.  

--- A helper function for recursively building a list of indices
--- for the tableau.  
listRecursion = (L) -> (
     -- Takes a List of integers and returns a nested list where the
     -- first entry of each list ranges from 0 to the first entry of L
     -- (minus one) and similar for the other entries and all possible
     -- combinations appear.  
     if #L === 0 then return {{}};
     a := L#0;
     L = drop(L,1);
     flatten for i from 0 to a-1 list (
	  M := listRecursion L;
	  M/(m -> prepend(i,m))
	  )
     )

bigRing = (L) -> (
     -- Takes a list of rings of arbitrary length and returns the tensor product of those rings. 
     if #L === 1 then return L_0;
     L_0**bigRing(drop(L,1))
     )

elemsize = (k,Li) -> for m in Li do (if member(k,m) then return #m)
-- takes an element k and a nested list L and returns the number of
-- elements in the list where k appears. Assumes k appears only once.  

dims = (L) -> (
     -- takes a nested list and returns a HashTable with keys the
     -- entries (atoms) of L and keys the length of the list where the
     -- atoms appear --- may appear in multiple lists so the values
     -- are lists.  
     K := flatten L#0;  -- keys of the hash table
     P := for k in K list ( 
	    k => for Li in L list elemsize(k,Li)
	  );
     new HashTable from P
     )

prods = T -> (
     -- takes a HashTable with values a list of integers and returns a
     -- HashTable with the same keys, but values a nested list.  The
     -- lists have length the length of the value in T and entries
     -- ranging from 0 to the corresponding value in the key of T, in
     -- all possible combminations for the value in T.  Uses the
     -- recursive function listRecursion. 
     K := keys T;
     P := for k in K list (
	  k => listRecursion T#k
	  );
     new HashTable from P
     )

end


restart
loadPackage"TableauToPolynomial"
debug TableauToPolynomial
mu1 = {{1,2,3},{4,5}}
mu2 = {{1,2,4},{3,5}}
mu3 = {{1,3,5},{2,4}}
L = {mu1, mu2, mu3}
tableauToPoly L
a
