if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "FourTiTwo";
    needsPackage "Posets";
    )

newPackage select((
    "PosetsPlus",
        Version => ".1", 
        Date => "6. August 2012",
        Authors => {
            {Name => "Sonja Mapes", Email => "smapes1@nd.edu", HomePage => "http://www.nd.edu/~smapes1/"},
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"}
        },
        Headline => "Package for extra functions dealing with posets",
        Configuration => {"DefaultPDFViewer" => "open", "DefaultPrecompute" => true, "DefaultSuppressLabels" => true},
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs", "FourTiTwo", "Posets"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "FourTiTwo";
    needsPackage "Posets";
    )

needsPackage"SimpleDoc" 

-- Load configurations
posets'PDFViewer = if instance((options Posets).Configuration#"DefaultPDFViewer", String) then (options Posets).Configuration#"DefaultPDFViewer" else "open";
posets'Precompute = if instance((options Posets).Configuration#"DefaultPrecompute", Boolean) then (options Posets).Configuration#"DefaultPrecompute" else true;
posets'SuppressLabels = if instance((options Posets).Configuration#"DefaultSuppressLabels", Boolean) then (options Posets).Configuration#"DefaultSuppressLabels" else true;

export {
     -- types and constructors
     PosetMap,   
        GroundMap,
     posetMap,	 
     
     -- checking properties
     isOrderPreserving,
     isOrderReversing,
     isSimplicial,
     isJoinPreserving,
     isMeetPreserving,

     -- Crosscuts
     --joinExists, (aren't these exported by Posets?)
     --meetExists, (can't export these too without conflict)
     intersectSets,
     isBoundedBelow,
     isBoundedAbove,
     isCrosscut,
     crosscuts,
     crosscutComplex,
     
     -- fibers
     posetMapFiber,
     isFiberContractible,
     
     --finite atomic lattices
     atomSupport,
     indexedAtomSupport
    }

------------------------------------------
-- Non-exported, strongly prevalent functions
------------------------------------------
-- Brought these over from Posets so that PosetsPlus 
-- would install. Don't need to re-add to
-- Posets when we pull these methods back.
------------------------------------------

indexElement := (P,A) -> position(P.GroundSet, i -> i === A)

principalOrderIdeal' := (P, i) -> positions(flatten entries(P.RelationMatrix_i), j -> j != 0)

principalFilter' := (P, i) -> positions(first entries(P.RelationMatrix^{i}), j -> j != 0)


------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------
--installPackage ("Graphs", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Graphs.m2")
--installPackage ("Posets", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Posets.m2")


---------------------
-- PosetMaps
---------------------

-- defining a PosetMap, the inputs are source poset, target poset, and a hashtable or list depending on which instance of the method
PosetMap = new Type of HashTable

-- the input of a list is pairs (a,b) where a maps to b
posetMap= method()
posetMap(Poset, Poset, List):= PosetMap => (P1,P2,M) -> (     
	if all(M, m -> #m ===2 ) and (sort apply(M, m-> first m) == sort P1.GroundSet) 
	then
	(
		posetMap(P1,P2, hashTable apply(#M, i -> first M_i => last M_i))
	) else error "Not a map on posets."
)

posetMap(Poset, Poset, HashTable) := PosetMap => (P1, P2, H) -> (
	new PosetMap from hashTable {symbol source => P1, symbol target => P2, symbol GroundMap => H, symbol cache => new CacheTable})

map(Poset,Poset,List) := PosetMap => opts -> (P1,P2,M) -> (posetMap(P1,P2,M))


-- evaluating a posetMap at an element in the source poset
eval = method()
eval(Thing, PosetMap) := Thing => (elt, f) -> (
     if unique((f.source).GroundSet|{elt}) == (f.source).GroundSet then ((f.GroundMap)#elt) else error "element not in source"   )

Thing / PosetMap := Thing => (elt,f) -> (eval(elt,f))




-- check if a PosetMap is order preserving
isOrderPreserving = method()
isOrderPreserving(PosetMap) := Boolean => (f) -> (
     checkLessThans := unique flatten apply((f.source).GroundSet, elt1 -> apply((f.source).GroundSet, elt2 -> if compare(f.source, elt1, elt2) == true then compare(f.target, (elt1/f),(elt2/f))));
     not (unique(checkLessThans|{false}) == checkLessThans))

-- check if a PosetMap is order reversing
isOrderReversing=method()
isOrderReversing(PosetMap) := Boolean => (f) -> (
     checkLessThans := unique flatten apply((f.source).GroundSet, elt1 -> apply((f.source).GroundSet, elt2 -> if compare(f.source, elt1, elt2) == true then compare(f.target, (elt2/f),(elt1/f))));
     not (unique(checkLessThans|{false}) == checkLessThans))

-- check if a PosetMap is simplicial
isSimplicial = method()
isSimplicial(PosetMap) := Boolean => (f) -> (
     if isOrderPreserving(f)== true or  isOrderReversing(f)== true then true else false
     )

-- check if a PosetMap is join preserving
isJoinPreserving = method()
isJoinPreserving(PosetMap) := Boolean => (f) -> (
     setOfJoins := select(subsets((f.source).GroundSet,2), pair -> joinExists((f.source),pair_0, pair_1)); -- note this excludes elements with itself
     checkJoins := unique apply(setOfJoins, pair-> ((posetJoin(f.source,pair_0,pair_1) / f)  ==posetJoin(f.target, (pair_0 /f), (pair_1 /f))));
     not (unique(checkJoins|{false}) == checkJoins)
     )

-- check if a PosetMap is meet preserving
isMeetPreserving = method()
isMeetPreserving(PosetMap) := Boolean => (f) -> (
     setOfMeets := select(subsets((f.source).GroundSet,2), pair -> meetExists((f.source),pair_0, pair_1)); -- note this excludes elements with itself
     checkMeets := unique apply(setOfMeets, pair-> ((posetMeet(f.source,pair_0,pair_1) / f)  ==posetMeet(f.target, (pair_0 /f), (pair_1 /f))));
     not (unique(checkMeets|{false}) == checkMeets)
     )

-- computes the fiber (as a subposet of the source poset) of a point under a PosetMap
posetMapFiber = method()
posetMapFiber(PosetMap, Thing) := Poset => (f,elt) -> (
     elts := select((f.source).GroundSet, preim -> (f.GroundMap)#preim == elt);
     subposet (f.source, elts)
     )
-- computes the fiber of a list of elements under the poset map
posetMapFiber(PosetMap, List) := Poset => (f,L) -> (
     elts := unique flatten apply(L, elt -> select((f.source).GroundSet, preim -> (f.GroundMap)#preim == elt));
     subposet (f.source, elts)
     )

-- non exported function needed for the lower down functions
nonnull :=(L) -> (
     select(L, i-> i =!= null))


-- checks if fibers are contractible, either over an element or a list of elements
isFiberContractible = method()
isFiberContractible(PosetMap, Thing) := Boolean => (f, elt) -> (
           fiberCmpx := orderComplex(posetMapFiber(f,elt)); 
	   homDims := nonnull (unique apply(keys HH fiberCmpx, key-> if key =!= symbol ring then (prune HH fiberCmpx)#key));
      	   if #homDims == 1 and homDims_0 == 0 then true else false
	   )
      
isFiberContractible(PosetMap, List) := Boolean => (f, L) -> (
      fiberCmpx := orderComplex(posetMapFiber(f,L)); 
      homDims := nonnull (unique apply(keys HH fiberCmpx, key-> if key =!= symbol ring then (prune HH fiberCmpx)#key));
      if #homDims == 1 and homDims_0 == 0 then true else false
     )      



-----------------------
-- for Crosscut Complex
-----------------------
-- function needed to intersect a list of sets rather than just 2 sets
intersectSets = x -> set keys select(tally flatten (keys \ x), n -> n === #x)

-- adding to the method meetExists, to check that the meet of a list of elements exists
meetExists (Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
    lowerBounds := toList intersectSets(Fk);
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, i -> sum entries M_{i});
        #(select(heightLowerBounds, i -> i == max heightLowerBounds)) <= 1
        )
    )

-- adding to the method joinExists, to check that the join of a list of elements exists
joinExists (Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalFilter'(P, indexElement(P, a))));
    upperBounds := toList intersectSets(Fk);
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, i -> sum entries M_{i});
        #(select(heightUpperBounds, i -> i == max heightUpperBounds)) <= 1
        )
    )

-- checking that a set of elements in a poset is bounded above
isBoundedAbove = method()
isBoundedAbove (Poset, List) := Boolean => (P,L) -> (
     upperBounds := apply(L, a -> set(principalFilter'(P, indexElement(P, a))));
     if #intersectSets(upperBounds) > 0 or #L == 0 then true else false
     )

-- checking that a set of elements in a poset is bounded below
isBoundedBelow = method()
isBoundedBelow (Poset, List) := Boolean => (P,L) -> (
     lowerBounds := apply(L, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
     if #intersectSets(lowerBounds) > 0 or #L == 0 then true else false
     )

-- determining if a subset of a poset is a crosscut
isCrosscut = method()
isCrosscut (Poset, List) := Boolean => (P,L) -> (
          M := maximalChains P;
	  isTrue := true;
	  if not isSubset(L,P.GroundSet) then isTrue = false;
     	  for c in M do (if #(set(c) * set(L)) != 1 then isTrue = false);
     	  if isTrue then (
	       S := subsets L;
	       for s in S do (
	       	    if #s > 1 and isTrue then (
    		    	 if isBoundedBelow(P, s) then isTrue = meetExists(P,s);
		    	 if isTrue then (
    		    	      if isBoundedAbove(P, s) then isTrue = joinExists(P,s);
			      );
	       	    	 );
	       	    );
	       );
     	  isTrue
	  )
	  
-- finds all crosscuts in a poset	  
crosscuts = method()
crosscuts (Poset) := List => (P) -> (
     S := subsets P.GroundSet;
     select( S, s -> isCrosscut(P,s) )
     )

-- given a poset and a list of elements, checks that the list is a crosscut and if so retruns the crosscut complex
crosscutComplex = method(Options => { symbol VariableName => getSymbol "v", symbol CoefficientRing => QQ })
crosscutComplex (Poset, List) := SimplicialComplex => opts -> (P, L) -> (
     if not isCrosscut(P,L) then error "expected crosscut as second argument" else (
     	  boundedSubsets := select(subsets(L), s -> #s > 0 and (isBoundedAbove(P,s) or isBoundedBelow(P,s)));   
     	  s := opts.VariableName;
     	  R := (opts.CoefficientRing)(monoid [s_0..s_(#L - 1)]);
     	  H := hashTable apply(#L, k -> (L_k, k));
     	  simplicialComplex apply(boundedSubsets, boundedSet -> product apply(boundedSet, t -> R_(H#t)))
	  )
     )





--------------------------
--finite atomic lattices
--------------------------
-- non-exported, computes the list of atoms just by their index in the ground set, for the purposes of storing the support in the cache
atoms' := (P) -> unique apply(select(coveringRelations P, R -> any(minimalElements P, elt -> (elt === R#0))), rels -> indexElement(P,rels_1))

-- for a poset (needs to be changed to give an error if not an f.a.l.) computes the support in the atoms of each element in the poset
atomSupport = method()
atomSupport(Poset) := List => (P) -> (
     atomSet := set atoms'(P);
     P.cache.indexedAtomSupport = apply(#P.GroundSet, i -> toList(atomSet*(set(principalOrderIdeal'(P,i)))));
     apply(P.cache.indexedAtomSupport, elt-> apply(elt, i-> P.GroundSet_i))           
     )





-- example
--P1 = poset({a,b,c},{(a,b), (b,c)})
--P2 = poset({x,y},{(x,y)})
--M = {{a,x},{b,y},{c,y}}
--posetMap(P1,P2,M)
--f = map(P1,P2,M)





------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        PosetsPlus
    Headline
        a package for working with partially ordered sets, which is an addition to Posets
    Description
        Text
            This package adds some functionality to the existing package Posets.  Later versions will be
	    incorporated into the Posets package.
       
///

------------------------------------------
-- Data type & constructor
------------------------------------------


doc ///
     Key     
     	  isBoundedAbove
	  (isBoundedAbove, Poset, List)
     Headline
     	  checks whether a set of elements in a poset is bounded above
     Usage
     	  i = isBoundedAbove(P,L)
     Inputs
     	  P : Poset
	       a poset
	  L : List
	       a list of elements in the poset P 
     Outputs
     	  i : Boolean
     Description
    	  Text
	       This method tests whether the set L is bounded from above in the poset P
	  Example
	       P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
	       L1 = {a,b,c,d}
	       L2 = {a,b,c}
	       isBoundedAbove(P,L1)
	       isBoundedAbove(P,L2)	       
     SeeAlso
     	  isBoundedBelow
///

doc ///
     Key     
     	  isBoundedBelow
	  (isBoundedBelow, Poset, List)
     Headline
     	  checks whether a set of elements in a poset is bounded below
     Usage
     	  i = isBoundedBelow(P,L)
     Inputs
     	  P : Poset
	       a poset
	  L : List
	       a list of elements in the poset P 
     Outputs
     	  i : Boolean
     Description
    	  Text
	       This method tests whether the set L is bounded from below in the poset P
	  Example
	       P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
	       L1 = {e,f}
	       L2 = {a,b}
	       isBoundedBelow(P,L1)
	       isBoundedBelow(P,L2)	       
     SeeAlso
     	  isBoundedAbove
///


doc ///
     Key     
     	  isCrosscut
	  (isCrosscut, Poset, List)
     Headline
     	  checks whether a set of elements in a poset is a crosscut
     Usage
     	  i = isCrosscut(P,L)
     Inputs
     	  P : Poset
	       a poset
	  L : List
	       a list of elements in the poset P 
     Outputs
     	  i : Boolean
     Description
    	  Text
	       This method tests whether the set L in the poset P is a crosscut
	  Example
	       P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
	       L1 = {a,b,c}
	       L2 = {a,b,c,d}
	       isCrosscut(P,L1)
	       isCrosscut(P,L2)	       
     SeeAlso
     	  crosscuts
///

doc ///
     Key     
     	  crosscuts
	  (crosscuts, Poset)
     Headline
     	  lists all crosscuts in a poset
     Usage
     	  L = crosscuts(P)
     Inputs
     	  P : Poset
	       a poset 
     Outputs
     	  L : List
	       a list of subsets of P
     Description
          Text
	       This method returns the list of crosscuts in the poset P
	  Example
	       P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
	       crosscuts(P)	       
     SeeAlso
     	  isCrosscut
///

doc ///
     Key
          crosscutComplex
	  (crosscutComplex, Poset, List)
	  [crosscutComplex,VariableName]
	  [crosscutComplex,CoefficientRing]
     Headline
          returns the crosscut complex of a crosscut in a poset
     Usage
     	  C = crosscutComplex(P,L)
     Inputs
     	  P : Poset
	       a poset
	  L : List
	       a list of elements in the poset P giving a crosscut 
	  VariableName=>Symbol
	  CoefficientRing=>Ring
     Outputs
     	  C : SimplicialComplex
     Description
    	  Text
	       This method returns the crosscut complex of the crosscut L in the poset P
	  Example
	       P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
	       L = {a,b,c,d}
	       crosscutComplex(P,L)       
     SeeAlso
     	  isCrosscut
///












-------------------------
-- TESTS
-------------------------

TEST ///
    P = poset({(a,e), (e,g), (b,e), (b,f), (c,f), (f,g), (d,d)})
    L1 = {a,b,c}
    L2 = {a,b,c,d}
    L3 = {e,f}
    L4 = {d,e,f}
    cx = crosscutComplex(P,L2)
    R = cx.ring
    assert ( isBoundedAbove(P, L1) == true )
    assert ( isBoundedAbove(P, L2) == false )
    assert ( isBoundedBelow(P, L1) == false )
    assert ( isBoundedBelow(P, L3) == true )
    assert ( isCrosscut(P, L1) == false )
    assert ( isCrosscut(P, L2) == true )
    assert ( isCrosscut(P, L4) == true )
    assert ( sort apply(crosscuts(P), s -> sort s) == sort {{a,b,c,d}, {d,e,f}, {d,g}} )
    assert ( sort flatten entries cx.facets == sort {R_3, R_0*R_1*R_2} )
/// 


end
