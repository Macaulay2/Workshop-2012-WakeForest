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
            {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
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
     intersectSets 
     

    }

------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------
installPackage ("Graphs", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Graphs.m2")
installPackage ("Posets", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Posets.m2")

PosetMap = new Type of HashTable

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


eval = method()
eval(Thing, PosetMap) := Thing => (elt, f) -> (
     if unique((f.source).GroundSet|{elt}) == (f.source).GroundSet then ((f.GroundMap)#elt) else error "element not in source"   )

Thing / PosetMap := Thing => (elt,f) -> (eval(elt,f))


-- methods that check properties of posetMaps
-- isOrderPreserving, reversing, and simplicial
isOrderPreserving = method()
isOrderPreserving(PosetMap) := Boolean => (f) -> (
     checkLessThans := unique flatten apply((f.source).GroundSet, elt1 -> apply((f.source).GroundSet, elt2 -> if compare(f.source, elt1, elt2) == true then compare(f.target, (elt1/f),(elt2/f))));
     not (unique(checkLessThans|{false}) == checkLessThans))

isOrderReversing=method()
isOrderReversing(PosetMap) := Boolean => (f) -> (
     checkLessThans := unique flatten apply((f.source).GroundSet, elt1 -> apply((f.source).GroundSet, elt2 -> if compare(f.source, elt1, elt2) == true then compare(f.target, (elt2/f),(elt1/f))));
     not (unique(checkLessThans|{false}) == checkLessThans))

isSimplicial = method()
isSimplicial(PosetMap) := Boolean => (f) -> (
     if isOrderPreserving(f)== true or  isOrderReversing(f)== true then true else false
     )


-- isJoinPreserving
-- isMeetPreserving

isJoinPreserving = method()
isJoinPreserving(PosetMap) := Boolean => (f) -> (
     setOfJoins := select(subsets((f.source).GroundSet,2), pair -> joinExists((f.source),pair_0, pair_1)); -- note this excludes elements with itself
     checkJoins := unique apply(setOfJoins, pair-> ((posetJoin(f.source,pair_0,pair_1) / f)  ==posetJoin(f.target, (pair_0 /f), (pair_1 /f))));
     not (unique(checkJoins|{false}) == checkJoins)
     )

isMeetPreserving = method()
isMeetPreserving(PosetMap) := Boolean => (f) -> (
     setOfMeets := select(subsets((f.source).GroundSet,2), pair -> meetExists((f.source),pair_0, pair_1)); -- note this excludes elements with itself
     checkMeets := unique apply(setOfMeets, pair-> ((posetMeet(f.source,pair_0,pair_1) / f)  ==posetMeet(f.target, (pair_0 /f), (pair_1 /f))));
     not (unique(checkMeets|{false}) == checkMeets)
     )



-- for Crosscut
intersectSets = x -> set keys select(tally flatten (keys \ x), n -> n === #x)

meetExists (Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
    lowerBounds := toList intersectSets(Fk);
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, i -> sum entries M_{i});
        #(select(heightLowerBounds, i -> i == max heightLowerBounds)) <= 1
        )
    )

joinExists (Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalFilter'(P, indexElement(P, a))));
    upperBounds := toList intersectSets(Fk);
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, i -> sum entries M_{i});
        #(select(heightUpperBounds, i -> i == max heightUpperBounds)) <= 1
        )
    )

isCrosscut = method()
isCrosscut (Poset, List) := Boolean => (P,L) -> (
     M := maximalChains P;
     isTrue := true;
     for c in M do (if #(set(c) * set(L)) != 1 then isTrue = false);
     if isTrue then (
	  S := subsets L;
	  for s in S do (
	       if #s > 1 and isTrue then (
		    Fk := apply(s, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
    		    if #intersectSets(Fk) > 0 then isTrue = meetExists(P,s);
		    if isTrue then (
			 Fk := apply(s, a -> set(principalFilter'(P, indexElement(P, a))));
    		    	 if #intersectSets(Fk) > 0 then isTrue = joinExists(P,s);
			 );
	       	    );
	       );
	  );
     isTrue
     )






-- methods dealing with fibers
-- compute fibers over a point in the target
-- check contractability of fibers




-- discrete morse theory types of things




-- example
P1 = poset({a,b,c},{(a,b), (b,c)})
P2 = poset({x,y},{(x,y)})
M = {{a,x},{b,y},{c,y}}
posetMap(P1,P2,M)
f = map(P1,P2,M)





------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        Posets
    Headline
        a package for working with partially ordered sets
    Description
        Text
            This package defines @TO "Poset"@ as a new data type and provides
            routines which use or produce posets.  A poset (partially ordered
            set) is a set together with a binary relation satisfying reflexivity,
            antisymmetry, and transitivity.
        Text
            @SUBSECTION "Contributors"@
            --
            The following people have generously contributed code to the package: 
            @HREF("http://www.math.cornell.edu/People/Grads/fisher.html","Kristine Fisher")@,
            @HREF("http://www.mathstat.dal.ca/~handrew/","Andrew Hoefel")@,
            @HREF("http://www.math.purdue.edu/~nkummini/","Manoj Kummini")@,
            @HREF("mailto:stephen.sturgeon\@uky.edu", "Stephen Sturgeon")@, and 
            @HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html", "Josephine Yu")@.
        Text
            @SUBSECTION "Other acknowledgements"@
            --
            A few methods in this package have been ported from John Stembridge's Maple 
            package implementing posets, which is available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
///

------------------------------------------
-- Data type & constructor
------------------------------------------

-- The Poset Type
doc ///
    Key
        Poset
        GroundSet
        RelationMatrix
        Relations
    Headline
        a class for partially ordered sets (posets)
    Description
        Text
            This class is a type of HashTable which represents finite posets.  It consists
            of a ground set, a list of relationships ${a,b}$ where $a \leq b$, and a matrix
            encoding these relations.
        Example
            G = {1,2,3,4};                  -- the ground set
            R = {{1,2},{1,3},{2,4},{3,4}};  -- a list of relations "generating" all relations
            P = poset(G, R)                 -- the poset with its relations matrix computed
    SeeAlso
        poset
///

-- _








-------------------------
-- TESTS
-------------------------