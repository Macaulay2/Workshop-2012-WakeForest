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

     -- Crosscuts
     --joinExists, (aren't these exported by Posets?)
     --meetExists, (can't export these too without conflict)
     intersectSets,
     isBoundedBelow,
     isBoundedAbove,
     isCrosscut,
     crosscuts,
     
     -- fibers
     posetMapFiber,
     isFiberContractible,
     
     --Morse stuff
     reverseEdges,
     isMatching,
     texMatching,
     displayMatching,
     outputTexMatching
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


meetExists(Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
    lowerBounds := toList intersectSets(Fk);
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, i -> sum entries M_{i});
        #(select(heightLowerBounds, i -> i == max heightLowerBounds)) <= 1
        )
    )


joinExists(Poset, List) := Boolean => (P,L) -> (
    Fk := apply(L, a -> set(principalFilter'(P, indexElement(P, a))));
    upperBounds := toList intersectSets(Fk);
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, i -> sum entries M_{i});
        #(select(heightUpperBounds, i -> i == max heightUpperBounds)) <= 1
        )
    )

isBoundedAbove = method()
isBoundedAbove(Poset, List) := Boolean => (P,L) -> (
     upperBounds := apply(L, a -> set(principalFilter'(P, indexElement(P, a))));
     if #intersectSets(upperBounds) > 0 then true else false
     )

isBoundedBelow = method()
isBoundedBelow(Poset, List) := Boolean => (P,L) -> (
     lowerBounds := apply(L, a -> set(principalOrderIdeal'(P, indexElement(P, a))));
     if #intersectSets(lowerBounds) > 0 then true else false
     )

isCrosscut = method()
isCrosscut(Poset, List) := Boolean => (P,L) -> (
     M := maximalChains P;
     isTrue := true;
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
	  
	  
crosscuts = method()
crosscuts(Poset) := List => (P) -> (
     S := subsets P.GroundSet;
     select( S, s -> isCrosscut(P,s) )
     )





-- methods dealing with fibers
-- compute fibers over a point in the target
-- check contractability of fibers
posetMapFiber = method()
posetMapFiber(PosetMap, Thing) := Poset => (f,elt) -> (
     elts := select((f.source).GroundSet, preim -> (f.GroundMap)#preim == elt);
     subposet (f.source, elts)
     )

nonnull :=(L) -> (
     select(L, i-> i =!= null))



isFiberContractible = method()
isFiberContractible(PosetMap, Thing) := Boolean => (f, elt) -> (
           fiberCmpx := orderComplex(posetMapFiber(f,elt)); 
	   homDims := nonnull (unique apply(keys HH fiberCmpx, key-> if key =!= symbol ring then (prune HH fiberCmpx)#key));
      	   if #homDims == 1 and homDims_0 == 0 then true else false
	   )



-- discrete morse theory types of things

------------------------------------------------------
--Given a list of edges E and a digraph G, reverses all
--edges in E.  Order matters for e in E, and duplicate
--elements will be ignored.
------------------------------------------------------

reverseEdges = method()
reverseEdges(List,Digraph):= (E,G) -> (
     if all(E, e-> member(e,edges G)) then (
	  tempGraph:= G;
	  for e in E do (
	       tempGraph = reverseEdge(e,G);
	  );
          tempGraph
     )
     else error "Not a subset of the directed edges of G."
);

isMatching = method()
isMatching(List,Digraph):= (M,G) -> (
     if all(M,e-> member(e,edges G)) then (
	  if (unique flatten M) == (flatten M) then true else error "Not a matching on G."
     )
     else error "Not a subset of the directed edges of G."
);

isAcyclic = method()
isAcyclic(Digraph) := G -> not isCyclic(G)

isAcyclicMatching = method()
isAcyclicMatching(List,Digraph):=(M,G)-> (
     isMatching(M,G) and isAcyclic(reverseEdges(M,G))
);

isAcyclicMatching(List,Poset):=(M,P)-> (
     isMatching(M,hasseDiagram P) and isAcyclic(reverseEdges(M,hasseDiagram P))
)


displayMatching = method(Options => { symbol SuppressLabels => posets'SuppressLabels, symbol PDFViewer => posets'PDFViewer, symbol Jitter => false })
displayMatching (List,Poset) := opts -> (M,P) -> (
    if not instance(opts.PDFViewer, String) then error "The option PDFViewer must be a string.";
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    name := temporaryFileName();
    outputTexMatching(M,P, concatenate(name, ".tex"), symbol SuppressLabels => opts.SuppressLabels, symbol Jitter => opts.Jitter);
    run concatenate("pdflatex -output-directory /tmp ", name, " 1>/dev/null");
    run concatenate(opts.PDFViewer, " ", name,".pdf &");
    )

outputTexMatching = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false});
outputTexMatching(List,Poset,String) := String => opts -> (M,P,name) -> (
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    fn := openOut name;
    fn << "\\documentclass[8pt]{article}"<< endl;
    fn << "\\usepackage{tikz}" << endl;
    fn << "\\newcommand{\\text}{\\mbox}" << endl;
    fn << "\\begin{document}" << endl;
    fn << "\\pagestyle{empty}" << endl << endl;
    fn << texMatching(M,P, opts) << endl;
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

texMatching = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false})
texMatching (List,Poset) := String => opts -> (M,P) -> (
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    -- edge list to be read into TikZ
    if not P.cache.?coveringRelations then coveringRelations P;
    if not all(M, e-> member(e,P.cache.coveringRelations)) then error "Edge set not subset of relations.";
    tempEdgeList:= select(P.cache.coveringRelations, e -> not member(e,M));
    edgelist := apply(tempEdgeList, r -> concatenate(toString first r, "/", toString last r));
    revEdgeList := apply(M, r-> concatenate(toString first r, "/", toString last r));
    -- Find each level of P and set up the positioning of the vertices.
    if not P.cache.?filtration then filtration P;
    F := P.cache.filtration;
    levelsets := apply(F, v -> #v-1);
    scalew := min{1.5, 15 / (1 + max levelsets)};
    scaleh := min{2 / scalew, 15 / #levelsets};
    halflevelsets := apply(levelsets, lvl -> scalew * lvl / 2);
    spacings := apply(levelsets, lvl -> scalew * toList(0..lvl));
    -- The TeX String
    "\\begin{tikzpicture}[scale=1, vertices/.style={draw, fill=black, circle, inner sep=0pt}]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list
            {"\t\\node [vertices", if opts.SuppressLabels then "]" else (", label=right:{" | tex P.GroundSet_(F_i_j) | "}]"),
             " (",toString F_i_j,") at (-",toString halflevelsets_i,"+",
             toString ((if opts.Jitter then random(scalew*0.2) else 0) + spacings_i_j),",",toString (scaleh*i),"){};\n"}
        ) |
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [->] (\\to)--(\\from);\n") |
    concatenate("\\foreach \\to/\\from in ", toString revEdgeList, "\n\\draw [<-,dashed,red] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )



end

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