if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "Posets";
    )

newPackage select((
    "DiscreteMorse",
        Version => ".1", 
        Date => "6. August 2012",
        Authors => {
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"}
        },
        Headline => "Package for handling discrete Morse functions on simplicial complexes",
        Configuration => {"DefaultPDFViewer" => "open", "DefaultPrecompute" => true, "DefaultSuppressLabels" => true},
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs", "Posets"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "Posets";
    )

-- Load configurations
posets'PDFViewer = if instance((options Posets).Configuration#"DefaultPDFViewer", String) then (options Posets).Configuration#"DefaultPDFViewer" else "open";
posets'Precompute = if instance((options Posets).Configuration#"DefaultPrecompute", Boolean) then (options Posets).Configuration#"DefaultPrecompute" else true;
posets'SuppressLabels = if instance((options Posets).Configuration#"DefaultSuppressLabels", Boolean) then (options Posets).Configuration#"DefaultSuppressLabels" else true;

export {
     -- types and constructors
     MorseMatching 
     
     -- checking properties
     isMatching,
     isAcyclic,
     isMorseMatching,
     
     
     --operations on inclusion poset
     reverseEdges,
     
     --operation to display Matchings
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

isMorseMatching = method()
isMorseMatching(List,Digraph):=(M,G)-> (
     isMatching(M,G) and isAcyclic(reverseEdges(M,G))
);

isMorseMatching(List,Poset):=(M,P)-> (
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