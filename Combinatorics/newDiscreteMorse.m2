if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "Posets";
    )

newPackage select((
    "DiscreteMorse",
        Version => "0.0.1", 
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
     MorseMatching,
     morseMatching,
     
     -- checking properties
     isMatching,
     isAcyclic,
     isMorseMatching,
     
     
     --operations on inclusion poset
     reverseEdges,
     
     --components of matchings,
     "edges",
     "complex",
     "poset",
     
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

------------------------------------------------------
--METHOD:  reverseEdges
--
--INPUT:  (Edges E, digraph G)
--        (Edges E, poset P)
--
--OUTPUT:  Digraph G\E+rev(E)
--
--Given a list of edges E and a digraph G (or poset P), 
--reverses all edges in E (or in hasseDiagram P.)
--Order matters for e in E, and duplicate elements
--will be ignored.
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

reverseEdges(List,Poset):= (E,P) -> (
     G:=hasseDiagram P;
     if all(E, e-> member(e,edges G)) then (
	  tempGraph:= G;
	  for e in E do (
	       tempGraph = reverseEdge(e,G);
	  );
          tempGraph
     )
     else error "Not a subset of the directed edges of G."
);

------------------------------------------------------
--METHOD:  isMatching
--
--INPUT:  (Edges M, digraph G)
--        (Edges M, poset P)
--
--OUTPUT:  Boolean
--
--Given a list of edges M in a matching and a digraph G
--(or poset P), checks if M is a matching on G (or
--hasseDiagram P.)
------------------------------------------------------

isMatching = method()

isMatching(List,Digraph):= (M,G) -> (
     if all(M,e-> member(e,edges G)) then (
	  if (unique flatten M) == (flatten M) then true else error "Not a matching on G."
     )
     else error "Not a subset of the directed edges of G."
);

isMatching(List,Poset):= (M,P) -> (
     --Note that this method passes in the edges using the INDICES of poset elements, not the original names.
     G:=hasseDiagram P;
     if all(M,e-> member(e,edges G)) then (
	  if (unique flatten M) == (flatten M) then true else error "Not a matching on G."
     )
     else error "Not a subset of the directed edges of G."
);

------------------------------------------------------
--METHOD:  isAcyclic
--
--INPUT:  Digraph G
--
--OUTPUT:  Boolean
--
--Given a digraph G, checks acyclicity of G.
------------------------------------------------------


isAcyclic = method()
isAcyclic(Digraph) := G -> not isCyclic(G)

------------------------------------------------------
--METHOD:  isMorseMatching
--
--INPUT:  (Edges M, digraph G)
--        (Edges M, poset P)
--
--OUTPUT:  Boolean
--
--Given a list of edges M in a matching and a digraph G
--(or poset P), checks if M is a Morse matching on G
--(or on the hasseDiagram of P.)
------------------------------------------------------

isMorseMatching = method()
isMorseMatching(List,Digraph):=(M,G)-> (
     isMatching(M,G) and isAcyclic(reverseEdges(M,G))
);

isMorseMatching(List,Poset):=(M,P)-> (
     --Note that this method passes in the edges using the INDICES of poset elements, not the original names.
     isMatching(M,hasseDiagram P) and isAcyclic(reverseEdges(M,hasseDiagram P))
)

------------------------------------------------------
--TYPE:  MorseMatching
--METHOD:  morseMatching
--
--INPUT:  (Edges M, simplicialComplex D)
--        (Edges M, poset P)
--
--OUTPUT:  Edges M or error
--
--If M in edges facePoset(D) or hasseDiagram P, checks
--if M is a Morse Matching, and if so, creates an object
--of type MorseMatching.
------------------------------------------------------

MorseMatching = new Type of HashTable

morseMatching= method()

morseMatching(List,Poset):= MorseMatching => (M, P) -> (
     --Note that this method passes in the edges using the INDICES of poset elements, not the original names.
     if isMorseMatching(M,P) then (
     	  new MorseMatching from hashTable {symbol edges => M, symbol poset => P,symbol cache => new CacheTable}
     )
     else error "Not a Morse Matching on P."
)

morseMatching(List,SimplicialComplex) := MorseMatching => (M, D) -> (
     	P:=facePoset(D);
	--Note that this method passes in lists of pairs of faces of D, converts them to INDEX edges, then passes into
	--the earlier function for morseMatching(List,Poset).
	--E is a conversion of M into index elements.
      	E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
	MM:=morseMatching(E,P);
	MM.cache.complex = D;
	MM
	)





------------------------------------------------------
--METHOD:  displayMatching
--
--INPUT:  (Edges M, simplicialComplex D)
--        (Edges M, poset P)
--
--OUTPUT:  pdf image of matching
--
--This function does NOT check if something is a matching.
--It simply displays a pdf of the Hasse diagram of a 
--poset or of the face poset of a simplicial complex.
------------------------------------------------------


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

displayMatching (List,SimplicialComplex) := opts -> (M,D) -> (
    P:=facePoset(D);
    E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
    displayMatching(E,P,opts)
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

outputTexMatching(List,SimplicialComplex,String) := String => opts -> (M,D,name) -> (
    P:=facePoset(D);
    outputTexMatching(M,P,name)
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

texMatching(List,SimplicialComplex) := String => opts -> (M,D) -> (
     P:=facePoset(D);
     texMatching(M,P)
)



------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        DiscreteMorse
    Headline
        a package for working with discrete Morse matching of simplicial complexes
    Description
        Text
            This package defines @TO "MorseMatching"@ as a new data type and
	    allows construction and verification of Morse matchings.
	Text
	    @SUBSECTION "Definition of Morse Matching"@
	    A Morse matching on the Hasse diagram G of the face poset of a simplicial
	    complex $\Delta$ is a subset $M$ of the edges such that:
	Text
	    1.  $M$ is a matching on $G$.
	Text
	    2.  The directed graph $(G|_{M^c})\cup \bar{M}$, obtained by reversing all
	    directed edges in $M$, is acyclic.
	Text
	    @SUBSECTION "Properties of Morse Matching" @
	    Constructing a Morse matching on a simplicial complex $\Delta$ gives an
	    order of faces to collapse, producing a complex of the same homotopy type
	    with a smaller $f$-vector.
///

end

--Sample code:

R=QQ[x,y,z,w,s]
D = simplicialComplex monomialIdeal "xyzws"
M = {{{y,z,s},{y,z,w,s}}, {{x},{x,s}}, {{x,y,w},{x,y,z,w}}, {{w},{y,w}}, {{s},{y,s}}}
displayMatching(M,D)
