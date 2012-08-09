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
     
     --computations with Morse matchings
     criticalCells,
     morseCollapse,
     
     --operations on inclusion poset
     reverseEdges,
     
     --components of matchings,
     matching,
     complex,
     inclusionPoset,
     
     --operation to display Matchings
     texMatching,
     displayMatching,
     outputTexMatching,
     
     --helper functions to remove after debugging
     indexElement,
     cellVariables,
     indexToCell,
     cellToIndex,
     indexToFace,
     faceToIndex,
     faceToCell,
     cellToFace,
     cellConverter,
     currentCellPosition,
     dimensionFetcher,
     collapseCell,
     trimComplex,
     stripCells,
     
     --exported cached symbols
     cells,
     chaincomplex,
     indextocell,
     celltoindex,
     facetoindex,
     indextoface,
     facetocell,
     celltoface,
     Coefficients,
     collapsedComplex
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
	       tempGraph = reverseEdge(e,tempGraph);
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
	       tempGraph = reverseEdge(e,tempGraph);
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
--     	  (Edges M, simplicial complex D)
--
--OUTPUT:  Boolean
--
--Given a list of edges M in a matching and a digraph G
--(or poset P or simplicial complex D), checks if M is
--a matching on G (or hasseDiagram P / facePoset D.)
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

isMatching(List,SimplicialComplex):= (M,D) -> (
     --Note that this method passes in the edges using the original names of elements.
     P:=dropElements(facePoset D,{{}});
     E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
     G:=hasseDiagram P;
     if all(E,e-> member(e,edges G)) then (
	  if (unique flatten E) == (flatten E) then true else error "Not a matching on G."
     )
     else error "Not a subset of the directed edges of G."
);

------------------------------------------------------
--METHOD:  isAcyclic
--
--INPUT:  Digraph G
--     	  (Edges M, Poset)
--     	  (Edges M, Simplicial Complex)
--
--OUTPUT:  Boolean
--
--Given a digraph G, checks acyclicity of G.
--Given a list of edges and poset/simplicial complex,
--checks acyclicity of inclusion poset with edges
--in list M reversed.
------------------------------------------------------


isAcyclic = method()
isAcyclic(Digraph) := G -> not isCyclic(G)

isAcyclic(List,Poset):= (M,P) -> (
     --Note that this method passes in the edges using the INDICES of poset elements, not the original names.
     G:=hasseDiagram P;
     if all(M,e-> member(e,edges G)) then (
	  if isAcyclic(reverseEdges(M,G)) then true else error "Not acyclic."
     )
     else error "Not a subset of the directed edges of G."
);

isAcyclic(List,SimplicialComplex):= (M,D) -> (
     --Note that this method passes in the edges using the original names of elements.
     P:=dropElements(facePoset D,{{}});
     E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
     G:=hasseDiagram P;
     if all(E,e-> member(e,edges G)) then (
	  if isAcyclic(reverseEdges(E,G)) then true else error "Not acyclic."
     )
     else error "Not a subset of the covering relations in face inclusion poset."
);


------------------------------------------------------
--METHOD:  isMorseMatching
--
--INPUT:  (Edges M, digraph G)
--        (Edges M, poset P)
--     	  (Edges M, SimplicialComplex)
--
--OUTPUT:  Boolean
--
--Given a list of edges M in a matching and a digraph G
--(or poset P or simplicial complex), checks if M is a
-- Morse matching on G (or on the hasseDiagram of P or 
--facePoset D.)
------------------------------------------------------

isMorseMatching = method()
isMorseMatching(List,Digraph):=(M,G)-> (
     isMatching(M,G) and isAcyclic(reverseEdges(M,G))
);

isMorseMatching(List,Poset):=(M,P)-> (
     --Note that this method passes in the edges using the INDICES of poset elements, not the original names.
     isMatching(M,hasseDiagram P) and isAcyclic(reverseEdges(M,hasseDiagram P))
)

isMorseMatching(List,SimplicialComplex):=(M,D)-> (
     --This method inputs matching in terms of ORIGINAL face names.
     P:=dropElements(facePoset D,{{}});
     E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
     isMorseMatching(E,hasseDiagram P)
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
     	  new MorseMatching from hashTable {symbol matching => M, symbol inclusionPoset => P,symbol cache => new CacheTable}
     )
     else error "Not a Morse Matching on P."
)

morseMatching(List,SimplicialComplex) := MorseMatching => (M, D) -> (
     	P:=dropElements(facePoset D, f -> f == {});
	--Note that this method passes in lists of pairs of faces of D, converts them to INDEX edges, then passes into
	--the earlier function for morseMatching(List,Poset).
	--E is a conversion of M into index elements.
      	E:=apply(M, m -> {indexElement(P,m_0), indexElement(P,m_1)});
	MM:=morseMatching(E,P);
	MM.cache.complex = D;
	MM
	)


------------------------------------------------------
--METHOD:  criticalCells
--
--INPUT:  MorseMatching
--
--OUTPUT:  List of Critical Cells
--
-- Given a Morse matching M, this method produces
-- a list of critical cells of the matching.
-- This function will work with EITHER a Morse matching
-- directly from an inclusion poset, or from a matching
-- on the faces of a simplicial complex.
------------------------------------------------------

criticalCells = method()
criticalCells(MorseMatching):= M ->(
     if M.cache.?criticalCells then (
	  M.cache.criticalCells
     )
     else (
	  indx:=select(toList (0..#M.inclusionPoset.GroundSet-1), i -> not member(i,flatten M.matching));
     	  M.cache.criticalCells = (M.inclusionPoset.GroundSet)_indx;
	  M.cache.criticalCells
     )
)

------------------------------------------------------
------------------------------------------------------
--Morse Collapsing Functions
------------------------------------------------------
------------------------------------------------------

------------------------------------------------------
------------------------------------------------------
--Various helper functions for Morse Collapsing
------------------------------------------------------
--Makes cell variables c_(i,j):
cellVariables=method()
cellVariables(MorseMatching) := M ->(
     if M.cache.?cells then (
	  M.cache.cells
     )
     else (
	  local c;
     	  D := M.cache.complex;
     	  F := apply(toList(0..dim D), i-> (fVector D)#i);
     	  varIndices := apply(#F, i-> apply(F_i, j-> (i,j)));
     	  M.cache.cells = apply(varIndices, i-> apply(i, j-> (symbol c)_j))
     )
)
------------------------------------------------------
------------------------------------------------------

------------------------------------------------------
------------------------------------------------------
--Makes six hash tables for converting between cells, faces, and indices:
------------------------------------------------------
------------------------------------------------------
--Index to Cell
------------------------------------------------------
------------------------------------------------------
indexToCell = method()
indexToCell(MorseMatching) := M -> (
     if M.cache.?indextocell then (
	  M.cache.indextocell
     )
     else (
     D:= M.cache.complex;
     C:= cellVariables(M);
     M.cache.indextocell = hashTable flatten apply(# C, fdim -> 
     	  apply(#(C_fdim), j ->
	       {indexElement(M.inclusionPoset,support(flatten entries D.cache.faces#fdim)_j),(C_fdim)_j}))
     )
)
------------------------------------------------------
------------------------------------------------------
--Cell Variables to Indices:
------------------------------------------------------
------------------------------------------------------
cellToIndex = method()
cellToIndex(MorseMatching):= M -> (
     if M.cache.?celltoindex then (
	  M.cache.celltoindex
     )
     else (
	  K:=indexToCell(M);
     	  M.cache.celltoindex = hashTable apply(keys M.cache.indextocell, i -> {M.cache.indextocell#i, i})
     )
)
------------------------------------------------------
------------------------------------------------------
--Indexes to Faces:
------------------------------------------------------
------------------------------------------------------
indexToFace = method()
indexToFace(MorseMatching):= M -> (
     if M.cache.?indextoface then (
     	  M.cache.indextoface
     )
     else (
	  D:= M.cache.complex;
     	  C:= cellVariables(M);
     	  M.cache.indextoface = hashTable flatten apply(#C, fdim -> 
     	       apply(#(C_fdim), j ->
	       	    {indexElement(M.inclusionPoset,support(flatten entries D.cache.faces#fdim)_j),support(flatten entries D.cache.faces#fdim)_j}))
     )
)
------------------------------------------------------
------------------------------------------------------
--Faces to Indices:
------------------------------------------------------
------------------------------------------------------
faceToIndex = method()
faceToIndex(MorseMatching):= M -> (
     if M.cache.?facetoindex then (
     	  M.cache.facetoindex
     )
     else (
	  D:=M.cache.complex;
	  C:=cellVariables(M);
	  K:=indexToFace(M);
	  M.cache.facetoindex = hashTable apply(keys M.cache.indextoface, i -> {M.cache.indextoface#i, i})
     )
)

------------------------------------------------------
------------------------------------------------------
--Cells to Faces
------------------------------------------------------
------------------------------------------------------
faceToCell = method()
faceToCell(MorseMatching):= M -> (
     if M.cache.?facetocell then (
	  M.cache.facetocell
     )
     else (
     	  D:=M.cache.complex;
     	  C:=cellVariables(M);
     	  K:=faceToIndex(M);
     	  J:=indexToCell(M);
     	  M.cache.facetocell = hashTable apply(keys K, k-> {k,J#(K#k)})
     )
)
------------------------------------------------------
------------------------------------------------------
--Faces to Cells
------------------------------------------------------
------------------------------------------------------
cellToFace = method()
cellToFace(MorseMatching):= M -> (
     if M.cache.?celltoface then (
	  M.cache.celltoface
     )
     else (
	  D:=M.cache.complex;
	  C:=cellVariables(M);
	  K:=cellToIndex(M);
	  J:=indexToFace(M);
	  M.cache.celltoface = hashTable apply(keys K, k-> {k,J#(K#k)})
     )
)

------------------------------------------------------
------------------------------------------------------
--Given an edge in matching M, converts to cell format.
------------------------------------------------------
------------------------------------------------------
cellConverter = method()
cellConverter(List,MorseMatching):= (E,M) -> (
     --This name fetcher function assumes the input is an edge in ORIGINAL matching, 
     --e.g. {{x},{x,y}}.
     F:=faceToCell(M);
     --outputs cell names
     {F#(first E), F#(last E)}
)

------------------------------------------------------
------------------------------------------------------
--Examines list of cells NOT yet removed by collapse.
--After using stripCells, this index may change.
------------------------------------------------------
------------------------------------------------------

currentCellPosition = method()
currentCellPosition(IndexedVariable,MorseMatching):= (c,M) -> (
     d:= first last c;
     --Note that before first collapse, this will be
     --the same as the index of c_(i,j).
     --This is NOT a constant.
     {d,position(M.cache.cells_d, i-> i === c)}
)

------------------------------------------------------
------------------------------------------------------
--Be careful about using this, as this actually removes
--cells from M.cache.cells.
------------------------------------------------------
------------------------------------------------------

stripCells = method()
stripCells(List,MorseMatching):= (e,M) ->(
     if not M.cache.?cells then cellVariables M;
     E := cellConverter(e,M);
     C1 := currentCellPosition(E_0,M);
     C2 := currentCellPosition(E_1,M);
     if (C1_1 === null) or (C2_1 === null) then error "Already removed edge.";
     cellList := M.cache.cells;
     cellList = replace(first C1,drop(cellList_(first C1),{C1_1,C1_1}),cellList);
     M.cache.cells = replace(first C2,drop(cellList_(first C2),{C2_1,C2_1}),cellList)
)

------------------------------------------------------
------------------------------------------------------
--Given an edge in matching M, calculates dimension of
--lower dimensional cell.
------------------------------------------------------
------------------------------------------------------

dimensionFetcher = method()
dimensionFetcher(List,MorseMatching):= (E,M) -> (
     --This fetcher function assumes the input is an edge in ORIGINAL matching, 
     --e.g. {{x},{x,y}}.
     F:=faceToCell(M);
     --outputs the dimension of smaller edge
     first last F#(first E)
)



------------------------------------------------------
--METHOD:  morseCollapse
--
--INPUT:  MorseMatching
--
--OUTPUT:  (List,ChainComplex)
--     List of critical cells and chain complex of
--     maps after contraction by Morse matching.
------------------------------------------------------

morseCollapse = method(Options=> {symbol Coefficients => QQ})
morseCollapse(MorseMatching):= opts -> (M) ->(
     critCells := criticalCells(M);
     if not M.cache.?indextoface then indexToFace(M);
     E:=apply(M.matching, e-> {M.cache.indextoface#(e_0),M.cache.indextoface#(e_1)});
     while E =!={} do (
	  collapseCell(first E,M);
	  E = drop(E,1);
     );
     M.cache.collapsedComplex = M.cache.chaincomplex
)


------------------------------------------------------
--METHOD:  collapseCell
--
--INPUT:  (List,MorseMatching)
--
--OUTPUT: MorseMatching
-- 
-- Removes an edge in the Morse matching, returns 
-- original Morse Matching, with cache table
-- contain contracted cell complex.
------------------------------------------------------

collapseCell = method(Options => {symbol Coefficients => QQ})
collapseCell(List,MorseMatching):= opts -> (e,M) ->(
     if not M.cache.?chaincomplex then M.cache.chaincomplex = chainComplex M.cache.complex;
     if not M.cache.?cells then cellVariables(M);
     V := M.cache.cells;
     C := M.cache.chaincomplex;
     --------------------------------
     --Initializes the 
     D := new ChainComplex;
     kk :=opts.Coefficients;
     D.ring = kk;
     --------------------------------
     --Puts edges in E into appropriate form.
     --------------------------------
     c := cellConverter(e,M);
     --------------------------------
     --Counts the number of cells of each dimension left, and removes one from d and d+1.
     d := dimensionFetcher(e,M);
     numCells := apply(#V, i-> if (i === d) or (i===(d+1)) then (#V_i-1) else #V_i);
     --------------------------------
     --Defines the modules in the chain complex
     D#-1 = QQ^1;
     for i from 0 to #numCells -1 do (
     	  D#i = QQ^(numCells_i);
     );
     --------------------------------
     --Construct NEW chain maps D.dd_(i-1), D.dd_i and D.dd_(i+1):
     --Bring them over from "trimComplex" function
     --------------------------------
     T:=trimComplex(c,C,M);
     D.dd_d = map(D#(d-1),D#d,T_0);
     if T_1 == map(QQ^1,QQ^0,0) then (
     	  D.dd_(d+1) = map(D#d,D#(d+1),T_1);
     )
     else (
	  D.dd_(d+1) = map(D#d,D#(d+1),transpose T_1);
     );
     if d+2 <= dim M.cache.complex then (
     	  D.dd_(d+2) = map(D#(d+1),D#(d+2),T_2);
     );
     scan(drop(toList(0..#numCells-1),{d,d+2}), i-> D.dd_i = C.dd_i);
     --------------------------------
     --Final stage:  Set chaincomplex to new chain complex,
     --then delete {c_(i,j),c_(i+1,k)} from M.cache.cells.
     --------------------------------
     M.cache.chaincomplex = D;
     stripCells(e,M)
)

------------------------------------------------------
--METHOD:  trimComplex
--
--INPUT:  (List,ChainComplex,MorseMatching)
--     	  (Edge E, M.cache.chaincomplex,M)
--
--OUTPUT: Differential maps {D_d,transpose D_(d+1), D_(d+2)}
-- 
-- Inputs an edge, the chain complex, and a morse matching, and outputs
-- the chain maps for the complex with c_i, c_j from E={c_i,c_j} removed.
------------------------------------------------------


trimComplex = method()
trimComplex(List,ChainComplex,MorseMatching):= (c,C,M) ->(
     ------------------------------------------------------
     --Fetches {dimension,index} pairs for edge E from cell list.
     ------------------------------------------------------
     idx1 := currentCellPosition(c_0,M);
     idx2 := currentCellPosition(c_1,M);
     ------------------------------------------------------
     --Sets dimension to the dimension of the lower dim cell.
     ------------------------------------------------------
     d := idx1_0;
     ------------------------------------------------------
     --Forms map D.dd_d by dropping row corresponding to c_0.
     ------------------------------------------------------
     A := submatrix'(C.dd_d,,{idx1_1});
     ------------------------------------------------------
     --If d+2 is NOT too large, forms map D.dd_(d+2) by dropping
     --rows corresponding to c_1.
     ------------------------------------------------------
     if d+2 <= dim M.cache.complex then (
     	  N := submatrix'(C.dd_(d+2),{idx2_1},);
     );
     ------------------------------------------------------
     --Set deletedCell to be column we wish to remove.
     --We work with transpose for each of "row" operations.
     ------------------------------------------------------
     deletedCell := first entries submatrix(transpose C.dd_(d+1),{idx2_1},);
     a := deletedCell_(idx1_1);
     ------------------------------------------------------
     --Set B to be (transposed) submatrix with deletedCell removed,
     --Then select all rows which have a nonzero entry in column c_1.
     ------------------------------------------------------
     B := entries submatrix'(transpose C.dd_(d+1),{idx2_1},);
     --
     --first entry is position, second entry is coefficient in idx1_1 position.
     -- B -> {i,j}
     attachedCells := apply(select(#B, r -> (B_r)_(idx1_1) !=0), n -> {n,(B_n)_(idx1_1)});
     ------------------------------------------------------
     --If d+2 is NOT too large, forms map D.dd_(d+2) by dropping
     --rows corresponding to c_1.
     ------------------------------------------------------
     newCellMaps := apply(attachedCells, i-> {first i, B_(first i)-(((B_(first i))_(idx1_1)/a)*deletedCell)});
     for m in newCellMaps do (
     	  B = replace(first m, last m, B);
     );
     if B === {} then B = matrix{{0_(C.ring)}};
     {A,submatrix'(matrix B,,{idx1_1}),N}
)


------------------------------------------------------------------
------------------------------------------------------------------
--toString and Net for Displaying Permutations
------------------------------------------------------------------
------------------------------------------------------------------


toString MorseMatching := M -> toString apply(M.matching, p-> (M.inclusionPoset_(p_0)=>M.inclusionPoset_(p_1)))

net MorseMatching := M -> toString M


------------------------------------------------------------------
------------------------------------------------------------------
--Functions for Latex / TikZ display
------------------------------------------------------------------
------------------------------------------------------------------

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
    P:=dropElements(facePoset D, f -> f == {});
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
    --removed edges to emptyset here - stylistic choice.
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
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n") |
    concatenate("\\foreach \\to/\\from in ", toString revEdgeList, "\n\\draw [<<-,thick, red] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )

texMatching(List,SimplicialComplex) := String => opts -> (M,D) -> (
     P:=dropElements(facePoset D, f -> f == {});
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
