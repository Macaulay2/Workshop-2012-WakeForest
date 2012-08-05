-- -*- coding: utf-8 -*-

--needsPackage "Polymake"
needsPackage "Polyhedra"

newPackage(
	"gfanInterface2",
	Version => "0.3.1", 
	Date => "July 22, 2010",
	Authors => {
		{Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => ""},
		{Name => "Andrew Hoefel", Email => "andrew.hoefel@mathstat.dal.ca", HomePage => "http://www.mathstat.dal.ca/~handrew/"}
	},
	Headline => "Interface to A. Jensen's gfan package",
	Configuration => {
		"path" => "", 
		"fig2devpath" => "", 
		"keepfiles" => false, 
		"verbose" => false
	},
	DebuggingMode => true
)

--needsPackage "Polymake"
needsPackage "Polyhedra"

export {
	MarkedPolynomialList,
	markedPolynomialList,
	PolymakeObject,
	PolymakeCone,
	PolymakeFan,
	polymakeFanToFan,
	polymakeConeToCone,
	gfan, -- done!
	gfanBuchberger, -- done!
	gfanDoesIdealContain, -- done!
	gfanFanCommonRefinement, -- v0.4 done!
	gfanFanLink, -- v0.4  needs a non-star example
	gfanFanProduct, -- v0.4 done!
	gfanGroebnerCone, -- done!
	gfanHomogeneitySpace, -- done!
	gfanHomogenize, -- done!
	gfanInitialForms, -- done!
	gfanInteractive, -- done! i.e. not implemented
	gfanIsMarkedGroebnerBasis, -- done!
	gfanKrullDimension, -- done!
	gfanLatticeIdeal, -- v0.4 done!
	gfanLeadingTerms, -- done!
	gfanMarkPolynomialSet, -- done!
	gfanMinkowskiSum, -- v0.4 -- implemented, documented, but i don't understand/agree with the output 
	gfanMinors, -- v0.4 done!
	gfanPolynomialSetUnion, -- done!
	gfanRender, 
	gfanRenderStaircase, 
	gfanSaturation, -- done!
	gfanSecondaryFan, -- v0.4 -- done! but could use better doc
	gfanStats, -- done!
	gfanSubstitute, -- done!
	gfanToLatex, -- done!
	gfanToPolyhedralFan, -- done!
	gfanTropicalBasis,  -- done! but could use an explanation of the example
	gfanTropicalBruteForce, -- done!
	gfanTropicalEvaluation, -- v0.4 -- done!
	gfanTropicalFunction, -- v0.4 -- done!
	gfanTropicalHyperSurface, -- v0.4 -- done!
	gfanTropicalIntersection, -- done!
	gfanTropicalLifting,
	gfanTropicalLinearSpace, -- v0.4 -- done! doc needs double checking
	gfanTropicalMultiplicity, -- example needed.
	gfanTropicalRank, -- v0.4 -- done! 
	gfanTropicalStartingCone, -- done!
	gfanTropicalTraverse, -- done!
	gfanTropicalWeilDivisor -- v0.4
	--gfanFunctions -- for testing purposes
}

gfanPath = gfanInterface2#Options#Configuration#"path"
if gfanPath == "" then gfanPath = prefixDirectory | currentLayout#"programs"

fig2devPath = gfanInterface2#Options#Configuration#"fig2devpath"
gfanVerbose = gfanInterface2#Options#Configuration#"verbose"
gfanKeepFiles = gfanInterface2#Options#Configuration#"keepfiles"

PolymakeTypes = {
	{	"sym" => "AMBIENTDIM",
		"str" => "AMBIENT_DIM",
		"type" => "cardinal"
	},
	{	"sym" => "DIM",
		"str" => "DIM",
		"type" => "cardinal"
	},
	{	"sym" => "LINEALITYDIM",
		"str" => "LINEALITY_DIM",
		"type" => "cardinal"
	},
	{	"sym" => "RAYS",
		"str" => "RAYS",
		"type" => "matrix"
	},
	{	"sym" => "NRAYS",
		"str" => "N_RAYS",
		"type" => "cardinal"
	},
	{	"sym" => "LINEALITYSPACE",
		"str" => "LINEALITY_SPACE",
		"type" => "matrix"
	},
	{	"sym" => "ORTHLINEALITYSPACE",
		"str" => "ORTH_LINEALITY_SPACE",
		"type" => "matrix"
	},
	{	"sym" => "FVECTOR",
		"str" => "F_VECTOR",
		"type" => "vector"
	},
	{	"sym" => "CONES",
		"str" => "CONES",
		"type" => "incidenceMatrix"
	},
	{	"sym" => "MAXIMALCONES",
		"str" => "MAXIMAL_CONES",
		"type" => "incidenceMatrix"
	},
	{	"sym" => "PURE",
		"str" => "PURE",
		"type" => "boolean"
	},
	{	"sym" => "MULTIPLICITIES",
		"str" => "MULTIPLICITIES",
		"type" => "columnVector"
	},
	{	"sym" => "RAYVALUES",
		"str" => "RAY_VALUES",
		"type" => "matrix"
	},
	{	"sym" => "LINEALITYVALUES",
		"str" => "LINEALITY_VALUES",
		"type" => "matrix"
	},
	{	"sym" => "MAXIMALCONESCOMPRESSED",
		"str" => "MAXIMAL_CONES_COMPRESSED",
		"type" => "incidenceMatrix"
	},
	{	"sym" => "CONESCOMPRESSED",
		"str" => "CONES_COMPRESSED",
		"type" => "incidenceMatrix"
	},
	{	"sym" => "MULTIPLICITIESCOMPRESSED",
		"str" => "MULTIPLICITIES_COMPRESSED",
		"type" => "columnVector"
	},
	{	"sym" => "DIM",
		"str" => "DIM",
		"type" => "cardinal"
	},
	{	"sym" => "IMPLIEDEQUATIONS",
		"str" => "IMPLIED_EQUATIONS",
		"type" => "matrix"
	},
	{	"sym" => "FACETS",
		"str" => "FACETS",
		"type" => "matrix"
	},
	{	"sym" => "RELATIVEINTERIORPOINT",
		"str" => "RELATIVE_INTERIOR_POINT",
		"type" => "vector"
	},
	--{	"sym" => "MYEULER", -- undocumented by gfan
	--	"str" => "MY_EULER",
	--	"type" => "cardinal"
	--},
	{	"sym" => "SIMPLICIAL", -- undocumented by gfan
		"str" => "SIMPLICIAL",
		"type" => "boolean"
	}
} / hashTable

MarkedPolynomialList = new Type of List
MarkedPolynomialList.synonym = "marked polynomial list";
  -- Currently: this is a list {inL,L}, where 
  --   inL is a list of monomials (with coefficient, often 1)
  --   L is a list of polynomials
  -- and L and inL have the same length, and the
  -- the monomial inL#i is the marked monomial, which
  -- should occur with the same coefficient in L#i.

PolymakeObject = new Type of HashTable;
PolymakeObject.synonym = "Polymake Object";

PolymakeFan = new Type of PolymakeObject;
PolymakeFan.synonym = "Polymake Fan";

PolymakeCone = new Type of PolymakeObject;
PolymakeCone.synonym = "Polymake Cone";

net PolymakeObject := P -> (
	goodkeys := select(keys P, k -> not member(k, {"rawstring", "rawblocks", "header"}));
	stack apply(goodkeys, k -> (net k) | " => " | (net P#k))
)

markedPolynomialList = method();
markedPolynomialList List := L -> (
	if #L =!= 2 then 
		error("A MarkedPolynomialList must be a list containing "
			| "a list of initial terms and a list of polynoimals."
		);
	if #(first L) =!= #(last L) then
		error("The lists of initial terms and polynomials in a "
			| "MarkedPolynomialList must have the same length."
		);
	if #(first L) =!= 0 then (
		R := class first first L;
		if class R =!= PolynomialRing then
			error("Initial terms and polynomials in a MarkedPolynomialList "
				| "should be elements of a polynomial ring."
			);
		scan(transpose L, t -> (
			m := first t;
			f := last t;
			if class m =!= R or class f =!= R then 
				error("Each initial term and polynomial of a MarkedPolynomialList "
					| "should be a member of the same polynomial ring."
				);
			if #(terms m) =!= 1 then
				error("Initial terms of a MarkedPolynomialList should consist "
					| "of a single term."
				);
			if not member(m, terms f) then
				error("Each initial terms of a MarkedPolynomialList should "
					| "appear in its corresponding polynomial. "
					| "(" | toString m | " is not a term of " | toString f | ")."
				);
			)
		);
	);
	new MarkedPolynomialList from L
)

expression MarkedPolynomialList := L -> 
	expression apply(transpose L, t -> (
		m := t#0;
		f := t#1;
		out := "(" | toString m | ")";
		if leadCoefficient(f-m) > 0 then 
			out = out | " +";
		if f-m != 0 then 
			return out | " " | toString(f-m)
			else
			return out;
		)
	)

net MarkedPolynomialList := L -> net expression L

RingMap MarkedPolynomialList := (F, L) -> L/(a-> a/F)

--------------------------------------------------------
--------------------------------------------------------
-- PARSING FUNCTIONS
--------------------------------------------------------
--------------------------------------------------------

gfanParseList = method();
gfanParseList String := (S) -> (
	S = replace("\n", "", S);
	stack := {};
	r := regex(///[\{,\}]///, S);
	popstate := false;
	while #r === 1 do (
		startpos := first first r;
		character := substring(startpos,1,S);
		prestring := substring(0, startpos, S);
		S = substring(startpos+1, #S,S);
		if character == "," then (
			if not popstate then (
				stack = append(drop(stack,-1), append(last stack, prestring));
			);
			popstate = false;
		) else if character == "{" then (
			stack = append(stack, {});
		) else if #stack == 0 then (
			error "Parsing error";
		) else if #stack == 1 then (
			if not popstate then (
				stack = append(drop(stack,-1), append(last stack, prestring));
			);
			return first stack;
		) else (
			if not popstate then (
				stack = append(drop(stack,-1), append(last stack, prestring));
			);
			stack = append(drop(stack,-2), append(stack#(#stack -2), last stack));
			popstate = true;
		);
		r = regex(///[\{,\}]///, S);
	);
	error "Parsing error";
)

gfanParseMarkedPoly = method();
gfanParseMarkedPoly String := (S) -> (
	indices := first regex(///\`[:space:]*.[^+-]*///,S);
	return { value substring(first indices, last indices,S), value S};
	--match from the start of the string all whitespace, one
	--non-white space character and then everything until the +/-
)

gfanParseIdeals = method()
gfanParseIdeals String := (s) -> (
	--needs to be simplified
	G := separate("\n,",s);
	firstLine := G#0;
	firstLine = separate("\n", firstLine);
	firstLine = drop(firstLine, 1);  -- remove the ring from the first line
	tempStr  := "";
	scan(firstLine, t -> tempStr = concatenate(tempStr, "\n", t)); -- build the firstline

	G = drop(G,1);  -- drop the old first entry
	G = prepend(tempStr, G); -- and then add the first entry minus the ring
	H := apply(G, t -> replace(///[\{\}]*///,"",t));
	apply(H, s -> value("{"|s|"}"))
)

gfanParseIdeal = method()
gfanParseIdeal String := (s) -> (
	G := separate("]",s);
	G = drop(G,1);
	value concatenate G 
)

gfanParseMarkedIdeal = method()
gfanParseMarkedIdeal String := (s) -> (
	G := separate("]",s);
	G = drop(G,1);
	markedPolynomialList transpose apply(gfanParseList(concatenate G), p -> gfanParseMarkedPoly(p))
)

gfanParseMarkedIdeals = method()
gfanParseMarkedIdeals String := (s) -> (
	G := separate("]",s);
	G = drop(G,1);
	apply(gfanParseList(concatenate G), L -> markedPolynomialList transpose apply(L, p -> gfanParseMarkedPoly(p)))
)

gfanParseMPL = method()
gfanParseMPL String := (s) -> (
	G := separate("]",s);
	G = drop(G,1);
	markedPolynomialList transpose apply(gfanParseList(concatenate G), p -> gfanParseMarkedPoly(p))
)

gfanParseLMPL = method()
gfanParseLMPL String := (s) -> (
	G := separate("]",s);
	G = drop(G,1);
	apply(gfanParseList(concatenate G), L -> 
		markedPolynomialList transpose apply(L, p -> gfanParseMarkedPoly(p)))
)

gfanParseMPLPair = method()
gfanParseMPLPair String := (s) -> (
	G := separate("\n",s);
	G = drop(G,1); -- drop the ring
	L := gfanParseList("{"| replace(///\{///, ",{", concatenate G ) | "}");
	P := {apply(L#1, gfanParseMarkedPoly), apply(L#2, gfanParseMarkedPoly)};
	apply(P, c -> markedPolynomialList transpose c)
)

gfanParseIdealPair = method()
gfanParseIdealPair String := (s) -> (
	G := separate("\n",s);
	G = drop(G,1);
	drop(value ("{"| replace(///\{///, ",{", concatenate G ) | "}"), 1)
)

gfanParseMarkedIdealPair = method()
gfanParseMarkedIdealPair String := (s) -> (
	G := separate("\n",s);
	G = concatenate drop(G,1);
	apply(drop(regex(///(\{[^\}]*\})(\{[^\}]*\})///, G),1), i-> transpose apply(gfanParseList(substring(first i, last i, G)), p-> gfanParseMarkedPoly(p)))
)

gfanParseInteger = method()
gfanParseInteger String := (s) -> value s

gfanParseBool = method()
gfanParseBool String := (s) -> s == "true\n"

gfanParseBoolInteger = method()
gfanParseBoolInteger String := (s) -> s == "1\n"


------------------------------------------
-- Polymake Parsing 
------------------------------------------

gfanParsePolyhedralFan = method()
gfanParsePolyhedralFan String := (s) -> (
	B := select(sublists(lines s, l -> #l =!= 0, toList, l -> null), l -> l =!= null);
	header := first B; --first list of lines
	if #B < 2 and #header < 2 then error(concatenate header);
	-- blocks are lists of the form {typeString, list of lines, parsed value}
	blocks := apply(drop(B,1), L -> gfanParsePolymakeBlock L);
	rawBlocks := hashTable apply(blocks, P -> first P => P#1);
	parsedBlocks := apply(select(blocks, Q -> last Q =!= null), P -> first P => last P);
	new gfanParsePolymakeHeader(header) from hashTable({ 
		"header" => stack header, 
		"rawstring" => s, 
		"rawblocks" => rawBlocks
		} | parsedBlocks
	)
)

gfanParsePolymakeHeader = method()
gfanParsePolymakeHeader List := (L) -> (
	typePosition := position(L, l -> "_type" == first separate(" ", l));
	typeLine := L#typePosition;
	typeWords := separate(" ", typeLine);
	if #typeWords === 2 and typeWords#1 == "PolyhedralCone" then 
		PolymakeCone
	else if #typeWords === 2 and typeWords#1 == "PolyhedralFan" then
		PolymakeFan
	else
		PolymakeObject
)

gfanParsePolymakeBlock = method()
gfanParsePolymakeBlock List := (L) -> (
	typeString := first L;
	data := drop(L,1);
	typePosition := position(PolymakeTypes, T -> T#"str" == typeString);
	if typePosition === null then return typeString => null;  -- Unrecognized type
	typeTuple := PolymakeTypes#typePosition;
	return {typeString, L, gfanParsePolymakeType(typeTuple#"type", data)};
)

gfanParsePolymakeType = method()
gfanParsePolymakeType (String, List) := (T, L) -> (
	L = apply(L, str -> replace("[[:space:]]*#.*|[[:space:]]+$","" ,str));
	if T == "cardinal" then (
		value first L
	)
	else if T == "matrix" then (
		apply(L, l -> select(separateRegexp(" +", l) / value, x -> x =!= null))
	)
	else if T == "incidenceMatrix" then (
		apply(L, l -> value replace("[[:space:]]+", ",", l))
	)
	else if T == "boolean" then (
		1 === value first L
	)
	else if T == "vector" then (
		select(separateRegexp(" +", first L) / value, x -> x =!= null)
	)
	else if T == "columnVector" then (
		flatten apply(L, l -> select(separateRegexp(" +", l) / value, x -> x =!= null))
	)
)

polymakeFanToFan = method()

polymakeFanToFan PolymakeFan := (F) -> (
	linealitySpace := posHull transpose matrix(F#"LINEALITY_SPACE" | - F#"LINEALITY_SPACE");
	fan apply(F#"MAXIMAL_CONES", L -> posHull(posHull transpose matrix apply(L, i -> F#"RAYS"#i), linealitySpace))
)

polymakeConeToCone = method()

polymakeConeToCone PolymakeCone := (C) -> (
	linealitySpace := posHull transpose matrix(C#"LINEALITY_SPACE" | - C#"LINEALITY_SPACE");
	posHull(posHull transpose matrix C#"FACETS", linealitySpace)
)

polymakeFan = method() 
polymakeFan (Matrix,Matrix,List) := (rays, lineality, maxcones) ->  (
	ambientdim := numRows(rays);
	lindim := numColumns(lineality);
	dim := numColumns(lineality) + max apply(maxcones, c-> #c);
	orthlin := entries transpose gens kernel lineality;
	lin := entries transpose lineality;
	r := entries transpose rays;
	numr := numColumns(rays);
	pure := all(maxcones, c -> #c == dim);
	--rawstr := blah;
	--Not done yet!
)

------------------------------------------
-- gfan toString functions
------------------------------------------
-- These functions produce strings that 
-- gfan can read
------------------------------------------

joinStrings = (S, between, before, after) -> (
	str := before | first S;
	S = drop(S, 1);
	scan(S, s -> str = str | between | s);
	str | after
)

gfanSymbolToString = method()
gfanSymbolToString Symbol := (X) -> (
	toString(X) | "\n"  
	--- toExternalString will write the word symbol if X is assigned
	--- and this is not desireable
)

gfanIdealToString = method()
gfanIdealToString Ideal := (I) -> 
	gfanPolynomialListToString flatten entries gens I

gfanPolynomialListToString = method()
gfanPolynomialListToString List := (L) ->
	joinStrings(L/toExternalString, "," | newline, "{", "}" | newline)

--Takes a marked polynomial as a pair: {inital term, polynomial}
gfanMarkedPolynomialToString = method()
gfanMarkedPolynomialToString List := (L) -> (
		out := toExternalString(first L);
		if (last L) - (first L) != 0 then 
			out = out | " + " | toExternalString((last L) - (first L));
		out
)

gfanMPLToString = method()
gfanMPLToString List := (L) -> (
	L = (transpose L) / gfanMarkedPolynomialToString;
	joinStrings(L, "," | newline, "{", "}" | newline)
)

gfanListOfPolynomialListsToString = method()
gfanListOfPolynomialListsToString := (L) -> (
	out := "{";
	n := #L - 1;
	for i from 0 to n do (
		out = out | gfanPolynomialListToString(L#i);
		if i < n then out = out | "," else out = out | "}";
		out = out | newline;
	);
	return out;
)

--list of marked polynomial lists to string
gfanLMPLToString = method()
gfanLMPLToString := (L) -> (
	out := "{";
	n := #L - 1;
	for i from 0 to n do (
		out = out | gfanMPLToString(L#i);
		if i < n then out = out | "," else out = out | "}";
		out = out | newline;
	);
	return out;
)

gfanSymmetriesToString = method()
gfanSymmetriesToString := (L) -> (
	if L === null then return "";
	out := "{";
	n := #L - 1;
	for i from 0 to n do (
		out = out | gfanSymmetryToString(L#i);
		if i < n then out = out | "," else out = out | "}";
		out = out | newline;
	);
	return out;
)

gfanSymmetryToString = method()
gfanSymmetryToString List := (L) -> (
	if L === null then return "";
	out := "(";
	n := #L - 1;
	for i from 0 to n do (
		out = out | toExternalString(L#i);
		if i < n then out = out | "," else out = out | ")";
		out = out | newline;
	);
	return out;
)

gfanIntegerListToString = method()
gfanIntegerListToString := (L) -> if L === null then ""  else toString L

gfanMatrixToString = method()
gfanMatrixToString := (M) -> if M === null then ""  else toString entries M

gfanVectorConfigToString = method()
gfanVectorConfigToString := (L) -> (
	if L === null then "" 
	else joinStrings( apply(L, a -> joinStrings( a/toString, ",", "(", ")")), ",", "{", "}")
)

gfanRingToString = method()
gfanRingToString PolynomialRing := (R) -> (
	p := char R;
	out := if p === 0 then "Q" else "Z/"|p|"Z";
	out = out | toExternalString(new Array from gens R) | newline;
	return out;
)

gfanMPLToRingToString = method()
gfanMPLToRingToString List := (L) -> (
	R := ring first last L; 
	p := char R;
	out := if p === 0 then "Q" else "Z/"|p|"Z";
	out = out | toExternalString(new Array from gens R) | newline;
	return out;
)


--------------------------------------------------------
-- gfanArgumentToString
--------------------------------------------------------

gfanArgumentToString = method()
gfanArgumentToString (String, String, Thing) := (cmd, key, value) -> (
	if value === null or value === false then 
		return "";

	cmdLineValue := false; -- whether a value is passed on the commandline
	if cmdLineArgs#?cmd and member(key, cmdLineArgs#cmd) then
		cmdLineValue = true;

	" " | argStrs#key | (if cmdLineValue then " " | value else "")
)


--------------------------------------------------------
-- runGfanCommand
--------------------------------------------------------

runGfanCommand = (cmd, opts, data) -> (
	tmpFile := gfanMakeTemporaryFile data;
	args := concatenate apply(keys opts, key -> gfanArgumentToString(cmd, key, opts#key));
	ex := gfanPath | cmd | args | " < " | tmpFile | " > " | tmpFile | ".out" | " 2> " | tmpFile | ".err";
	if gfanVerbose then << ex << endl;
	run ex;
	out := get(tmpFile | ".out");
	gfanRemoveTemporaryFile tmpFile;
	gfanRemoveTemporaryFile(tmpFile | ".out");
	gfanRemoveTemporaryFile(tmpFile | ".err");
	out
)

gfanMakeTemporaryFile = (data) -> (
	tmpName := temporaryFileName();
	if gfanVerbose then << "using temporary file " << tmpName << endl;
	tmpFile := openOut tmpName;
	tmpFile << data << close;
	tmpName
)

gfanRemoveTemporaryFile = (fileName) -> 
	if not gfanKeepFiles then removeFile fileName

runGfanCommandCaptureBoth = (cmd, opts, data) -> (
	tmpFile := gfanMakeTemporaryFile data;
	args := concatenate apply(keys opts, key -> gfanArgumentToString(cmd, key, opts#key));
	ex := gfanPath | cmd | args | " < " | tmpFile | " > " | tmpFile | ".out" | " 2> " | tmpFile | ".err";
	if gfanVerbose then << ex << endl;
	run ex;
	out := get(tmpFile | ".out");
	err := get(tmpFile | ".err");
	gfanRemoveTemporaryFile tmpFile;
	gfanRemoveTemporaryFile(tmpFile | ".out");
	gfanRemoveTemporaryFile(tmpFile | ".err");
	(out,err)
)

runGfanCommandCaptureError = (cmd, opts, data) -> (
	tmpFile := gfanMakeTemporaryFile data;
	args := concatenate apply(keys opts, key -> gfanArgumentToString(cmd, key, opts#key));
	ex := gfanPath | cmd | args | " < " | tmpFile | " > " | tmpFile | ".out" | " 2> " | tmpFile | ".err";
	if gfanVerbose then << ex << endl;
	run ex;
	err := get(tmpFile | ".err");
	gfanRemoveTemporaryFile tmpFile;
	gfanRemoveTemporaryFile(tmpFile | ".out");
	gfanRemoveTemporaryFile(tmpFile | ".err");
	err
)


---------------------------------------------------
-- Information on functions and arguments
--------------------------------------------------

-- Check capitalization
-- This is a list of which arguments are used for which function.
-- Currently this is not used.
argFuncs = {
	"d" => {gfanRenderStaircase, gfanTropicalStartingCone, gfanTropicalLinearSpace},
	"e" => {gfan},
	"g" => {gfan,gfanBuchberger,gfanTropicalStartingCone},
	"h" => {gfanToLatex,gfanTropicalBasis},
	"i" => {gfanHomogenize},
	"m" => {gfanLeadingTerms,gfanRenderStaircase},
	"n" => {gfanTropicalLinearSpace},
	"L" => {gfanRender},
	"r" => {gfanBuchberger},
	"s" => {gfanPolynomialSetUnion},
	"t" => {gfanTropicalIntersection},
	"w" => {gfanBuchberger,gfanHomogenize,gfanRenderStaircase},
	"W" => {gfanBuchberger},
	"asfan" => {gfanGroebnerCone},
	"disableSymmetryTest" => {gfan},
	--missing help
	"ideal" => {gfanInitialForms},
	"noincidence" => {gfanTropicalTraverse},
	"pair" => {gfanGroebnerCone, gfanInitialForms},
	"polynomialset" => {gfanToLatex},
	"polynomialsetlist" => {gfanToLatex},
	"restrict" => {gfanGroebnerCone,gfanToPolyhedralFan},
	"shiftVariables" => {gfanRender},
	-- "subspace" => {gfan}, -- missing v0.4
	"symmetry" => {gfan,gfanTropicalTraverse,gfanToPolyhedralFan},
	"tplane" => {gfanTropicalIntersection},
}

-- Fix capitalization
-- This converts the macaulay 2 argument names to gfan argument names
argStrs = hashTable {
	"d" => "-d",
	"e" => "-e",
	"g" => "-g",
	"h" => "-h",
	"i" => "-i",
	"i1" => "-i1", 
	"i2" => "-i2",
	"L" => "-L",
	"m" => "-m",
	"n" => "-n",
	"M2" => "-M2",
	"r" => "-r",
	"s" => "-s",
	"t" => "-t",
	"w" => "-w",
	"W" => "-W",
	"asfan" => "--asfan",
	"disableSymmetryTest" => "--disablesymmetrytest",
	"dressian" => "--dressian",
	"help" => "--help",
	"ideal" => "--ideal",
	"kapranov" => "--kapranov",
	"mark" => "--mark",
	"names" => "--names",
	"nocones" => "--nocones",
	"noincidence" => "--noincidence",
	"pair" => "--pair",
	"pluckersymmetries" => "--pluckersymmetries",
	"polynomialset" => "--polynomialset_",
	"polynomialsetlist" => "--polynomialsetlist_",
	"restrict" => "--restrict",
	"scale" => "--scale",
	"shiftVariables" => "--shiftVariables",
	"star" => "--star",
	"symmetry" => "--symmetry",
	"symmetryExploit" => "--symmetryExploit",
	"symmetryPrinting" => "--symmetryPrinting",
	"symsigns" => "--symsigns",
	-- "subspace" => "--subspace", -- missing in v0.4
	"tplane" => "--tplane",
	"trees" => "--trees",
	"unimodular" => "--unimodular",
	"vectorinput" => "--vectorinput",
	"xml" => "--xml"
};


---------------------------------------------------------
-- cmdLineArgs
-- Describes which functions have command line arguments
-- that take values on the command line and not on stdin.
-- Used by gfanArgumentToString
---------------------------------------------------------
cmdLineArgs = hashTable { 
	"gfan_render" => { "shiftVariables" },
	"gfan_renderstaircase" => { "d", "w" },
	"gfan_fancommonrefinement" => {"i1", "i2"},
	"gfan_fanlink" => {"i"},
	"gfan_fanproduct" => {"i1", "i2"},
	"gfan_minors" => {"r", "d", "n"},
	"gfan_tropicallinearspace" => {"n", "d"}
}


--------------------------------------------------------
--------------------------------------------------------
-- GFAN HOOKS START HERE 
--------------------------------------------------------
--------------------------------------------------------


--------------------------------------------------------
-- gfan
--------------------------------------------------------

gfan = method( Options => {
	"g" => false, 
	"symmetry" => null, 
	"e" => false, 
	"disableSymmetryTest" => false
	}
)

gfan Ideal := opts -> (I) -> (
	if opts#"g" then error "Polynomials must be marked for the -g option";
	input := gfanRingToString(ring I) 
		| gfanIdealToString(I) 
		| gfanSymmetriesToString(opts#"symmetry");
	gfanParseLMPL runGfanCommand("gfan", opts, input)
)

gfan MarkedPolynomialList := opts -> (L) -> (
	input := gfanMPLToRingToString(L)
		| gfanMPLToString(L) 
		| gfanSymmetriesToString(opts#"symmetry");
	gfanParseLMPL runGfanCommand("gfan", opts, input)
)

gfan List := opts -> (L) -> (
	if opts#"g" then error "Polynomials must be marked for the -g option";
	input := gfanRingToString(ring first L)
		| gfanPolynomialListToString(L) 
		| gfanSymmetriesToString(opts#"symmetry");
	gfanParseLMPL runGfanCommand("gfan", opts, input)
)

--------------------------------------------------------
-- gfan_buchberger
--------------------------------------------------------

gfanBuchberger = method( Options => {
	"w"=>null, 
	"r"=>false, 
	"W"=>false, 
	"g"=>false
	}
)

gfanBuchberger List := opts -> (L) -> (
	input := gfanRingToString(ring first L) 
		| gfanPolynomialListToString(L) 
		| gfanIntegerListToString(opts#"w");
	gfanParseMPL runGfanCommand("gfan_buchberger", opts, input)
)

gfanBuchberger Ideal := opts -> (I) -> (
	gfanBuchberger(flatten entries gens I, opts)
)

gfanBuchberger MarkedPolynomialList := opts -> (L) -> (
	gfanBuchberger(last L, opts)
)

--------------------------------------------------------
-- gfan_doesidealcontain
--------------------------------------------------------

gfanDoesIdealContain = method(Options=>{})
gfanDoesIdealContain (MarkedPolynomialList, List) := opts -> (I,J) -> (
	input := gfanMPLToRingToString(I) 
		| gfanMPLToString(I) 
		| gfanPolynomialListToString(J);
	gfanParseBoolInteger runGfanCommand("gfan_doesidealcontain", opts, input)
)

--------------------------------------------------------
-- gfan_fancommonrefinement
--------------------------------------------------------

gfanFanCommonRefinement = method( Options => {
	"i1" => null, -- these are set inside the method
	"i2" => null, -- these are set inside the method
	}
)

gfanFanCommonRefinement (PolymakeObject, PolymakeObject) := opts -> (F,G) -> (
	fileA := gfanMakeTemporaryFile F#"rawstring";
	fileB := gfanMakeTemporaryFile G#"rawstring";
	opts = opts ++ { "i1" => fileA , "i2" => fileB };
	out := gfanParsePolyhedralFan runGfanCommand("gfan_fancommonrefinement", opts, "");
	gfanRemoveTemporaryFile fileA;
	gfanRemoveTemporaryFile fileB;
	out
)

--------------------------------------------------------
-- gfan_fanlink
--------------------------------------------------------

gfanFanLink = method( Options => {
	"i" => null,  -- this is set inside the method
	"symmetry" => null,
	"star" => false
	}
)

gfanFanLink (PolymakeObject, List) := opts -> (F,V) -> (
	fileName := gfanMakeTemporaryFile F#"rawstring";
	input := gfanIntegerListToString V;
	opts = opts ++ { "i" => fileName };
	out := gfanParsePolyhedralFan runGfanCommand("gfan_fanlink", opts, input);
	gfanRemoveTemporaryFile fileName;
	out
)

--------------------------------------------------------
-- gfan_fanproduct
--------------------------------------------------------

gfanFanProduct = method( Options => {
	"i1" => null, -- these are set inside the method
	"i2" => null, -- these are set inside the method
	}
)

	-- version 0.4
gfanFanProduct (PolymakeObject, PolymakeObject) := opts -> (F,G) -> (
	fileA := gfanMakeTemporaryFile F#"rawstring";
	fileB := gfanMakeTemporaryFile G#"rawstring";
	opts = opts ++ { "i1" => fileA , "i2" => fileB };
	out := gfanParsePolyhedralFan runGfanCommand("gfan_fanproduct", opts, "");
	gfanRemoveTemporaryFile fileA;
	gfanRemoveTemporaryFile fileB;
	out
)


--------------------------------------------------------
-- gfan_groebnercone
--------------------------------------------------------

gfanGroebnerCone = method( Options => {
	"restrict" => false,
	"pair" => false,
	"asfan" => false,
	"xml" => false,
	"vectorinput" => false
	}
)

gfanGroebnerCone (MarkedPolynomialList, MarkedPolynomialList) := opts -> (L,M) -> (
	if not opts#"pair" then (
		if gfanVerbose then 
			 << "Using --pair option for gfanGroebnerCone." << endl;
		opts = opts ++ {"pair" => true};
	);

	if gfanMPLToRingToString(L) != gfanMPLToRingToString(M) then (
		error("The arguments to gfanGroebnerCone should be defined over the same ring.");
	);

	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L) 
		| gfanMPLToString(M);
	gfanParsePolyhedralFan runGfanCommand("gfan_groebnercone", opts, input) 
)

gfanGroebnerCone MarkedPolynomialList := opts -> (L) -> (
	if opts#"pair" then
		error("The pair option for gfanGroebnerCone should be used along with " 
			| "two MarkedPolynomialLists as arguments.");
	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_groebnercone", opts, input)
)

--------------------------------------------------------
-- gfan_homogeneityspace
--------------------------------------------------------

gfanHomogeneitySpace = method(Options=>{})

gfanHomogeneitySpace (List) := opts -> (L) -> (
	input := gfanRingToString(ring first L) | gfanPolynomialListToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_homogeneityspace", opts, input) 
)

gfanHomogeneitySpace (MarkedPolynomialList) := opts -> (L) -> (
	gfanHomogeneitySpace(last L)
)

--------------------------------------------------------
-- gfan_homogenize
--------------------------------------------------------

gfanHomogenize = method( Options => {
	"i"=>false,
	"w"=>false
	}
)

gfanHomogenize (List, Symbol) := opts -> (L,X) -> (
	input := gfanRingToString(ring first L) 
		| gfanPolynomialListToString(L) 
		| gfanSymbolToString(X) 
		| gfanIntegerListToString(opts#"w");
	out := runGfanCommand("gfan_homogenize", opts, input);
	R := ring first L;
	S := (coefficientRing R)[gens R | {X}];
	gfanParseIdeal(out)
)

gfanHomogenize (MarkedPolynomialList, Symbol) := opts -> (L,X) -> (
	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L) 
		| gfanSymbolToString(X) 
		| gfanIntegerListToString(opts#"w");
	out := runGfanCommand("gfan_homogenize", opts, input);
	R := ring first first L;
	S := (coefficientRing R)[gens R | {X}];
	gfanParseMPL(out)
)


--------------------------------------------------------
-- gfan_initialforms
--------------------------------------------------------

--Dear Mike:
--If --ideal is used, does the output need to be marked? Note, it is a GB wrt W.
--Does --pair make sense without --ideal? Probably not.
--Does --pair and --ideal need to be marked? I would assume so.
--So, is no --pair and no --ideal the only case where the output is not marked?

--Hey! Version 0.4 clarifies this.

gfanInitialForms = method( Options => {
	"ideal" => false,
	"pair" => false,
	"mark" => false
	}
)

gfanInitialForms (List, List) := opts -> (L,W) -> (
	input := gfanRingToString(ring first L) 
		| gfanPolynomialListToString(L) 
		| gfanIntegerListToString(W);
	if opts#"pair" then
		gfanParseIdealPair runGfanCommand("gfan_initialforms", opts, input)
	else 
		gfanParseIdeal runGfanCommand("gfan_initialforms", opts, input)
)

gfanInitialForms (MarkedPolynomialList, List) := opts -> (L,W) -> (
	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L) 
		| gfanIntegerListToString(W);
	if opts#"pair" then
		gfanParseMPLPair runGfanCommand("gfan_initialforms", opts, input)
	else 
		gfanParseMPL runGfanCommand("gfan_initialforms", opts, input)
)

--------------------------------------------------------
-- gfan_interactive
--------------------------------------------------------

gfanInteractive = method( Options => {} )

gfanInteractive := opts -> () -> (
	error "Not implemented";
)

--------------------------------------------------------
-- gfan_ismarkedgroebnerbasis
--------------------------------------------------------

gfanIsMarkedGroebnerBasis = method( Options => {} )

gfanIsMarkedGroebnerBasis (MarkedPolynomialList) := opts -> (L) -> (
	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L);
	gfanParseBool runGfanCommand("gfan_ismarkedgroebnerbasis", opts, input)
)


--------------------------------------------------------
-- gfan_krulldimension
--------------------------------------------------------

gfanKrullDimension = method( Options => {} )

gfanKrullDimension (MarkedPolynomialList) := opts -> (L) -> (
	input := gfanMPLToRingToString(L) 
		| gfanMPLToString(L);
	gfanParseInteger runGfanCommand("gfan_krulldimension", opts, input)
)


--------------------------------------------------------
-- gfan_latticeideal
--------------------------------------------------------

gfanLatticeIdeal = method( Options => {
	"t" => false
	}
)

gfanLatticeIdeal (List) := opts -> (L) -> (
	input := gfanSymmetriesToString L;
	QQ[(getSymbol("x"))_0..(getSymbol("x"))_(#(first L)-1)];
	gfanParseIdeal replace("x", "x_", runGfanCommand("gfan_latticeideal", opts, input))
)


--------------------------------------------------------
-- gfan_leadingterms
--------------------------------------------------------

gfanLeadingTerms = method( Options => { 
	"m" => false 
	} 
)

gfanLeadingTerms (MarkedPolynomialList) := opts -> (L) -> (
	if opts#"m" then (
		error "gfanLeadingTerms: Expected a list of MarkedPolynomialLists with the -m option.";
	) else (
		input := gfanMPLToRingToString(L) | gfanMPLToString(L);
		return gfanParseIdeal runGfanCommand("gfan_leadingterms", opts, input);
	)
)

gfanLeadingTerms (List) := opts -> (L) -> (
	if opts#"m" then (
		input := gfanMPLToRingToString(first L) | gfanLMPLToString(L);
		return gfanParseIdeals runGfanCommand("gfan_leadingterms", opts, input);
	) else (
		error "gfanLeadingTerms: Expected a MarkedPolynomialList when -m is not used.";
	)
)


--------------------------------------------------------
-- gfan_markpolynomialset
--------------------------------------------------------

gfanMarkPolynomialSet = method( Options => {} )

gfanMarkPolynomialSet (List, List) := opts -> (L,W) -> (
	input := gfanRingToString(ring first L) 
		| gfanPolynomialListToString(L) 
		| gfanIntegerListToString(W);
	gfanParseMarkedIdeal runGfanCommand("gfan_markpolynomialset", opts, input)
)


--------------------------------------------------------
-- gfan_minkowskisum
--------------------------------------------------------

gfanMinkowskiSum = method( Options => {
	"symmetry" => null,
	"disableSymmetryTest" => false,
	"nocones" => false
	}
)

gfanMinkowskiSum (List) := opts -> (L) -> (
	input := gfanRingToString(ring first L)
		| gfanPolynomialListToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_minkowskisum", opts, input)
)

--------------------------------------------------------
-- gfan_minors
--------------------------------------------------------

gfanMinors = method( Options => {
	"r" => null, 
	"d" => null,
	"n" => null,
	"M2" => false,
	"names" => null,
	"dressian" => false,
	"pluckersymmetries" => false
	}
)

gfanMinors (ZZ,ZZ,ZZ) := opts -> (r,d,n) -> (
	input := "";
	opts = opts ++ { "r" => r, "d" => d, "n" => n};
	out := null;
	if opts#"dressian" then (
		out = runGfanCommand("gfan_minors", opts, input);
		QQ[apply(subsets(toList(0..n-1), d), ind -> (getSymbol("p"))_(concatenate(ind/toString)))];
		out = replace("p(.{"| d | "," | d | "})", "p_\"\\1\"", out);
		return gfanParseIdeal out;
	) else if opts#"pluckersymmetries" then (
		return value replace("\\}\n\\{", ",", runGfanCommand("gfan_minors", opts, input));
	) else (
		out = runGfanCommand("gfan_minors", opts, input);
		QQ[flatten apply(d, i -> apply(n, j ->  (getSymbol("m"))_(""|i|j)))];
		out = replace("m(..)", "m_\"\\1\"", out);
		return gfanParseIdeal out;
	)
)


--------------------------------------------------------
-- gfan_polynomialsetunion
--------------------------------------------------------

--Should this be marked?
gfanPolynomialSetUnion = method( Options => { 
	"s"=>false 
	}
)

gfanPolynomialSetUnion (MarkedPolynomialList,MarkedPolynomialList) := opts -> (L,K) -> (
	input := gfanMPLToRingToString(L) 
		| gfanLMPLToString({L,K});
	gfanParseMarkedIdeal runGfanCommand("gfan_polynomialsetunion", opts, input)
)


--------------------------------------------------------
-- gfan_render
--------------------------------------------------------

gfanRender = method( Options => {
	"L" => false,
	"shiftVariables" => 0,
	}
)

gfanRender (List) := opts -> (L) -> (
	fileName := temporaryFileName();
	gfanRender(fileName, List, opts);
)

gfanRender (String, List) := opts -> (fileName, L) -> (
	input := gfanMPLToRingToString(first L) | gfanLMPLToString(L);
	out := runGfanCommand("gfan_render", opts, input);

	figure := openOut(fileName | ".fig");
	figure << out << close;
	<< "Figure rendered to " << fileName << ".fig" << endl;
	if fig2devPath != "" then (
		run fig2devPath | "fig2dev -Lpng " | fileName  | ".fig " | fileName |".png";
		<< "Figure converted to png: " << fileName << ".png" << endl;
		show URL("file://" | fileName | ".png");
	) else (
		<< "fig2dev path not set." << endl ;
	)
)


--------------------------------------------------------
-- gfan_renderstaircase
--------------------------------------------------------

gfanRenderStaircase = method( Options=> {
	"m"=>false,
	"d"=>8,
	"w"=>5
	}
)

gfanRenderStaircase (List) := opts -> (L) -> (
	gfanRenderStaircase(temporaryFileName(), L, opts);
)

gfanRenderStaircase (String, List) := opts -> (fileName, L) -> (
	out := if opts#"m" then
		runGfanCommand("gfan_renderstaircase", opts,
			gfanMPLToRingToString(first L) | gfanLMPLToString(L) | "\n")
	else
		runGfanCommand("gfan_renderstaircase", opts, 
			gfanMPLToRingToString(L) | gfanMPLToString(L) | "\n");

	figure := openOut(fileName | ".fig");
	figure << out << close;
	<< "Figure rendered to " << fileName << ".fig" << endl;

	if fig2devPath != "" then (
		run fig2devPath | "fig2dev -Lpng " | fileName  | ".fig " | fileName |".png";
		<< "Figure converted to png: " << fileName << ".png" << endl;
		show URL("file://" | fileName | ".png");
	) else << "fig2dev path not set." << endl ;
)

--------------------------------------------------------
-- gfan_saturation
--------------------------------------------------------

gfanSaturation = method( Options => {
	"h" => false
	}
)

gfanSaturation (Ideal) := opts -> (I) -> (
	input := gfanRingToString(ring I) | gfanIdealToString(I);
	gfanParseIdeal runGfanCommand("gfan_saturation", opts, input)
)

--------------------------------------------------------
-- gfan_secondaryfan
--------------------------------------------------------

gfanSecondaryFan = method( Options => {
	"unimodular" => false,
	"scale" => null,
	"symmetry" => null
	}
)

gfanSecondaryFan (List) := opts -> (L) -> (
	--version 0.4
	input := gfanVectorConfigToString L;
	gfanParsePolyhedralFan runGfanCommand("gfan_secondaryfan", opts, input)
)

--------------------------------------------------------
-- gfan_stats
--------------------------------------------------------

gfanStats = method( Options => {} )

gfanStats (List) := opts -> (L) -> (
	input := gfanMPLToRingToString(first L) 
		| gfanLMPLToString(L);
	runGfanCommand("gfan_stats", opts, input) -- Parse this?
)

--------------------------------------------------------
-- gfan_substitute
--------------------------------------------------------

gfanSubstitute = method( Options => {} )

gfanSubstitute (MarkedPolynomialList, PolynomialRing) := opts -> (L,R) -> (
	input := gfanMPLToRingToString(L) | gfanMPLToString(L) | gfanRingToString(R);
	use R;
	gfanParseMarkedIdeal runGfanCommand("gfan_substitute", opts, input)
)


--------------------------------------------------------
-- gfan_tolatex
--------------------------------------------------------

gfanToLatex = method( Options => { 
	"h" => false,
	"polynomialset" => false,
	"polynomialsetlist" => false
	}
)

gfanToLatex (List) := opts -> (L) -> (
	if opts#?"polynomialset" and opts#"polynomialset" then (
		return runGfanCommand("gfan_tolatex", opts, gfanMPLToString(L));
	) else (
		if not (opts#?"polynomialsetlist" and opts#"polynomialsetlist") then 
			opts = opts ++ { "polynomialsetlist" => true };
		return runGfanCommand("gfan_tolatex", opts,  gfanLMPLToString(L));
	);
)

gfanToLatex (MarkedPolynomialList) := opts -> (L) -> (
	if not opts#"polynomialset" then 
		opts = opts ++ { "polynomialset" => true };
	return runGfanCommand("gfan_tolatex", opts,  gfanMPLToString(L));
)

--------------------------------------------------------
-- gfan_topolyhedralfan
--------------------------------------------------------

gfanToPolyhedralFan = method( Options => {
	"restrict" => false,
	"symmetry" => null
	}
)

gfanToPolyhedralFan List := opts -> (L) -> (
	input := gfanMPLToRingToString(first L) 
		| gfanSymmetriesToString(opts#"symmetry") 
		| gfanLMPLToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_topolyhedralfan", opts, input) 
)

--------------------------------------------------------
-- gfan_tropicalbasis
--------------------------------------------------------

gfanTropicalBasis = method( Options => {
	"h"=>false
	}
)

gfanTropicalBasis (Ideal) := opts -> (I) -> (
	input := gfanRingToString(ring I) 
		| gfanIdealToString(I);
	gfanParseIdeal runGfanCommand("gfan_tropicalbasis", opts, input)-- should this be marked? Probably not.
)


--------------------------------------------------------
-- gfan_tropicalbruteforce
--------------------------------------------------------

gfanTropicalBruteForce = method( Options => {} )

gfanTropicalBruteForce List := opts -> (L) -> (
	input := gfanMPLToRingToString(L) | gfanMPLToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_tropicalbruteforce", opts, input) 
)


--------------------------------------------------------
-- gfan_tropicalevaluation
--------------------------------------------------------

gfanTropicalEvaluation = method( Options => {} )

gfanTropicalEvaluation (RingElement, List) := opts -> (f,L) -> (
	--v0.4 
	input := gfanRingToString(ring f) | gfanPolynomialListToString({f}) | gfanSymmetriesToString(L);
	value runGfanCommand("gfan_tropicalevaluation", opts, input) 
	-- Make/find a parsing function for the above
)


--------------------------------------------------------
-- gfan_tropicalfunction
--------------------------------------------------------

gfanTropicalFunction = method( Options => {} )

gfanTropicalFunction RingElement := opts -> (f) -> (
	--v0.4 
	input := gfanRingToString(ring f) | gfanPolynomialListToString{f};
	gfanParsePolyhedralFan runGfanCommand("gfan_tropicalfunction", opts, input) 
)


--------------------------------------------------------
-- gfan_tropicalhypersurface
--------------------------------------------------------

gfanTropicalHyperSurface = method( Options => {} )

gfanTropicalHyperSurface RingElement := opts -> (f) -> (
	--v0.4 
	input := gfanRingToString(ring f) | gfanPolynomialListToString{f};
	gfanParsePolyhedralFan runGfanCommand("gfan_tropicalhypersurface", opts, input) 
)


--------------------------------------------------------
-- gfan_tropicalintersection
--------------------------------------------------------

gfanTropicalIntersection = method( Options => {
	"t" => false,
	"tplane" => false,
	"symmetryPrinting" => false,
	"symmetryExploit" => false,
	"restrict" => false
	}
)

gfanTropicalIntersection (List) := opts -> (L) -> (
	input := gfanRingToString(ring first L) | gfanPolynomialListToString(L);
	gfanParsePolyhedralFan runGfanCommand("gfan_tropicalintersection", opts, input)
)

--------------------------------------------------------
-- gfan_tropiciallifting
--------------------------------------------------------

gfanTropicalLifting = method( Options => {} )

gfanTropicalLifting := opts -> () -> (
	error "Not implemented";
)

--------------------------------------------------------
-- gfan_tropiciallinearspace
--------------------------------------------------------

gfanTropicalLinearSpace = method( Options => {
	"trees" => false,
	"n" => null;
	"d" => null;
	}
)

gfanTropicalLinearSpace (List, ZZ, ZZ) := opts -> (L, n, d) -> (
	--v0.4
	opts = opts ++ { "n" => n , "d" => d};
	input := (gfanIntegerListToString L) | "\n"; -- implicitly this accepts reals. It should be made explicit.
	R := QQ[getSymbol("t"), apply(n, i -> getSymbol("x"|i))];
	(out, err) := runGfanCommandCaptureBoth("gfan_tropicallinearspace", opts, input);
	(gfanParseIdeal out, err)
)


--------------------------------------------------------
-- gfan_tropicalmultiplicity
--------------------------------------------------------

gfanTropicalMultiplicity = method( Options => {} )

gfanTropicalMultiplicity (List) := opts -> (L) -> (
	input := gfanMPLToRingToString(L) | gfanMPLToString(L);
	gfanParseInteger runGfanCommand("gfan_tropicalmultiplicity", opts, input)
)

--------------------------------------------------------
-- gfan_tropicalrank
--------------------------------------------------------

gfanTropicalRank = method( Options => {
	"kapranov" => false
	}
)

gfanTropicalRank (Matrix) := opts -> (M) -> (
	--v0.4
	input := gfanMatrixToString M;
	(out, err) :=runGfanCommandCaptureBoth("gfan_tropicalrank", opts, input);
	(gfanParseInteger out, err)
)

--------------------------------------------------------
-- gfan_tropicalstartingcone
--------------------------------------------------------

gfanTropicalStartingCone = method( Options => {
	"g" => false, 
	"d" => false
	}
)

gfanTropicalStartingCone (List) := opts -> (L) -> (
	input := gfanRingToString(ring first L) | gfanPolynomialListToString(L);
	gfanParseMarkedIdealPair runGfanCommand("gfan_tropicalstartingcone", opts, input)
)


--------------------------------------------------------
-- gfan_tropicaltraverse
--------------------------------------------------------

gfanTropicalTraverse = method( Options => {
	"symmetry"=>null,
	"symsigns"=>false,
	"noincidence"=>false
	}
)

gfanTropicalTraverse (List) := opts -> (L) -> (
	input := gfanMPLToRingToString(first L) 
		| gfanMPLToString(first L) 
		| gfanMPLToString(last L)
		| gfanSymmetriesToString(opts#"symmetry");
	gfanParsePolyhedralFan runGfanCommand("gfan_tropicaltraverse", opts, input) 
)


--------------------------------------------------------
-- gfan_tropicalweildivisor
--------------------------------------------------------

gfanTropicalWeilDivisor = method( Options => {
	"i1" => null,  -- perhaps these should be removed
	"i2" => null
	}
)

gfanTropicalWeilDivisor (PolymakeFan, PolymakeFan) := opts -> (F,G) -> (
	--v0.4
	fileA := gfanMakeTemporaryFile F#"rawstring";
	fileB := gfanMakeTemporaryFile G#"rawstring";
	opts = opts ++ { "i1" => fileA , "i2" => fileB };
	out := gfanParsePolyhedralFan runGfanCommand("gfan_weildivisor", opts, "");
	gfanRemoveTemporaryFile fileA;
	gfanRemoveTemporaryFile fileB;
	out
)


--------------------------------------------------------
-- Documentation
--------------------------------------------------------

beginDocumentation()

gfanFunctions = hashTable {
	gfan => "gfan", 
	gfanBuchberger => "gfan_buchberger",
	gfanDoesIdealContain => "gfan_doesidealcontain",
	gfanFanCommonRefinement => "gfan_fancommonrefinement", -- v0.4
	gfanFanLink => "gfan_fanlink", -- v0.4
	gfanFanProduct => "gfan_fanproduct", -- v0.4
	gfanGroebnerCone => "gfan_groebnercone",
	gfanHomogeneitySpace => "gfan_homogeneityspace",
	gfanHomogenize => "gfan_homogenize",
	gfanInitialForms => "gfan_initialforms",
	gfanInteractive => "gfan_interactive",
	gfanIsMarkedGroebnerBasis => "gfan_ismarkedgroebnerbasis",
	gfanKrullDimension => "gfan_krulldimension",
	gfanLatticeIdeal => "gfan_latticeideal", -- v0.4
	gfanLeadingTerms => "gfan_leadingterms",
	gfanMarkPolynomialSet => "gfan_markpolynomialset",
	gfanMinkowskiSum => "gfan_minkowskisum", -- v0.4
	gfanMinors => "gfan_minors", -- v0.4
	gfanPolynomialSetUnion => "gfan_polynomialsetunion",
	gfanRender => "gfan_render", 
	gfanRenderStaircase => "gfan_renderstaircase", 
	gfanSaturation => "gfan_saturation",
	gfanSecondaryFan => "gfan_secondaryfan", -- v0.4
	gfanStats => "gfan_stats",
	gfanSubstitute => "gfan_substitute",
	gfanToLatex => "gfan_tolatex",
	gfanToPolyhedralFan => "gfan_topolyhedralfan",
	gfanTropicalBasis => "gfan_tropicalbasis",
	gfanTropicalBruteForce => "gfan_tropicalbruteforce",
	gfanTropicalEvaluation => "gfan_tropicalevaluation", -- v0.4
	gfanTropicalFunction => "gfan_tropicalfunction", -- v0.4
	gfanTropicalHyperSurface => "gfan_tropicalhypersurface", -- v0.4
	gfanTropicalIntersection => "gfan_tropicalintersection",
	gfanTropicalLifting => "gfan_tropicallifting",
	gfanTropicalLinearSpace => "gfan_tropicallinearspace", -- v0.4
	gfanTropicalMultiplicity => "gfan_tropicalmultiplicity",
	gfanTropicalRank => "gfan_tropicalrank", -- v0.4
	gfanTropicalStartingCone => "gfan_tropicalstartingcone",
	gfanTropicalTraverse => "gfan_tropicaltraverse",
	gfanTropicalWeilDivisor => "gfan_tropicalweildivisor" -- v0.4
}

--gfanHelp = hashTable apply(keys gfanFunctions, fn -> 
--	gfanFunctions#fn => apply( lines runGfanCommandCaptureError(gfanFunctions#fn, {"--help"}, {true}, "") , l->PARA {l}) 
--)
gfanHelp = (functionStr) -> 
	apply( lines runGfanCommandCaptureError(functionStr, hashTable {"help" => true}, "") , l->PARA {l}) 



doc ///
	Key
		"gfanInterface2"
	Headline
		a Macaulay2 interface to gfan
	Description
		Text
			@EM "gfanInterface2"@ is an interface to Anders Jenssen's {\tt gfan} package, which is a C++
			program to compute the Groebner fan (i.e. all the initial ideals) of an ideal.

			The main function in this package is @TO gfan@ which computes all of the Groebner 
			bases and initial ideals of a given ideal.  A useful feature of this function is 
			that it can handle symmetries in the ideal. If you want the geometric information 
			of this list of Groebner basis, see @TO gfanGroebnerCone@.

			Most of the functions in gfanInterface2 require 
			marked polynomial lists as input (see @TO MarkedPolynomialList@).
			In a marked polynomial list, the leading term of each polynomial is distinguished.

			New users should read the the guide @TO "Conventions for calling methods with options"@.
			Since {\tt gfan} is distributed with @EM "Macaulay2"@, one rarely needs to consult 
			the guide for @TO "Installation and Configuration of gfanInterface2"@.

			Most of functions in the gfan package are accessible through this interface.
			If you find that a method is missing or that an option does not perform as you expect
			please feel free to contact the package author. We are also interested to hear 
			concerns about the parameter and return types of each method. 
///

doc ///
	Key
		"Installation and Configuration of gfanInterface2"
	Description
		Text
			The {\tt gfanInterface2} package makes use of the binary executables from
			Anders Jenssen's {\tt gfan} software package. These binary files are distributed
			with @EM "Macaulay2"@ (since version 1.3) and so, it is not necessary to install {\tt gfan} 
			separately.

			The {\tt gfanInterface2} package contains the configuration option {\tt "path"} which 
			allows the user to specify which {\tt gfan} executables are used. When the path unspecified, 
			it defaults to an empty string and the binaries provided by Macaulay 2 are used.

			You can change the path, if needed, while loading the package:

		Example
			loadPackage("gfanInterface2", Configuration => { "path" => "/directory/to/gfan/"}, Reload => true)

		Text
			The path to the executables should end in a slash. 
			To set the path permanently, one needs to change 
			{\tt gfanInterface2.m2} either before installing or in the installed copy.
			You will find the path configuration near the top of the file.

			If {\tt gfanInterface2} is already installed and loaded, you can find the path
			of the source file by the following command:

		Example
			gfanInterface2#"source file"

		Text
			If you want to use {\tt gfan} executables outside of @EM "Macaulay2"@, they can be found with 
			{\tt currentLayout#"programs"}:

		Example
			prefixDirectory | currentLayout#"programs"

		Text
			If you would like to see the input and output files used to communicate with {\tt gfan}
			you can set the {\tt "keepfiles"} configuration option to {\tt true}. If {\tt "verbose"}
			is set to {\tt true}, {\tt gfanInterface2} will output the names of the temporary files used.

		Example
			loadPackage("gfanInterface2", Configuration => { "keepfiles" => true, "verbose" => true}, Reload => true);
			QQ[x,y];
			gfan ideal{x,y};

		Text
			Finally, if you want to be able to render Groebner fans and monomial staircases
			to {\tt .png} files, you should install {\tt fig2dev} and specify its path
			as follows:

		Example
			loadPackage("gfanInterface2", Configuration => { "fig2devpath" => "/directory/to/fig2dev/"}, Reload => true)

		Text
			Again, the path should end in a slash.
///


doc ///
	Key
		"Conventions for calling methods with options"
	Description
		Text
			In creating {\tt gfanInterface2}, the objective has been to mirror
			the {\tt gfan} commands as closely as possible in Macaulay 2. 
			Many commands in {\tt gfan} allow command line options and these
			are reproduced in {\tt gfanInterface2} as optional arguments. 

			For example, say we want to find the Groebner bases of 
			an ideal with symmetry. From the command line, one would
			type @TT "gfan --symmetry"@ and then give the ring, ideal and 
			symmetries of the ideal as input.

			In {\tt gfanInterface2} we pass the optional argument {\tt "symmetry"} the
			symmetries and provide the ideal as an argument.

		Example
			QQ[x,y,z]; 
			gfan(ideal(x^2*y -z, y^2*z - x, z^2*x - y), "symmetry" => {{0,1,2}, {1,2,0}})

		Text
			For each optional {\tt gfan} argument, the corresponding {\tt gfanInterface2}
			argument is obtained by simply removing the dashes.

			Here's another example. If we run {\tt gfanBuchberger} without a weight vector,
			it will use the lexicographic order.

		Example
			QQ[x,y,z];
			gfanBuchberger(ideal(x,y+z))

		Text
			If we want to use a different order, the {\tt gfan} documentation tells us to
			use the {\tt -w} argument. So, in Macaulay 2, we set the {\tt w} argument 
			to the desired weight vector.

		Example
			QQ[x,y,z];
			gfanBuchberger(ideal(x,y+z), "w" => {1,2,3})

		Text
			Many optional arguments to {\tt gfan} require no additional input. In this case,
			we set the optional argument in Macaulay 2 to be {\tt true}.

	SeeAlso
			MarkedPolynomialList
///

doc ///
	Key
		"MarkedPolynomialList"
	Description
		Text
			A marked polynomial list is a list of polynomials in which 
			the each polynomial has a distinguished term.

			In gfan, the leading terms of polynomials are marked by writing them first. 
			For example, the leading term of @TEX "$y^2 + x^2 + z^2$"@ is @TEX "$y^2$"@ as 
			it appears first. In Macaulay 2, polynomials are sorted based on the term 
			order of the ring and so distinguished terms are lost if they do not correspond 
			to the current ring's term order.

		Example
			QQ[x,y,z];
			y^2 + x^2 + z^2

		Text
			In {\tt gfanInterface2}, we represent marked Groebner bases using a list 
			of leading terms and a second list of polynomials. Such a pair of lists
			is made into a {\tt MarkedPolynomialList} by using the @TO markedPolynomialList@
			constructor.

		Example
			QQ[x,y,z];
			L = markedPolynomialList {{y^2, x^2}, {x^2 + y^2 + z^2, x^2 + y^2 + z^2}}
			first L
			last L

		Text
			Many methods in {\tt gfanInterface2} require {\tt MarkedPolynomialLists} as input
			and produce them as output.

			For example, the method @TO gfanMarkPolynomialSet@ takes a list of polynomials
			and a weight vector and returns a list of marked polynomials. 
			In this case, the leading term is first computed using 
			the weight vector and then lexicographic order to break ties.

		Example
			QQ[x,y,z];
			gfanMarkPolynomialSet({x*y^3+z^4, x^2*z^2 + y^3*z}, {-1,2,5})

	SeeAlso
		markedPolynomialList
///

doc ///
	Key
		markedPolynomialList
		(markedPolynomialList, List)
	Headline
		constructs a MarkedPolynomialList
	Usage
		L = markedPolynomialList P
	Inputs
		P:List
			of length two
	Outputs
		L:MarkedPolynomialList
			containg polynomials from the second entry of {\tt P} marked by the first entry of {\tt P}
	Description
		Text
			A marked polynomial list is a list of polynomials in which 
			the each polynomial has a distinguished term.

			The input to {\tt markedPolynomialList} should be a list containing two lists:
			a list of marked terms and a list of polynomials to be marked.

		Example
			QQ[x,y,z];
			polynomials = {x^2 + y^2 + z^2, y^2 + x^2 + z^2, y^2 + x^2 + z^2};
			markedTerms = {x^2, y^2, z^2};
			markedPolynomialList {markedTerms, polynomials}
	SeeAlso
		MarkedPolynomialList
///

doc ///
	Key
		"PolymakeObject"
	Description
		Text
			{\tt PolymakeObject} is the superclass of @TO "PolymakeFan"@ and @TO "PolymakeCone"@.
			It stores the basic information of polyhedral objects output by @EM "gfanInterface2"@.

			{\tt PolymakeObject}s store their own string representation ({\tt "rawstring"}), 
			along with parsed blocks ({\tt "rawblocks"}) and a separated header ({\tt "header"}).

			The keys on a {\tt PolymakeObject} that are in capital letters point to the actual polyheadral
			information.

		Example
			QQ[x,y];
			F = gfanToPolyhedralFan {markedPolynomialList {{x},{x+y}}}
			keys F
			F#"DIM"
			F#"header"
			F#"rawstring"

	SeeAlso
		PolymakeFan
		PolymakeCone
///

doc ///
	Key
		"PolymakeFan"
	Description
		Text
			A {\tt PolymakeFan} is a type of @TO "PolymakeObject"@ which stores various information
			about a polyhedral fan. A {\tt PolymakeFan} is structured as @TO "HashTable"@ with strings for
			keys that point to the stored information.

		Example
			QQ[x,y];
			F = gfanToPolyhedralFan {markedPolynomialList {{x},{x+y}}}
			keys F
			F#"DIM"
			F#"header"

		Text
			The keys in capital letters refer to polyhedral information, while those in lower case letters store
			parsing information.

	SeeAlso
		polymakeFanToFan
		PolymakeObject
		PolymakeCone
///

doc ///
	Key
		"PolymakeCone"
	Description
		Text
			A {\tt PolymakeFan} is a type of @TO "PolymakeObject"@ which stores various information
			about a polyhedral cone. A {\tt PolymakeFan} is structured as @TO "Hashtable"@ with strings for
			keys that point to the stored information.

		Example
			R = QQ[x,y,z,w]; 
			C = gfanGroebnerCone markedPolynomialList {{x*y*z}, { x*y*z + z*w^2*x + y^2*w*x}}
			keys C
			C#"DIM"
			C#"header"

		Text
			The keys in capital letters refer to polyhedral information, while those in lower case letters store
			parsing information.

	SeeAlso
		polymakeConeToCone
		PolymakeObject
		PolymakeFan
///

doc ///
	Key
		polymakeConeToCone
		(polymakeConeToCone, PolymakeCone)
	Headline
		converts a PolymakeCone into a Cone from the Polyhedra package
	Usage
		G = polymakeConeToCone F
	Inputs
		F:PolymakeCone
	Outputs 
		G:Cone
	Description
		Text
			This method converts a @TO PolymakeCone@, as output by gfan, into a @TO Cone@ from the
			@TO Polyhedra@ package.

		Example
			R = QQ[x,y,z,w]; 
			C = gfanGroebnerCone markedPolynomialList {{x*y*z}, { x*y*z + z*w^2*x + y^2*w*x}}
			G = polymakeConeToCone C
			rays G
			linSpace G

	SeeAlso
		polymakeFanToFan
		PolymakeFan
		PolymakeCone
///

doc ///
	Key
		polymakeFanToFan
		(polymakeFanToFan, PolymakeFan)
	Headline
		converts a PolymakeFan into a Fan from the Polyhedra package
	Usage
		G = polymakeFanToFan F
	Inputs
		F:PolymakeFan
	Outputs 
		G:Fan
	Description
		Text
			This method converts a @TO PolymakeFan@, as output by gfan, into a @TO Fan@ from the
			@TO Polyhedra@ package.

		Example
			R = QQ[x,y,z,w]; 
			F = gfanToPolyhedralFan gfan { x*y -z,  z*w - x}
			G = polymakeFanToFan F
			rays G
			linSpace G

	SeeAlso
		polymakeConeToCone
		PolymakeFan
		PolymakeCone
///

doc ///
	Key
		gfan
		(gfan, Ideal)
		(gfan, List)
		(gfan, MarkedPolynomialList)
	Headline
		all reduced Groebner bases of a polynomial ideal
	Usage
		G = gfan(I)
		G = gfan(L)
		G = gfan(M)
	Inputs
		I:Ideal
			contained in a polynomial ring
		L:List
			of polynomials
		M:MarkedPolynomialList
	Outputs 
		G:List
			of @TO2 {"MarkedPolynomialList", "marked polynomial lists"}@ that are reduced Groebner bases of {\tt I}, {\tt L}, or {\tt M}
	Description
		Text
			This method produces all reduced Groebner bases of a polynomial ideal. 
			The ideal can be given as an {\tt Ideal}, {\tt List} of polynomials, or
			a {\tt MarkedPolynomialList}. 
			The {\tt "g"=> true} option can be used to inform {\tt gfan} that the input
			is already a Groebner basis with respect to some monomial order. 
			However, in this case, the input must be a {\tt MarkedPolynomialList}.

		Example
			R = QQ[x,y,z]; 
			gfan(ideal(x^2*y -y^2, y^2*x - x^2))
			gfan({x^2*y -y^2, y^2*x - x^2}, "symmetry" => {{0,1,2}, {1,0,2}})
			gfan(markedPolynomialList {{y^5, x*y^2, x^2},{y^5-y^2,x*y^2 - y^4, x^2 -y^4}}, "g" => true)

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan"@
///

doc ///
	Key
		gfanBuchberger
		(gfanBuchberger, Ideal)
		(gfanBuchberger, List)
		(gfanBuchberger, MarkedPolynomialList)
	Headline
		reduced Groebner basis with respect to some monomial order
	Usage
		G = gfanBuchberger(I)
		G = gfanBuchberger(L)
		G = gfanBuchberger(M)
	Inputs
		I:Ideal
			contained in a polynomial ring
		L:List
			of polynomials
		M:MarkedPolynomialList
			
	Outputs
		G:MarkedPolynomialList
			a marked reduced Groebner basis of {\tt I}
	Description
		Text
			This method computes a reduced Groebner basis of an ideal 
			with respect to the lexicographic order (by default) or with 
			respect to some weight vector if option {\tt w} is specified. The output
			is a {\tt MarkedPolynomialList}.
			The input can be given as an {\tt Ideal}, {\tt List} of polynomials, or 
			{\tt MarkedPolynomialList}. In the case of a {\tt MarkedPolynomialList},
			the marked terms are ignored.

		Example
			QQ[x,y,z];
			I = ideal(x*y + z, x*z + y);
			gfanBuchberger(I)
			gfanBuchberger(I, "w" => {1,2,3})
			gfanBuchberger({x*y + z, x*z +y}, "w" => {1,2,3})

		Text
			
			Note that Macaulay 2 can compute Groebner bases with respect to given
			weights without using gfan. 

		Example
			QQ[x,y,z, MonomialOrder => { Weights => {1,2,3}, Lex } ];
			G = gens gb ideal(x*y + z,  x*z + y )
			markedPolynomialList transpose  apply(flatten entries G, g-> {leadTerm g, g})

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_buchberger"@
///

doc ///
	Key
		gfanDoesIdealContain
		(gfanDoesIdealContain, MarkedPolynomialList, List)
	Headline
		check ideal membership by the division algorithm
	Usage
		B = gfanDoesIdealContain(L,K)
	Inputs
		L:MarkedPolynomialList
			a marked Groebner basis.
		K:List
			a list of polynomials
	Outputs
		B:Boolean
			true if every polynomial in {\tt K} belongs to the ideal generated by {\tt L}
	Description
		Text
			This method determines if a list of polynomialsis contained in an ideal.
			Macaulay 2 provides this functionality in the @TO isSubset@ method.

		Example
			QQ[x,y,z];
			gfanDoesIdealContain(gfanBuchberger({x*y - y, x*z + z}), {y*z})
			isSubset(ideal(y*z), ideal(x*y - y, x*z +z))

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_doesidealcontain"@
///

doc ///
	Key
		gfanFanCommonRefinement
		(gfanFanCommonRefinement, PolymakeObject, PolymakeObject)
	Headline
		find the common refinement of two polyheadral fans
	Usage
		P = gfanFanCommonRefinement(F,G)
	Inputs
		F:PolymakeObject
		G:PolymakeObject
	Outputs
		P:PolymakeObject
			the common refinement of {\tt F} and {\tt G}
	Description
		Text
			This method takes two PolymakeObjects and finds their common refinement.

			In the following, {\tt F} is the fan with two cones partitions the plane along the line
			@TEX "$y=x$"@ while {\tt G} has two cones that parition the plane along @TEX "$y = x/2$"@.
			The common refinement of these two fans is the fan of the four cones between these two lines.
		Example
			QQ[x,y];
			F = gfanToPolyhedralFan gfan {x+y}
			G = gfanToPolyhedralFan gfan {x+y^2}
			gfanFanCommonRefinement(F,G)
		Text

			In the next example we take two half planes which overlap in the first
			quadrant. Their common refinement is simply their intersection.

		Example
			QQ[x,y];
			F = gfanToPolyhedralFan {markedPolynomialList{{x}, {x+y}}}
			G = gfanToPolyhedralFan {markedPolynomialList{{y^2}, {x+y^2}}}
			gfanFanCommonRefinement(F,G)
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_fancommonrefinement"@
///

doc ///
	Key
		gfanFanLink
		(gfanFanLink, PolymakeObject, List)
	Headline
		the link of a vertex in a polyhedral fan
	Usage
		P = gfanFanLink(F, V)
	Inputs
		F:PolymakeObject
			a polyhedral fan
		V:List
			a vertex of the fan
	Outputs
		P:PolymakeObject
			the link of {\tt F} at {\tt V}
	Description
		Text
			This method computes the link of a polyhedral fan around a vertex.

		Example
			QQ[x,y];
			F = gfanToPolyhedralFan {markedPolynomialList{{x}, {x+y}}};
			G = gfanToPolyhedralFan {markedPolynomialList{{y^2}, {x+y^2}}};
			Q = gfanFanCommonRefinement(F,G)
			gfanFanLink(Q, {2,1}, "star" =>true)

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_fanlink"@
///

doc ///
	Key
		gfanFanProduct
		(gfanFanProduct, PolymakeObject, PolymakeObject)
	Headline
		computes the product of polyhedral fans
	Usage
		P = gfanFanProduct(F,G)
	Inputs
		F:PolymakeObject
			a polyhedral fan
		G:PolymakeObject
			a polyhedral fan
	Outputs
		P:PolymakeObject
			the product of {\tt F} and {\tt G}
	Description
		Text
			This method computes the product of two polyhedral fans. 
			The arguments {\tt i1} and {\tt i2} are automatically set.

		Example
			QQ[x,y];
			F = gfanToPolyhedralFan {markedPolynomialList{{x}, {x+y}}}
			G = gfanToPolyhedralFan {markedPolynomialList{{y^2}, {x+y^2}}}
			gfanFanProduct(F,G)

		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_fanproduct"@
///

doc ///
	Key
		gfanGroebnerCone
		(gfanGroebnerCone, MarkedPolynomialList)
		(gfanGroebnerCone, MarkedPolynomialList, MarkedPolynomialList)
	Headline
		polyhedral information about a Groebner cone
	Usage
		S = gfanGroebnerCone(L)
		S = gfanGroebnerCone(L, M)
	Inputs
		L:MarkedPolynomialList
			a marked reduced Groebner basis, or a minimal basis.
		M:MarkedPolynomialList
			a marked reduced Groebner basis.
	Outputs
		S:String
			a description of the Groebner cone of {\tt L}
	Description
		Text
			This method computes the Grobener cone of {\tt L} in the case where {\tt L} is
			a marked reduced Groebner basis. If {\tt L} is only a marked minimal basis, then
			a smaller cone is produced.

		Example
			QQ[x,y];
			gfanGroebnerCone( markedPolynomialList {{x}, {x+y}} )  

		Text
			
			In the above example any weights {\em w = a(1,1) + p (1,-1)} for a 
			a real number and {\em p >= 0} give {\em (x)} as the initial ideal 
			of {\em (x+y)} with respect to {\em w}.
			
			When both {\tt L} and {\tt M} are given as input and are compatible marked 
			reduced Groebner bases in the sense that {\tt L} is an initial ideal of {\tt M} 
			then {\tt gfaGroebnerCone(L,M)} computes the cone of {\tt L} in the fan of {\tt M}.
			For example, the cone on which {\em (x+y)} is its own initial ideal is simply the line 
			{\em w = a(1,1)} for {\em a} a real number.

		Example 
			QQ[x,y];
			gfanGroebnerCone( markedPolynomialList {{x}, {x+y}}, markedPolynomialList {{x}, {x+y}} )  
		Text
			
			Note that the {\tt pair} option will automatically be specified when 
			two marked Groebner bases are given.
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_groebnercone"@
///

doc ///
	Key
		gfanHomogeneitySpace
		(gfanHomogeneitySpace, List)
		(gfanHomogeneitySpace, MarkedPolynomialList)
	Headline
		homogeneity space of a list of polynomials
	Usage
		gfanHomogeneitySpace(L)
		gfanHomogeneitySpace(M)
	Inputs
		L:List
			of polynomials
		M:MarkedPolynomialList
	Outputs
		S:String
			polymake data with a lineality space of all weight vectors for which {\tt L} is homogeneous.
	Description
		Text
			This method computes the homogeneity space of {\tt L} or {\tt M}. 
			If a {\tt MarkedPolynomialList} is used, then the marked terms are simply ignored.

		Example
			QQ[x,y,z];
			gfanHomogeneitySpace {x+y^2, y+z^2}

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_homogeneityspace"@
///

doc ///
	Key
		gfanHomogenize
		(gfanHomogenize, List, Symbol)
		(gfanHomogenize, MarkedPolynomialList, Symbol)
	Headline
		homogenize a list of polynomials with respect to a weight vector
	Usage
		G = gfanHomogenize(L,X)
		H = gfanHomogenize(M,X)
	Inputs
		L:List
			of polynomials
		M:MarkedPolynomialList
		X:Symbol
			the homogenizing variable
	Outputs
		G:List
			polynomials from {\tt L} homogenized with variable {\tt X}
		H:MarkedPolynomialList
			polynomials from {\tt M} homogenized with variable {\tt X}
	Description
		Text
			The method homogenizes the polynomials in {\tt L} or {\tt M} with respect to 
			a given weight vector provided by the optional argument {\tt w}. 
			If the {\tt w} option is not specified, the polynomials are
			homogenized with respect to total degree.
			This functionality is also provided by the 
			@TO homogenize@ method which does not use {\tt gfan}.

		Example
			QQ[x,y];
			L = {x+y, x^2*y + x};
			gfanHomogenize(L, symbol z, "w" => {2,3})
			QQ[x,y,z];
			L = {x+y, x^2*y + x}; 
			homogenize(matrix{L}, z, {2,3,1})

		Text
			Using the variant that accepts a {\tt MarkedPolynomialList} as input produces
			a {\tt MarkedPolynomialList} as output.

		Example
			QQ[x,y];
			L = markedPolynomialList {{y}, {x+y}};
			gfanHomogenize(L, symbol z,  "w" => {2,3})

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_homogenize"@
///

doc ///
	Key
		gfanInitialForms
		(gfanInitialForms, List, List)
		(gfanInitialForms, MarkedPolynomialList, List)
	Headline
		initial forms of polynomials with respect to a weight vector
	Usage
		G = gfanInitialForms(L,W)
		H = gfanInitialForms(M,W)
	Inputs
		L:List
			of polynomials
		M:MarkedPolynomialList
		W:List
			a weight vector
	Outputs
		G:List
			initial forms of the polynomials in {\tt L} with respect to weight {\tt W}
		H:MarkedPolynomialList
			marked initial forms of the polynomials in {\tt L} with respect to weight {\tt W}
	Description
		Text
			This method takes the initial forms of a list of polynomials. 
			If the {\tt "ideals"} option is used, generators for the initial ideal are given.
			If the {\tt "pair"} option is used, then the output is a pair of MarkedPolynomialLists.

		Example
			QQ[x,y,z]
			L = {x + y, x + z}
			gfanInitialForms(L, {1,2,1})
			gfanInitialForms(L, {1,2,1}, "ideal"=>true, "pair"=>true)
			gfanInitialForms({x*y+z, x*z + y}, {1,1,1}, "ideal"=>true)

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_initialforms"@
///

doc ///
	Key
		gfanInteractive
	Headline
		not implemented
	Description
		Text
			This method is not implemented.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_interactive"@
///

doc ///
	Key
		gfanIsMarkedGroebnerBasis
		(gfanIsMarkedGroebnerBasis, MarkedPolynomialList)
	Headline
		check if a list of marked polynomials are a Groebner basis
	Usage
		B = gfanIsMarkedGroebnerBasis(L)
	Inputs
		L:MarkedPolynomialList
	Outputs
		B:Boolean
			true if {\tt L} forms a Groebner basis
	Description
		Text
			This method takes a marked polynomial list and determines if
			it is a Groebner basis with respect to some weight vector.

		Example
			QQ[x,y,z];
			gfanIsMarkedGroebnerBasis markedPolynomialList {{x^2,y^3}, {x^2+y, y^3+z}}
			gfanIsMarkedGroebnerBasis markedPolynomialList {{y,y^3}, {x^2+y, y^3+z}}
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_ismarkedgroebnerbasis"@
///

doc ///
	Key
		gfanKrullDimension
		(gfanKrullDimension, MarkedPolynomialList)
	Headline
		krull dimension
	Usage
		D = gfanKrullDimension(L)
	Inputs
		L:MarkedPolynomialList
			a @TO2 {"MarkedPolynomialList", "marked Groebner basis"}@
	Outputs
		D:ZZ
			the Krull dimension of the polynomial ring modulo the ideal generated by {\tt L}
	Description
		Text
			This method returns the Krull dimension of the quotient of the 
			polynomial ring by the ideal generated by {\tt L}.

			Note that Macaulay 2 already provides this functionality (see @TO dim@).

		Example
			QQ[x,y,z,u,v];
			L = {x^3, y^2};
			gfanKrullDimension gfanBuchberger L
			dim ideal L
		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_krulldimension"@
///

doc ///
	Key
		gfanLatticeIdeal
		(gfanLatticeIdeal, List)
	Headline
		computes the lattice ideal of a lattice
	Usage
		I = gfanLatticeIdeal L
	Inputs
		L:List
			of generators of the lattice
	Outputs
		I:List
			a list of generators for the lattice ideal
	Description
		Text
			This method computes the generators for the lattice ideal. The input
			should be a list of points that generate the lattice.

		Example
			gfanLatticeIdeal {{2,-1,0},{3,0,-1}}
		Text
			The lattice ideal of a free abelian subgroup $L$ of $\mathbb Z^n$ is the ideal generated by
			$ \mathbf{x}^{\alpha^+} - \mathbf{x}^{\alpha^-}$ for $\alpha =\alpha^+ - \alpha^- \in L$.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_latticeideal"@
///

doc ///
	Key
		gfanLeadingTerms
		(gfanLeadingTerms, List)
		(gfanLeadingTerms, MarkedPolynomialList)
	Headline
		leading terms of a list (or list of lists) of marked polynomials
	Usage
		T = gfanLeadingTerms(L)
		T = gfanLeadingTerms(M)
	Inputs
		L:MarkedPolynomialList
		M:List
			of MarkedPolynomialLists
	Outputs
		T:List
			the leading terms of {\tt L} (or lists of the leading terms of each list in {\tt M})
	Description
		Text
			This method produces a list of the marked terms in a marked polynomial list. If
			the {\tt m} option is used it produces a list of the leading terms for a list of 
			marked polynomial lists.

			This functionality is already provided in Macaulay 2 by the {\tt first} function.

		Example
			QQ[x,y,z];
			L = gfanMarkPolynomialSet({x*y^3+z^4, x^2*z^2 + y^3*z}, {-1,2,5})
			gfanLeadingTerms L
			first L
			M = gfanMarkPolynomialSet({x^2*y+y*z^2, x*z^2 + x*y*z}, {-1,2,5})
			gfanLeadingTerms({M,L}, "m" => true)
			{M,L} / first
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_leadingterms"@
///

doc ///
	Key
		gfanMarkPolynomialSet
		(gfanMarkPolynomialSet, List, List)
	Headline
		mark the initial terms of a list of polynomials with respect to a weight vector
	Usage
		M = gfanMarkPolynomialSet(L,W)
	Inputs
		L:List
			of polynomials
		W:List
			a weight vector
	Outputs
		M:MarkedPolynomialList
			the polynomials in {\tt L} @TO2 {"MarkedPolynomialList", "marked"}@ with respect to {\tt W}
	Description
		Text
			This method marks the leading terms a given polynomial list. 
			The leading term of a polynomial is the term whose exponent vector
			has the largest dot product with {\tt W}.

		Example
			QQ[x,y,z];
			gfanMarkPolynomialSet({x + y + z, x^10 + y^4 + z^2, x^2*z + y^2}, {1, 3, 5})
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_markpolynomialset"@
///

doc ///
	Key
		gfanMinkowskiSum
		(gfanMinkowskiSum, List)
	Headline
		the Minkowski sum of Newton polytopes
	Usage
		P = gfanMinkowskiSum L
	Inputs
		L:List
			of polynomials
	Outputs
		P:PolymakeObject
			the Minkowski sum of the newton polytopes of the polynomials in {\tt L}
	Description
		Text
			The Newton polytope of a polynomial is the convex hull of the exponent vectors
			of the terms. This method produces a polymake object that describes the Minkowski
			sum of these polytopes.

		Example
			QQ[x,y]
			gfanMinkowskiSum { x + y + x*y }
			gfanMinkowskiSum { x + y + x*y + 1}
			gfanMinkowskiSum { x + y + x*y, x + y + x*y + 1}

		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_minkowskisum"@
///

doc ///
	Key
		gfanMinors
		(gfanMinors, ZZ, ZZ, ZZ)
	Headline
		minors of a matrix of indeterminates
	Usage
		L = gfanMinors(r,d,n)
	Inputs
		r:ZZ
			size of the minor
		d:ZZ
			number of rows
		n:ZZ
			number of columns
	Outputs
		L:List
			a list of the {\tt r}x{\tt r} minors of a {\tt d}x{\tt n} matrix of indeterminates
	Description
		Text
			The method produces the {\tt r}x{\tt r} minors of a {\tt d}x{\tt n} matrix of indeterminates. Note that the variables in the output are indexed by strings.

		Example
			gfanMinors(2,3,3)
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_minors"@
///

doc ///
	Key
		gfanPolynomialSetUnion
		(gfanPolynomialSetUnion, MarkedPolynomialList, MarkedPolynomialList)
	Headline
		union of two lists of marked polynomials
	Usage
		U = gfanPolynomialSetUnion(L,K)
	Inputs
		L:MarkedPolynomialList
			
		K:MarkedPolynomialList
			
	Outputs
		U:MarkedPolynomialList
			the union of lists {\tt L} and {\tt K} 
	Description
		Text
			This method produces the union of two lists of marked polynomials.
			For this method the marked term of the polynomial is not considered.
			That is to say, the union is taken as if the polynomials were not marked.
			The resulting polynomials in the output are marked with with preference
			given to the marked terms in the first argument.

		Example
			QQ[x,y,z];
			f = x + y + z;
			g = x + y;
			h = y + z;
			L = markedPolynomialList {{z, y}, {f,g}}
			M = markedPolynomialList {{x, y} , {f,h}}
			gfanPolynomialSetUnion(L,M)

		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_polynomialsetunion"@
///

doc ///
	Key
		gfanRender
		(gfanRender, List)
		(gfanRender, String, List)
	Headline
		render an image of a Grobener fan
	Usage
		gfanRender(L)
	Inputs
		fileName:String
			the name of the file to be output, given without an extension
		L:List
			all @TO2 {"MarkedPolynomialList", "marked reduced Groebner bases"}@ of {\tt I} or an ideal 
	Description
		Text
			This method renders the Groebner fan of an ideal and writes it to a {\tt .fig} file.
			If {\tt fig2dev} is installed then the {\tt .fig} file will be converted to {\tt .png}
			and displayed. The names of the {\tt .fig} and {\tt .png} files are printed on 
			standard out.

			This method may support more options in the future to control rendering, conversion,
			and display. It may also eventually output file names in a list.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_render"@
///

doc ///
	Key
		gfanRenderStaircase
		(gfanRenderStaircase, List)
		(gfanRenderStaircase, String, List)
	Headline
		render the staircase of a monomial initial ideal
	Usage
		gfanRenderStaircase(L)
		gfanRenderStaircase(fileName, L)
	Inputs
		fileName:String
			the name of the file to be output, given without an extension
		L:List
			a @TO2 {"MarkedPolynomialList", "marked Groebner basis"}@ 
			or lists of @TO2 {"MarkedPolynomialList", "marked Groebner bases"}@ 
			(for use with the {\tt m} option)
	Description
		Text
			This method renders the staircase of the monomial initial ideal of the given
			Groebner basis (or bases in the case of the {\tt m} option).
			The rendered image is written to a {\tt .fig} file.
			If {\tt fig2dev} is installed then the {\tt .fig} file will be converted to {\tt .png}
			and displayed. The names of the {\tt .fig} and {\tt .png} files are printed on 
			standard out.

			This method may support more options in the future to control rendering, conversion,
			and display. It may also eventually output file names in a list.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_renderstaircase"@
///

doc ///
	Key
		gfanSaturation
		(gfanSaturation, Ideal)
	Headline
		saturation of an ideal
	Usage
		gfanSaturation(I)
	Inputs
		I:Ideal
	Outputs
		L:List
			polynomials generating the saturation of {\tt I} with the product of the 
			variables of the ring of {\tt I}
	Description
		Text
			This method computes the saturation of an ideal with respect to the product of the generators of
			the ideal's ring.
		Example
			QQ[x,y,z];
			I = ideal(y*z*(x-1), x*(z^2 - y));
			gfanSaturation I
		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_saturation"@
///

doc ///
	Key
		gfanSecondaryFan
		(gfanSecondaryFan, List)
	Headline
		computes the secondary fan of a vector configuration
	Usage
		F = gfanSecondaryFan L
	Inputs
		L:List
			of integer vectors
	Outputs
		F:PolymakeFan
			the secondary fan of {\tt L}
	Description
		Text
			This method computes the secondary fan of a list of vectors.
		Example
			gfanSecondaryFan {{1,0},{1,1}, {1,2}, {1,2}}
		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_secondaryfan"@
///

doc ///
	Key
		gfanStats
		(gfanStats, List)
	Headline
		display certain properties of a list of polynomials
	Usage
		gfanStats(L)
	Inputs
		L:List
			containing lists of @TO2 {"MarkedPolynomialList", "marked Groebner bases"}@
	Outputs
		S:String
			describing the bases in {\tt L}
	Description
		Text
			This method outputs various information on a list of Groebner bases. The results are not parsed.

		Example
			QQ[x,y,z];
			L = gfan {x*y + z}
			gfanStats L

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_stats"@
///

doc ///
	Key
		gfanSubstitute
		(gfanSubstitute, MarkedPolynomialList, PolynomialRing)
	Headline
		rename the variables of a list of polynomials
	Usage
		gfanSubstitute(L,R)
	Inputs
		L:MarkedPolynomialList
			of polynomials
		R:PolynomialRing
			with the name number of variables as the ring of the polynomials in {\tt L}
	Outputs
		L:List
			of polynomials from {\tt L} with variables replaced by those in {\tt R}
	Description
		Text
			This method replaces each variable in a marked polynomial list with variables from 
			a different ring.
		Example
			R = QQ[z,a,b];
			S = QQ[x,y,z];
			L = markedPolynomialList {{x*y, z^2} , {x*y+ z^2, x*y + z^2}}
			gfanSubstitute(L, R)

		Text
			Caution should be used as this method invokes {\tt use R} which changes the global
			symbol table. It would be preferrable to use the map command which is built into
			Macaulay 2. A ring map can be applied directly to a marked polynomial list.

		Example
			f = map(R,S, {z,a,b})
			f L

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_substitute"@
///

doc ///
	Key
		gfanToLatex
		(gfanToLatex, List)
		(gfanToLatex, MarkedPolynomialList)
	Headline
		convert a list of polynomials to LaTeX
	Usage
		gfanToLatex(L)
		gfanToLatex(M)
	Inputs
		L:List
			of marked polynomial lists or a marked polynomial list (for the {\tt polynomialset} option)
		M:MarkedPolynomialList 
	Outputs
		S:String
			LaTeX markup for {\tt L}
	Description
		Text
			This method converts marked polynomial lists and lists of marked polynomial lists to latex. If the given input is a list, the option {\tt polynomialsetlist} is assumed. Similarly, if the input is a marked polynomial list then {\tt polynomialset} is assumed.
		Example
			QQ[x,y,z];
			L = gfan{x^2 + y*z, z^2 + y*z}
			gfanToLatex L
			gfanToLatex first L
			gfanToLatex({{x,z}, {x+y, x+z}}, "polynomialset" => true)
		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tolatex"@
///

doc ///
	Key
		gfanToPolyhedralFan
		(gfanToPolyhedralFan, List)
	Headline
		polyhedral data about the fan of a list of Groebner bases
	Usage
		gfanToPolyhedralFan(L)
	Inputs
		L:List
			containing @TO2 {"MarkedPolynomialList", "marked reduced Groebner bases"}@
	Outputs
		P:PolymakeFan
			the fan of the Groebner bases in {\tt L}
	Description
		Text
			This method takes a list of 
			@TO2 {"MarkedPolynomialList", "marked reduced Groebner bases"}@
			and outputs a polyhedral fan whose faces correspond to the marked Groebner bases.
			
			For example, @TEX "$x + y$"@ is a marked Groebner basis with initial term @TEX "$x$"@
			for any weight vector @TEX "$(a,b)$"@ with @TEX "$a < b$"@. 
		Example
			QQ[x,y]
			M = markedPolynomialList {{x},{x+y}}
			F = gfanToPolyhedralFan { M }
		Text
			The single facet above is @TEX "$\\mathbb R_{\\geq 0} (1,-1) + \\mathbb R (1,1)$"@
			from reading off the ray and the lineality space. This corresponds to 
			@TEX "$\\{(a,b) \\mid a < b\\}$"@. 

			Adding in the Groebner basis with @TEX "$y$"@ as the initial term gives a second facet.

		Example
			L = markedPolynomialList {{y},{x+y}}
			F = gfanToPolyhedralFan { M, L }
		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_topolyhedralfan"@
///

doc ///
	Key
		gfanTropicalBasis
		(gfanTropicalBasis, Ideal)
	Headline
		tropical basis of an ideal
	Usage
		gfanTropicalBasis(I)
	Inputs
		I:Ideal
	Outputs
		L:List
			of polynomials that give a tropical basis of {\tt I}
	Description
		Text
			This method produces a tropical basis of a given homogeneous ideal. If the ideal is not homogeneous, it must be homogenized using the {\tt h} option.

		Example
			QQ[x,y];
			gfanTropicalBasis ideal {x^2+y^2, x^2-x*y}

		Text
			
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalbasis"@
///

doc ///
	Key
		gfanTropicalBruteForce
		(gfanTropicalBruteForce, List)
	Headline
		computes the tropical variety of an ideal
	Usage
		gfanTropicalBruteForce(L)
	Inputs
		L:MarkedPolynomialList
			a marked reduced Groebner basis for a homogeneous ideal
	Outputs
		P:PolymakeFan
			describing the tropical variety of the ideal of {\tt L}
	Description
		Text
			This method computes the tropical variety of a marked reduced Groebner basis (given in the form of a marked polynomial list).

			The following example is taken from the gfan documentation (v0.4 p.20).

		Example
			QQ[a,b,c,d,e,f,g,h,i,j]
			gfanTropicalBruteForce gfanBuchberger ideal "bf-ah-ce, bg-ai-de, cg-aj-df, ci-bj-dh, fi-ej-gh"

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalbruteforce"@
///

doc ///
	Key
		gfanTropicalEvaluation
		(gfanTropicalEvaluation, RingElement, List)
	Headline
		evaluates a tropical polynomial function
	Usage
		Y = gfanTropical(f, L)
	Inputs
		f:RingElement
			a polynomial
		L:List
			of points
	Outputs
		Y:List
			the values of the tropicalization of {\tt f} evaluated at each of the points in {\tt L}
	Description
		Text
			This method evaluates a tropical polynomial function at a list of points.

		Example
			QQ[x,y,z]
			gfanTropicalEvaluation(x*y+z^2, {{1,1,0}, {0,0,3}, {1,1,3} })

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalevaluation"@
	SeeAlso
		gfanTropicalFunction
///

doc ///
	Key
		gfanTropicalFunction
		(gfanTropicalFunction, RingElement)
	Headline
		tropicalizes a polynomial
	Usage
		F = gfanTropicalFunction(f)
	Inputs
		f:RingElement
			a polynomial
	Outputs
		F:PolymakeFan
			the tropicalization of {\tt f}
	Description
		Text
			This method tropicalizes a polynomial. The output is a piecewise linear function given in the form of a polyhedral fan.

			For example, the tropicalization of $x*y + z^2$ is max$(x+y, 2z)$.
		Example
			QQ[x,y,z]
			gfanTropicalFunction(x*y+z^2)

		Text
			To evaluate the tropical function at a point $p$, as given by the polyhedral data above, we write it a linear combination of the appropriate ray and lineality vectors. The coefficients used are then combined in a linear combination with the given ray values.

			For instance the point $p = (1, 7, 13)$ can be written as $3(-1,-1,2) + 2(2,0,1) + 5(0,2,1)$. The values on the these rays are $4, 2$ and $2$ respectively. Thus the tropical function evaluated at $p$ is $3*4 + 2*2 + 5*2 = 26$.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalfunction"@
	SeeAlso
		gfanTropicalEvaluation
///

doc ///
	Key
		gfanTropicalHyperSurface
		(gfanTropicalHyperSurface, RingElement)
	Headline
		the tropical hypersurface of a principal ideal
	Usage
		F = gfanTropicalHyperSurface(f)
	Inputs
		f:RingElement
			a polynomial
	Outputs
		F:PolymakeFan
			the tropical hypersurface of the ideal generated by {\tt f}
	Description
		Text
			This method computes the tropical hypersurface of a principal ideal.

		Example
			QQ[x,y];
			gfanTropicalHyperSurface(x^2 + x*y)

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalhypersurface"@
	SeeAlso
		gfanTropicalBruteForce
///

doc ///
	Key
		gfanTropicalIntersection
		(gfanTropicalIntersection, List)
	Headline
		polyhedral data describing intersection of tropical hypersurfaces
	Usage
		gfanTropicalIntersection(L)
	Inputs
		L:List
			of polynomials
	Outputs
		P:PolymakeFan
			the intersection of the tropical hypersurfaces of polynomials in {\tt L}
	Description
		Text
			This method intersects a list of tropical hypersurfaces. The input is a list of polynomials whose tropicalizations give the hypersurfaces.

		Example
			QQ[x,y];
			gfanTropicalHyperSurface(x+y)
			gfanTropicalHyperSurface(x+y+1)
			gfanTropicalIntersection {x+y, x+y+1}

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalintersection"@
	SeeAlso
		gfanTropicalBruteForce
		gfanTropicalHyperSurface
///

doc ///
	Key
		gfanTropicalLifting
	Headline
		not implemented
	Description
		Text
			This method is not implemented.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicallifting"@
///

doc ///
	Key
		gfanTropicalLinearSpace
		(gfanTropicalLinearSpace, List, ZZ, ZZ)
	Headline
		equations of a tropical linear space from Pluecker coordinates
	Usage
		(L, S) = gfanTropicalLinearSpace(P,N,D)
	Inputs
		P:List
			of Pluecker coordinates
		N:ZZ
			ambient dimension
		D:ZZ
			subspace dimension
	Outputs
		L:List
			polynomials defining the linear space
		S:String
			a string describing which variable corresponds to which minor
	Description
		Text
			This method takes Pluecker coordinates for a linear subspace and computes
			the polynomials which define the corresponding tropical linear space.
			The output is a pair which contains both the defining polynomials and
			a string which describes which coordinate corresponds to which minor.

		Example
			(L, S) = gfanTropicalLinearSpace({1,2,3}, 3, 1);
			L
			S

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicallinearspace"@
///

doc ///
	Key
		gfanTropicalMultiplicity
		(gfanTropicalMultiplicity, List)
	Headline
		multiplicity of a tropical cone
	Usage
		gfanTropicalMultiplicity(L)
	Inputs
		L:MarkedPolynomialList
	Outputs
		M:ZZ
			the multiplicity of the tropical cone of {\tt L}
	Description
		Text
			This method compute the multiplicity of a tropical cone. The tropical cone is described by a marked reduced Groebner basis for 
			its initial ideal.

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalmultiplicity"@
///

doc ///
	Key
		gfanTropicalRank
		(gfanTropicalRank, Matrix)
	Headline
		the tropical rank of a matrix
	Usage
		(R, S) = gfanTropicalRank M
	Inputs
		M:Matrix
	Outputs
		R:ZZ
			the rank of {\tt M}
		S:String
			a description of how the rank was found
	Description
		Text
			This method computes the tropical rank of matrix. The output is a pair
			whose first coordinate is the rank and whose second coordinate is a string
			describing how the rank was computed.

		Example
			(R,S) = gfanTropicalRank matrix {{1,2},{1,2}};
			R
			S

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalrank"@
///

doc ///
	Key
		gfanTropicalStartingCone
		(gfanTropicalStartingCone, List)
	Headline
		a pair of Groebner bases for use with gfanTropicalTraverse
	Usage
		gfanTropicalStartingCone(L)
	Inputs
		L:List
			of homogeneous polynomials
	Outputs
		P:List
			a pair of @TO MarkedPolynomialList@s
	Description
		Text
			This method compute a pair of Groebner bases as needed for @TO gfanTropicalTraverse@.
		Example
			QQ[x,y,z]
			gfanTropicalStartingCone{x+y+z}

		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalstartingcone"@
	SeeAlso
		gfanTropicalTraverse
///

doc ///
	Key
		gfanTropicalTraverse
		(gfanTropicalTraverse, List)
	Headline
		polyhedral data describing a tropical variety
	Usage
		gfanTropicalTraverse(L)
	Inputs
		L:List
			a pair of @TO MarkedPolynomialList@s.
	Outputs
		F:PolymakeFan
			describing the tropical variety of the given ideal
	Description
		Text
			This method computes the tropical variety of a homogeneous ideal. Use @TO gfanTropicalStartingCone@ to produce
			the pair of Groebner bases that {\tt gfanTropicalTraverse} needs as input.

		Example
			QQ[x,y,z]
			P = gfanTropicalStartingCone {x+y+z}
			gfanTropicalTraverse P

		Text

			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicaltraverse"@
///

doc ///
	Key
		gfanTropicalWeilDivisor
		(gfanTropicalWeilDivisor, PolymakeFan, PolymakeFan)
	Headline
		the tropical Weil divisor of a piecewise linear function
	Usage
		W = gfanTropicalWeilDivisor(C,F)
	Inputs
		C:PolymakeFan
			a k-cycle
		F:PolymakeFan
			a piecewise linear function
	Outputs
		W:PolymakeFan
			the Weil divisor
	Description
		Text
			This method computes the tropical Weil divisor of a piecewise linear function.

			The following example is taken from the gfan manual.

		Example
			QQ[x_1..x_3];
			C = gfanTropicalHyperSurface (x_1*x_2 + x_2*x_3 + x_1*x_3 + x_1*x_2*x_3)
			F = "..."

		Text
			@STRONG "gfan Documentation"@
			@gfanHelp "gfan_tropicalweildivisor"@
///


---------------------------------------
-- Tests
---------------------------------------

-- TEST gfan
TEST ///
R = QQ[x,y,z];
L = gfan(ideal(x^2*y -y^2, y^2*x - x^2));
assert(#L == 4)
assert(any(L, l -> set first l === set {y^5,x*y^2,x^2}))

S = gfan({x^2*y -y^2, y^2*x - x^2}, "symmetry" => {{0,1,2}, {1,0,2}})
assert(#S == 2)

G = gfan(markedPolynomialList {{y^5, x*y^2, x^2},{y^5-y^2,x*y^2 - y^4, x^2 -y^4}}, "g" => true)
Gprime = {
	markedPolynomialList {{y^5,x*y^2,x^2},{y^5-y^2,-y^4+x*y^2,-y^4+x^2}},
	markedPolynomialList {{y^4,x*y^2,x^2*y,x^3},{y^4-x^2,x*y^2-x^2,x^2*y-y^2,x^3-y^3}},
	markedPolynomialList {{y^3,x*y^2,x^2*y,x^4},{-x^3+y^3,x*y^2-x^2,x^2*y-y^2,x^4-y^2}},
	markedPolynomialList {{y^2,x^2*y,x^5},{-x^4+y^2,-x^4+x^2*y,x^5-x^2}}
}
assert(G == Gprime)  -- may fail if the order of output changes
///

-- TEST gfanBuchberger
TEST ///
equalMPL = (A,B) -> set transpose A === set transpose B
QQ[x,y,z];
I = ideal(x*y + z, x*z + y);
B = gfanBuchberger(I)
Bprime = markedPolynomialList {{y^2,x*z,x*y},{y^2-z^2,x*z+y,x*y+z}}
assert equalMPL(B,Bprime)

A = gfanBuchberger(I, "w" => {1,2,3})
Aprime = markedPolynomialList {{z^2,x*z,x*y},{-y^2+z^2,x*z+y,x*y+z}}
assert equalMPL(A,Aprime)
assert not equalMPL(A, B)
///

-- TEST gfanDoesIdealContain
TEST ///
QQ[x,y,z];
assert gfanDoesIdealContain(gfanBuchberger({x*y - y, x*z + z}), {y*z})
assert not gfanDoesIdealContain(gfanBuchberger({x*y - y, x*z + z}), {y*z+1})
///

-- TEST gfanCommonRefinement
TEST ///
QQ[x,y];
F = gfanToPolyhedralFan gfan {x+y};
G = gfanToPolyhedralFan gfan {x+y^2};
C = gfanFanCommonRefinement(F,G);
assert(C#"AMBIENT_DIM" === 2)
assert(C#"DIM" === 2)
assert C#"SIMPLICIAL"
assert(C#"LINEALITY_DIM" === 0)
assert(C#"N_RAYS" === 4)
assert(set C#"RAYS" === set {{-2, -1}, {-1, -1}, {1, 1}, {2, 1}})
assert(set C#"CONES" === set {{}, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {1, 3}, {2, 3}})
///

-- TEST gfanFanLink
TEST ///
QQ[x,y];
F = gfanToPolyhedralFan {markedPolynomialList{{x}, {x+y}}};
G = gfanToPolyhedralFan {markedPolynomialList{{y^2}, {x+y^2}}};
Q = gfanFanCommonRefinement(F,G);
C = gfanFanLink(Q, {2,1}, "star" => true)
assert(C#"AMBIENT_DIM" === 2)
assert(C#"DIM" === 2)
assert C#"SIMPLICIAL"
assert(C#"LINEALITY_DIM" === 0)
assert(C#"N_RAYS" === 2)
assert(set C#"RAYS" === set {{1, 1}, {2, 1}})
assert(set C#"CONES" === set {{}, {0}, {1}, {0, 1}})
///

-- TEST gfanFanProduct
TEST ///
QQ[x,y];
F = gfanToPolyhedralFan {markedPolynomialList{{x}, {x+y}}};
G = gfanToPolyhedralFan {markedPolynomialList{{y^2}, {x+y^2}}};
C = gfanFanProduct(F,G);
assert(C#"AMBIENT_DIM" === 4)
assert(C#"DIM" === 4)
assert C#"SIMPLICIAL"
assert(C#"LINEALITY_DIM" === 2)
assert(C#"N_RAYS" === 2)
assert(set C#"RAYS" === set {{0, 0, -1, 2}, {1, -1, 0, 0}})
assert(set C#"CONES" === set {{}, {0}, {1}, {0, 1}})
assert(set C#"LINEALITY_SPACE" === set {{1, 1, 0, 0}, {0, 0, 2, 1}})
///

-- TEST gfanGroebnerCone
TEST ///
QQ[x,y];
C = gfanGroebnerCone( markedPolynomialList {{x}, {x+y}} )
assert(set C#"IMPLIED_EQUATIONS" === set {})
assert(C#"AMBIENT_DIM" === 2)
assert(C#"RELATIVE_INTERIOR_POINT" === {1, 0})
assert(set C#"LINEALITY_SPACE" === set {{1, 1}})
assert(C#"LINEALITY_DIM" === 1)
assert(C#"DIM" === 2)
assert(set C#"FACETS" === set {{1,-1}})
C = gfanGroebnerCone( markedPolynomialList {{x}, {x+y}},  markedPolynomialList {{x}, {x+y}} )
assert(set C#"IMPLIED_EQUATIONS" === set {{1, -1}})
assert(C#"AMBIENT_DIM" === 2)
assert(C#"RELATIVE_INTERIOR_POINT" === {0, 0})
assert(set C#"LINEALITY_SPACE" === set {{1, 1}})
assert(C#"LINEALITY_DIM" === 1)
assert(C#"DIM" === 1)
assert(set C#"FACETS" === set {})
///

-- TEST gfanHomogeneitySpace
TEST ///
QQ[x,y,z];
C = gfanHomogeneitySpace {x+y^2, y+z^2}
assert(set C#"IMPLIED_EQUATIONS" === set {{1, 0, -4}, {0, 1, -2}})
assert(C#"AMBIENT_DIM" === 3)
assert(C#"RELATIVE_INTERIOR_POINT" === {0, 0, 0})
assert(set C#"LINEALITY_SPACE" === set {{4, 2, 1}})
assert(C#"LINEALITY_DIM" === 1)
assert(C#"DIM" === 1)
assert(set C#"FACETS" === set {})
///

-- TEST gfanHomogenize
TEST ///
QQ[x,y];
L = {x+y, x^2*y + x};
H = gfanHomogenize(L, symbol z, "w" => {2,3})
assert(H == {x*z + y, x*z^5 + x^2*y})
L = markedPolynomialList {{y}, {x+y}};
H = gfanHomogenize(L, symbol z,  "w" => {2,3})
assert(H == markedPolynomialList {{y}, {y + x*z}})
///

-- TEST gfanInitialForms
TEST ///
QQ[x,y,z];
L = {x+y, x + z};
H = gfanInitialForms(L, {1,2,1});
assert(H == {y, x+z});
L = {x*y+z, x*z + y};
H = gfanInitialForms(L, {1,1,1});
assert(set H === set {x*y, x*z});
H = gfanInitialForms(L, {1,1,1}, "ideal" => true);
assert(set H === set {y^2 - z^2, x*y, x*z});
///

-- TEST gfanInteractive (SKIPPED)

-- TEST gfanIsMarkedGroebnerBasis 
TEST ///
QQ[x,y,z];
assert gfanIsMarkedGroebnerBasis markedPolynomialList {{x^2,y^3}, {x^2+y, y^3+z}}
assert not gfanIsMarkedGroebnerBasis markedPolynomialList {{y,y^3}, {x^2+y, y^3+z}}
///

-- TEST gfanKrullDimension 
TEST ///
QQ[x,y,z,u,v];
L = {x^3, y^2};
assert(gfanKrullDimension gfanBuchberger L === 3)
///

-- TEST gfanLaticeIdeal 
TEST ///
L = gfanLatticeIdeal {{2,-1,0},{3,0,-1}}
assert(L === {-x_0 *x_1 + x_2, x_0^2 - x_1})
///

-- TEST gfanLeadingTerms 
TEST ///
QQ[x,y,z];
L = gfanMarkPolynomialSet({x*y^3+z^4, x^2*z^2 + y^3*z}, {-1,2,5})
I = gfanLeadingTerms L
assert( I == first L)
///

-- TEST gfanMarkPolynomialSet 
TEST ///
QQ[x,y,z];
equalMPL = (A,B) -> set transpose A === set transpose B
M = gfanMarkPolynomialSet({x + y + z, x^10 + y^4 + z^2, x^2*z + y^2}, {1, 3, 5})
assert equalMPL(M, markedPolynomialList {{z,y^4,x^2*z},{x+y+z,x^10+y^4+z^2,x^2*z+y^2}})
///

-- TEST gfanMinkowskiSum 
TEST ///
QQ[x,y];
M = gfanMinkowskiSum { x + y + x*y, x + y + x*y + 1}
assert(M#"AMBIENT_DIM" === 2)
assert(M#"MAXIMAL_CONES" == {{0, 1}, {0, 2}, {1, 3}, {2, 4}, {3, 4}})
assert(M#"DIM" === 2)
assert(M#"RAYS" == {{-1, -1}, {-1, 0}, {0, -1}, {0, 1}, {1, 0}})
assert(M#"F_VECTOR" == {1, 5, 5})
///

-- TEST gfanMinors 
TEST ///
M = gfanMinors(2,2,3)
assert(M == {-m_"01"*m_"10"+m_"00"*m_"11",-m_"02"*m_"10"+m_"00"*m_"12",-m_"02"*m_"11"+m_"01"*m_"12"})
///

-- TEST gfanPolynomialSetUnion 
TEST ///
QQ[x,y,z];
f = x + y + z;
g = x + y;
h = y + z;
L = markedPolynomialList {{z, y}, {f,g}}
M = markedPolynomialList {{x, y} , {f,h}}
U = gfanPolynomialSetUnion(L,M)
equalMPL = (A,B) -> set transpose A === set transpose B
assert equalMPL(U, markedPolynomialList {{z,y,y},{x+y+z,x+y,y+z}})
///

-- TEST gfanRender SKIPPED
-- TEST gfanRenderStaircase SKIPPED

-- TEST gfanSaturation 
TEST ///
QQ[x,y,z];
I = ideal(y*z*(x-1), x*(z^2 - y));
S = gfanSaturation I;
assert(S == { z^2 -y, x-1})
///

-- TEST gfanSecondaryFan 
TEST ///
F = gfanSecondaryFan {{1,0},{1,1}, {1,2}, {1,2}}
assert(F#"AMBIENT_DIM" ===  4)
assert(F#"MAXIMAL_CONES" == {{0, 1}, {0, 2}, {1, 3}, {2, 3}})
assert(F#"SIMPLICIAL" === true)
assert(F#"DIM" === 4)
assert(F#"RAYS" == {{-2, 4, -1, -1}, {1, -2, -5, 6}, {1, -2, 6, -5}, {2, -4, 1, 1}})
assert(F#"ORTH_LINEALITY_SPACE" == {{1, -2, 0, 1}, {0, 0, 1, -1}})
assert(F#"CONES" == {{}, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {1, 3}, {2, 3}})
assert(F#"LINEALITY_SPACE" == {{1, 0, -1, -1}, {0, 1, 2, 2}})
assert(F#"PURE" === true)
assert(F#"LINEALITY_DIM" === 2)
assert(F#"N_RAYS" === 4)
assert(F#"F_VECTOR" == {1, 4, 4})
///

-- TEST gfanStats 
TEST ///
QQ[x,y,z];
L = gfan {x*y + z};
S = gfanStats L
assert(#S === 181)
///



end

installPackage "gfanInterface2"
check gfanInterface2

-------------------------------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------

-- Code for extracting options and methods

loadPackage "gfanInterface2"

applyBinary = (L, f) -> (
	S := null;
	scan(L, i -> if S === null then S = i else S = f(i,S));
	S
)

fns = select(gfanInterface2#"exported symbols", k -> 
		substring(0,4,toString k) == "gfan" and class value k === MethodFunctionWithOptions)

apply(fns, f -> f => (value f, options value f))

opts = select(apply(fns, f -> options value f), o -> o =!= null)
opts = applyBinary(opts, (x,y) -> x ++ y)
sort keys opts

-------------------------------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------


restart
installPackage("gfanInterface2")
uninstallPackage "gfanInterface2"
installPackage("gfanInterface2", UserMode=>true, DebuggingMode=>true)
installPackage("gfanInterface2", DebuggingMode=>true, RemakeAllDocumentation => true, RerunExamples => true)

loadPackage "gfanInterface2"
loadPackage("gfanInterface2", Configuration => { 
	"path" => "/Applications/Macaulay2-1.3.1/libexec/Macaulay2/x86_64-MacOS-10.6/",
	"keepfiles" => true,
	"verbose" => true
	}) 

viewHelp

R = QQ[x,y,z]; 
I = ideal(x,y+z); 
L = transpose {{x,x},{z,y+z}};
gfan(I)
gfan(ideal(x^2*y -z, y^2*z - x, z^2*x - y), "symmetry" => {{0,1,2}, {1,2,0}})
gfan(new MarkedPolynomialList from transpose{{x,x},{z,y+z}})
gfanBuchberger(I)
gfanBuchberger(I, "w"=> {1,2,3})
gfanDoesIdealContain(L, {x})
gfanDoesIdealContain(L, {y})
gfanGroebnerCone(transpose{{x,x},{y,y+z}})
gfanGroebnerCone(transpose{{x,x},{y,y+z}}, "restrict"=>true)
gfanGroebnerCone(transpose{{x,x},{y,y+z}}, "asfan"=>true)
gfanGroebnerCone({transpose{{x,x},{y,y+z}},transpose{{y,y+z},{x,x}}}, "pair"=>true)
gfanHomogeneitySpace(transpose{{x,x},{y,y+z}})
gfanHomogenize({z+1},a)
gfanInitialForms({z+x+y},{2,1,2})
gfanInitialForms({z+x+y},{2,1,2}, "pair"=>true)
gfanInitialForms({z+x+y},{2,1,2}, "ideal"=>true)
gfanIsMarkedGroebnerBasis(transpose{{y,y+z},{x, x+1}})
gfanKrullDimension(transpose{{x,x+1}})
gfanLeadingTerms(transpose{{x,x+y},{z,z+x+y}})
gfanLeadingTerms({transpose{{x,x+y},{z,z+x+y}},transpose{{x*y,x*y + y^2}}}, "m"=>true)
gfanMarkPolynomialSet({x+y+z}, {1,1,2})
gfanPolynomialSetUnion({x},{x+y})
gfanRender(gfan(ideal(x*y+z, y^3+x*z)))
gfanRenderStaircase(transpose{{x,x},{y^3,y^3}, {z^2,z^2}})
gfanRenderStaircase({transpose{{x,x},{y^3,y^3}, {z^2,z^2}},transpose{{x,x},{y^3,y^3}, {z^2,z^2}}}, "m"=>true)
gfanStats({transpose{{x,x+y},{z,z}},transpose{{y,y+x},{z,z}}})
gfanSubstitute(transpose{{y,y+x},{z,z}}, QQ[a,b,c])
gfanToLatex(transpose{{y,y+x},{z,z}}, "polynomialset"=>true)
gfanToLatex({transpose{{y,y+x}},transpose{{z,z}}}, "polynomialsetlist"=>true)
gfanToLatex({transpose{{y,y+x}},transpose{{z,z}}}, "polynomialsetlist"=>true, "h"=>true)
gfanTropicalBasis(ideal{x^2+x*y, z^2})
gfanTropicalBasis(ideal{x^2+y, z^2}, "h"=>true)
gfanTropicalIntersection({x^2+y, z^2})
gfanTropicalIntersection({x^2+y, z^2}, "t"=>true)
gfanTropicalStartingCone({x^2+y*x, x*y+z^2})
gfanTropicalStartingCone({x^2+y*x, x*y+z^2}, "d"=>true)
gfanTropicalTraverse(gfanTropicalStartingCone({x^2+y*x, x*y+z^2}))
gfanTropicalMultiplicity(first gfanTropicalStartingCone({x^2+y*x, x*y+z^2}))
gfanSaturation(ideal(z*y-z*x))
gfanToPolyhedralFan({transpose{{x*y, x*y+ z}, {z,z}}, transpose{{x*y, x*y},{z,z}}})
gfanToPolyhedralFan({transpose{{x*y, x*y+ z}, {z,z}}, transpose{{x*y, x*y},{z,z}}}, "restrict"=>true)
gfanToPolyhedralFan(gfan(ideal(x^2*y -z, y^2*z - x, z^2*x - y), {{0,1,2}, {1,2,0}}, "symmetry"=>true), {{0,1,2}, {1,2,0}}, "symmetry"=>true)
gfanTropicalBruteForce(transpose{{x*y,x*y + z}, {z,z}})

-------- examples from the gfan manual ----------
R = QQ[a..j]
I = ideal"bf-ah-ce, bg-ai-de, cg-aj-df, ci-bj-dh, fi-ej-gh"
gfan I
first oo
last ooo
o10/first/monomialIdeal

-- Andrew, try this. You might need to update your M2, and rebuild, which gives you a bug-fixed gfan (0.4plus).
-- I want to discuss with you at some point what the actual fields in the polymake object should be called, and what the types of their values should be.
-- e.g. MULTIPLICITIES, and MULTIPLICITIES_COMPRESSED seem to have different types. **FIXED
-- (other comments:
--  MY_EULER is Anders' private info, so let's remove it **FIXED (errors are no longer produced on unrecognised blocks)
--  _COMPRESSED should be called _ORBITS (Anders said so: he made a mistake) **NOT FIXED 
--  SIMPLICIAL: should be a boolean **FIXED (I updated the type and converted 1 into true)
--  we should probably make the type: PolymakeFan **FIXED (now I'm parsing the type in the header)
R = QQ[a..o] 
I = ideal"bg-aj-cf, bh-ak-df, bi-al-ef, ck-bm-dj, ch-am-dg, cl-ej-bn, ci-eg-an, dn-co-em, dl-bo-ek, di-ao-eh, gk-fm-jh, gl-fn-ij, hl-fo-ik, kn-jo-lm, hn-im-go"
C = gfanTropicalStartingCone I_*; 
D = gfanTropicalTraverse(C, "symmetry" => {{0,8,7,6,5,4,3,2,1,14,13,11,12,10,9}, {5,6,7,8,0,9,10,11,1,12,13,2,14,3,4}})

