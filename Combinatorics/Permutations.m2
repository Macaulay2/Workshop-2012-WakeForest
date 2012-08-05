if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "Posets";
    )

newPackage select((
    "Permutations",
        Version => "1.0.1", 
        Date => "August 5 2011",
        Authors => {
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"}
        },
        Headline => "A package for combinatorics on graphs, simplicial complexes, permutations, and posets",
        Configuration => {"DefaultPDFViewer" => "open", "DefaultPrecompute" => true, "DefaultSuppressLabels" => true},
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs", "Posets"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "Posets";
    )

export {
     Permutation,
     permutation,
--     Permutations,
     permute,
     Cycle,
     cycle,
     cycleDecomposition,
     --checkCycle,
     checkTranspositions,
     isBasicPermutation,
     isTransposition,
     isSimpleTransposition,
     fillBasicPermutation,
     composePermutations,
     permutationVector,
     identityPermutation,
     isIdentity,
     inverseOfPermutation,
     toPermutation,
     --minChangePermutations,
     lengthOfTranspositions,
     lengthOfPermutation,
     countOrbits,
     countFixedPoints,
     randomPermutation,
     inversionVector,
     permutationFromInversionVector,
     permuteSet,
     permuteRows,
     permuteColumns,
     permutationMatrix,
     cartesianProduct,
     --numberOfInversions,
     --subsets [already implemented in basic M2]
     --compositions [already implemented in basic M2]
     --partitions [already implemented in basic M2] (ZZ) or (ZZ,ZZ)
     --partition [implemented and USEFUL!]
     --conjugate partition
     --isPermutation
     bruhatComparison,
     BruhatOrder,
     BruhatRelations,
     weakBruhatOrder,
     weakBruhatRelations,
     weakBruhatComparison,
     coveringPair,
     minimalCycles,
     rotateRight,
     rotateLeft,
     displayPermutation,
     sign,
     simpleTranspositions
};

----------------------------------------------------------------------------------------
--
-- TYPES
--
----------------------------------------------------------------------------------------
-----
---Various ways of defining Permutations (Vectors, Cycles, Tranpositions)
-----
----------------------------------------------------------------------------------------

Permutation = new Type of HashTable
Cycle = new Type of List


------------------------------------------------------------------
------------------------------------------------------------------
--Net for Displaying Permutations
------------------------------------------------------------------
------------------------------------------------------------------
net Permutation := P -> toString P -- displayPermutation P -- toString P

displayPermutation = method()
displayPermutation(Permutation) := Net => (P) -> (
	L := apply(sort keys P.map, k -> (toString(k) || toString(P(k))) | (" "||" "));
	L = {"( " || "( "}  | L | {")"||")"};
	horizontalJoin L
)

------------------------------------------------------------------
------------------------------------------------------------------
--Various Constructors
------------------------------------------------------------------
------------------------------------------------------------------

permutation = method()

toString Permutation := P -> toString(apply(sort keys P.map,i->(P.map)#i))


------------------------------------------------------------------
--This method constructs a permutation as a pair of lists, which
--contain the same (nonrepeating) elements.
------------------------------------------------------------------

permutation(List,List) := Permutation => (M,L) -> (
	if(set L === set M) and (unique L === L) and (unique M === M) then
		permutation hashTable apply(#M, i -> M#i=>L#i)
	else error "Not a permutation."
)

------------------------------------------------------------------
--This method takes a list L as input, and outputs the permutation
--taking the (sorted) L as input and outputting L.
--Example:  L = {5,1,4,2,3} would give the permutation s = (1,2,4,3,5),
--written here in cycle notation.  It would be stored as the hash 
--table {1 => 2, 2=> 4, 3=>5, 4=>3, 5=>1}.
------------------------------------------------------------------

permutation(List):= Permutation => L -> (     
	if unique L === L then
	(
		M := sort L;
		permutation hashTable apply(#M, i -> M#i=>L#i)
	) else error "Not a permutation."
)

------------------------------------------------------------------
--This method picks the ith permutation (lex ordered) out of
--permutations of list L.
------------------------------------------------------------------

permutation(List,ZZ) := Permutation => (L,i) -> (
	if 0 <= i and i <= (#L)!-1 then
		permutation permutationByIndex(L, i)
	else 
		error("Permutation index (" | i | ") too large for list size (" | #L | ").")
)

------------------------------------------------------------------
-- This constructs a permutation (array form) from a cycle.
------------------------------------------------------------------

permutation(Cycle) := Permutation => (L) -> (
	S := apply(L, l -> orbitToPermutation l);
	fold(S, (i,j) -> composePermutations(i,j))     
)

------------------------------------------------------------------
-- This extends a permutation on {1,2,..,#P} to {1,2,...,#N}.
------------------------------------------------------------------

permutation(Permutation, ZZ) := Permutation => (P, N) ->
	composePermutations(P, identityPermutation N)

------------------------------------------------------------------
-- This constructs the nth permutation (lex) on {1,2,..,m}.
------------------------------------------------------------------

permutation(ZZ,ZZ) := Permutation => (m,n) -> 
	permutation(toList (1..m), n)

------------------------------------------------------------------
-- This converts a hash table to a permutation.
------------------------------------------------------------------

permutation(HashTable) := Permutation => (H) -> 
	new Permutation from hashTable {symbol map => H, symbol cache => new CacheTable}



----------------------------------------
--Helper Function for permutation(Cycle)
--Converts a list representing one orbit 
--of a cycle decomposition into a permutation.
---------------------------------------------

orbitToPermutation = (L) -> (
	permutation hashTable flatten apply(#L, i-> L#i => L#((i+1) %#L))
)

--------------------------------------------
-- Helper function for permutation(List, ZZ)
--------------------------------------------
permutationByIndex = (L,i) -> (
	if #L <= 1 then return L;
	k := (#L - 1)!;
	j := i % k;
	l := round((i - j)/k); -- i = l * #L! + j
	prepend(L#l, permutationByIndex(drop(L, {l,l}), j))
)

----------------------------------------------------------------------------------------
-----
---Various ways of defining Permutations (Vectors, Cycles, Tranpositions)
-----
----------------------------------------------------------------------------------------

isBasicPermutation = method()

isBasicPermutation(Permutation):= Boolean => (P) -> 
	all(keys P.map, k -> class k === ZZ)

fillBasicPermutation = method()

fillBasicPermutation(Permutation):= Permutation => (P)->(
	if not isBasicPermutation P then
		error "Not correct type of Permutation.";
	a := min keys P.map;
	b := max keys P.map;
	I := identityPermutation(toList(a..b));
	I*P
)

----------------------------------------------------------------------------------------
-----
-----
-----
----------------------------------------------------------------------------------------


Permutation Thing := (p,t) -> if p.map#?t then (p.map)#t else t

List / Permutation := List => (L,p)-> apply(L, x-> p x)

permute = method()

permute(List, Permutation) := (L,P) -> L / P

permuteSet = method()

permuteSet(List, Permutation) := List => (L,P) -> 
	apply(toList(1..#L) / P, i -> L#(i-1))

permuteRows = method()

permuteRows(Matrix,Permutation):= Matrix => (M,P) -> (
	matrix permuteSet(entries M,P)
)

permuteColumns = method()

permuteColumns(Matrix, Permutation):= Matrix => (M,P) -> (
	matrix transpose permuteSet(entries transpose M,P)
)

Permutation * Matrix := Matrix => (P,M) -> permuteRows(M,P)

Matrix * Permutation := Matrix => (M,P) -> permuteColumns(M,P)

permutationMatrix = method()

permutationMatrix(Permutation) := Matrix => (P) -> (
	if isBasicPermutation P then (
		n := max keys P.map;
		matrix apply(toList(1..n), i -> 
			apply(toList(1..n), j -> if P(j) === i then 1 else 0))
	) else error "Not a basic permutation"
)

----------------------------------------------------------------------------------------
-----
---Cycles
-----
----------------------------------------------------------------------------------------

toCycleString:= (L) -> (
	"(" |
		concatenate apply(#L, i -> (
			spaceStr:="";
			if i=!= #L-1 then spaceStr=" ";
			toString(L#i) | spaceStr
			)
		)
	| ")"
)

toString Cycle := (C) -> concatenate apply(C, toCycleString)

net Cycle := (C) -> toString C

cycle = method()

cycle(List):= Cycle => (L)-> (     
	L = apply(L, toList);
	if all(L, l -> l === unique l) then
		new Cycle from L
	else
		error "Not a set of cycles."
)

cycle(List,ZZ) := Cycle => (L,N) ->
	cycle(cycle L, N)

cycle(Cycle, ZZ) := Cycle => (C, N) -> (
	P := permutation C;
	I := identityPermutation N;
	cycle composePermutations(P,I)
)

--Returns canonical decomposition for cycles.  Has trouble if comparing numbers to symbols.
cycle(Permutation) := Cycle => (P) -> (
	if P.cache.?cycleDecomposition then (
		return P.cache.cycleDecomposition;
	);
	L := keys P.map;
	Z :={};
	while #L=!=0 do (
		m := max L;
		K :={m};
		i :=(P.map)#m;
		while i=!=m do (
			K = append(K,i);
			i = P.map#i;
		);
		if #K>1 then Z = append(Z,K);
		L = select(L,l-> not member(l,K));
	);
	P.cache.cycleDecomposition = new Cycle from Z
)

----------------------------------------
--
-- Types of permutations
--
----------------------------------------

identityPermutation = method()

identityPermutation(ZZ) := Permutation => (N) -> permutation toList(1..N)

identityPermutation(List) := Permutation => (L) -> permutation(L,L)

isIdentity = method()

isIdentity(Permutation) := Boolean => (P) ->
	all(keys P.map, k -> k == P(k))

rotateRight = method();
rotateRight(ZZ) := Permutation => (N) -> permutation cycle {toList(1..N)}

rotateLeft = method();
rotateLeft(ZZ) := Permutation => (N) -> permutation cycle reverse {toList(1..N)}




--This just puts possible cycles in a standard format, which is a list of lists.
--
--cycleToCycle = method()
--
--cycleToCycle(List):= List =>(l) -> (
--     apply(l, i->toList i)
--     )
 
--This checks if each cycle consists of unique elements.  Does NOT assume cycles are disjoint.

--checkCycle = method ()
--
--checkCycle(List):= Boolean => (L) -> (
--     c:=cycleToCycle L;
--     S:=apply(c, i-> unique i);
--     if L===S then true
--     else "Not a set of cycles."
--     )



----------------------------------------------------------------------------------------
-----
---Transpositions
-----
----------------------------------------------------------------------------------------

--This function checks that a transposition is made up up a list of pairs of elements.
--No information about a "base set" is assumed.  
isTransposition = method()

isTransposition(Cycle) := Boolean => (C) -> (
	D := minimalCycles C;
	#D === 1 and #(first D) === 2 
)

isTransposition(Permutation) := Boolean => (P) -> isTransposition cycle P

isSimpleTransposition = method()

isSimpleTransposition(Cycle) := Boolean => (C) -> (
	D := minimalCycles C;
	#D === 1 and #(first D) === 2 and 1 + min first D === max first D
)

isSimpleTransposition(Permutation) := Boolean => (P) -> lengthOfPermutation P === 1


simpleTranspositions = method()

-- Implemented using bubble sort
simpleTranspositions(Permutation) := Cycle => (P) -> (
	L := permutationVector P;
	cycle reverse flatten apply(#L, i -> apply(number(take(L, i), p -> p > L#i), j -> {i-j+1,i-j}))
)

simpleTranspositions(Cycle) := Cycle => (C) -> 
	simpleTranspositions permutation C


----------------------------------------------------------------------------------------
-----
---Permutation Operations
-----
----------------------------------------------------------------------------------------

randomPermutation = method()

randomPermutation(ZZ) := Permutation => (N) -> (
	L := toList (1..N);
	M := toList random L;
	permutation(L,M)
)

permutationVector = method()

permutationVector(Permutation):= List => (P) -> 
	apply(sort keys P.map, k -> P(k))

inverseOfPermutation = method()

inverseOfPermutation(Permutation):= Permutation => (P) -> (
	M := P.map;
	A := hashTable apply(keys M, i-> M#i=>i);
	permutation A
)

inversionVector = method()

inversionVector(Permutation):= List => (P) ->(
	if P.cache.?inversionVector then return P.cache.inversionVector;
	if isBasicPermutation P then 
		P = fillBasicPermutation P;
	L := permutationVector P;
	P.cache.inversionVector = apply(#L, i -> number(take(L, i), p -> p > L#i))
)

permutationFromInversionVector = method();

permutationFromInversionVector(List) := (L) -> (
	N := reverse toList(1..#L);
	L = reverse L;
	permutation reverse apply(L, i -> ( A := N#i; N = drop(N,{i,i}); A))
)

lengthOfPermutation = method()

lengthOfPermutation(Permutation) := ZZ => (P) -> (
	if P.cache.?lengthOfPermutation then return P.cache.lengthOfPermutation;
	P.cache.lengthOfPermutation = sum inversionVector P
)


countOrbits = method()

countOrbits(Permutation) := ZZ => (P) -> #cycle P

countOrbits(Cycle) := ZZ => (C) -> #cycle permutation C

countFixedPoints = method()

countFixedPoints(Permutation) := ZZ => (P) -> 
	number(keys P.map, k -> k == P(k))

sign = method()

sign(Permutation) := ZZ => (P) -> 
	if even lengthOfPermutation P then 1 else -1

sign(Cycle) := ZZ => (C) -> 
	if even sum apply(C, L -> #L - 1) then 1 else -1

Permutation ^ ZZ := (P,N)->(
	if N === 0 then return identityPermutation keys P.map;
	if N === 1 then return P;
	if N < 0 then return (inverseOfPermutation P)^(-N);
	if N % 2 === 0 then 
		(P*P)^(floor(N/2))
	else
		P * ((P*P)^(floor(N/2)))
)

composePermutations = method()

composePermutations(Permutation,Permutation):= Permutation => (P,M) -> (
     permutation hashTable apply(keys M.map | keys P.map, i-> i=> P(M(i)))
     )

Permutation * Permutation := composePermutations

--Product = Concatenation
Cycle ** Cycle := Cycle => (C,D) -> C|D

--Pairwise minimal product
Cycle * Cycle := Cycle => (C,D) -> minimalCycles(C|D)

minimalCycles = method()

minimalCycles(Permutation) := Cycle => (P) -> 
	cycle P

--Takes a list of cycles or a Cycle
minimalCycles(List) := Cycle => (M) -> 
	cycle permutation cycle M

----------------------------------------------------------------------------------------
-----
---Bruhat Order
-----
----------------------------------------------------------------------------------------

Permutation == Permutation := Boolean => (P,S) -> 
	isIdentity((P^-1)*S)

Permutation ? Permutation := (P,S)-> (
	weakBruhatComparison(P,S)
)

cartesianProduct = method()

cartesianProduct(List,List):= List => (H,J) -> (
     flatten apply(H, h-> apply(J, i-> {h,i}))
     )

weakBruhatComparison = method()

weakBruhatComparison(Permutation,Permutation) := (P,S)->(
     if P==S then symbol==
     else if lengthOfPermutation(P) === lengthOfPermutation(S)+lengthOfPermutation((S^-1)*P) then symbol >
     else if lengthOfPermutation(S) === lengthOfPermutation(P)+lengthOfPermutation((P^-1)*S) then symbol <
     else incomparable
     )

-- returns true if Q covers P
weakBruhatCover = method()
weakBruhatCover(Permutation, Permutation) := (P,Q) -> 
	lengthOfPermutation(P) < lengthOfPermutation(Q) and isSimpleTransposition(P^-1 * Q)

bruhatCover = method()
bruhatCover(Permutation, Permutation) := (P,Q) -> 
	lengthOfPermutation(P) < lengthOfPermutation(Q) and isTransposition(P^-1 * Q)


lowerOnes = (n) -> matrix apply(n, i-> 
     apply(n, j->(if i>=j then 1 else 0) ) )

rankMatrix = (p) -> lowerOnes(# keys p.map) * permutationMatrix(p) * transpose (lowerOnes(# keys p.map))


------------------------------------------
-- bruhatComparison
------------------------------------------
-- Compares two permutation with respect to
-- the Bruhat order and returns
-- one of ==, <, >, or incomparable.
------------------------------------------
-- The algorithm works by recursively producing
-- all permutations greater than the lower
-- lengthed input. These greater permutations
-- are made by multiplying by an arbitrary
-- transposition. Recursion is stopped if 
-- the length decreases or becomes larger than 
-- the length of the larger permutation.
-- Visited permutations are cached.
-- Also lengths are not computed using
-- the normal algorithm, but updated
-- using lengthOfPermutationTransposition.

bruhatComparison = method()
bruhatComparison(Permutation, Permutation) := (P,Q) -> (
	if P == Q then return symbol==;
	if lengthOfPermutation(P) == lengthOfPermutation(Q) then return incomparable;
	comparisonSign := symbol<;
	if lengthOfPermutation(P) > lengthOfPermutation(Q) then (
		(P,Q) = (Q,P);
		comparisonSign = symbol>;
	);
	N := length permutationVector P;
	transpos := flatten apply(toList(1..(N-1)), i -> apply(toList((i+1)..N), j -> {i,j}));
	VisitedPermutations := set {};
	recursiveBruhatComparison := (P) -> (
		if P == Q then return true;
		if lengthOfPermutation P >= lengthOfPermutation Q then return false;
		any(transpos, T -> ( 
				R := P * permutation cycle {T};
				R.cache.lengthOfPermutation = lengthOfPermutationTransposition(P,T);
				if lengthOfPermutation R < lengthOfPermutation P then return false;
				if member(R, VisitedPermutations) then return false;
				VisitedPermutations = VisitedPermutations + set {R};
				if #VisitedPermutations % 100 === 0 then << #VisitedPermutations << endl;
				if recursiveBruhatComparison(R) then (
					<< T << endl;
					true
				) else false
			)
		)
	);
	if recursiveBruhatComparison(P,Q) then comparisonSign else incomparable
)

bruhatInterval = method()
bruhatInterval(Permutation, Permutation) := (P,Q) -> (
	if P == Q then return set { {P, set{}}};
	if lengthOfPermutation(P) >= lengthOfPermutation(Q) then return set{};
	N := length permutationVector P;
	transpos := flatten apply(toList(1..(N-1)), i -> apply(toList((i+1)..N), j -> {i,j}));
	VisitedPermutations := set {};
	IntervalPermutations := set {};
	isInInterval := (P) -> (
		if P == Q then (
			IntervalPermutations = IntervalPermutations + set {P};
			return true;
		);
		if lengthOfPermutation P >= lengthOfPermutation Q then return false;
		L := apply(transpos, T -> (
				R := P * permutation cycle {T};
				R.cache.lengthOfPermutation = lengthOfPermutationTransposition(P,T);
				R
			)
		);
		L = select(L, R -> 
			member(R, IntervalPermutations) or 
			(	(not member(R, VisitedPermutations))
				and lengthOfPermutation R < lengthOfPermutation P
				and isInInterval R
			)
		);
		if #L === 0 then (
			VisitedPermutations = VisitedPermutations + set {P};
		) else (
			IntervalPermutations = IntervalPermutations + set {P};
		);
		#L == 0
	);
	isInInterval(P);
	IntervalPermutations
)

--Computes the length of P*T
--P a permutation
--T a list of length two describing a transposition
lengthOfPermutationTransposition = (P,T) -> (
	I := min T;
	J := max T;
	A := P I;
	B := P J;
	L := lengthOfPermutation P;
	V := drop(drop(permutationVector P, I), J - 1 - length permutationVector P);
	if B > A then 
		L + 1 + 2 * number(V, i -> A < i and i < B) 
	else 
		L - 1 - 2 * number(V, i -> B < i and i < A)
)


weakBruhatRelations = method()

weakBruhatRelations(ZZ):= List => (N) -> (
	P := (permutations toList(1..N)) / permutation;
	PR := partition(p-> lengthOfPermutation p, P);
	H := flatten join values PR;
	m:= max keys PR;
	CH:= flatten apply( P, h-> apply( P, i-> {h,i}));
	CP:= flatten apply( #P, h-> apply( #P, i-> {h,i}));
	R:= flatten apply(toList(0..m-1), i-> cartesianProduct(PR#i,PR#(i+1)));
	GL:=select(R, r-> isSimpleTransposition((first r)^-1 *(last r)));
	apply(positions(CH, r-> member(r,GL)), i-> CP_i)
)


weakBruhatOrder = method()

weakBruhatOrder(ZZ):= Poset => (N) ->(
     B:= weakBruhatRelations N;
     H:= unique flatten B;
     S:= toList(0..(#H-1));
     poset(S, B)
     )

coveringPair = method()

coveringPair(Permutation,Permutation):= Boolean => (P,S) -> (     
     (# first cycle composePermutations(P,(S^-1)))===1
     )

BruhatRelations = method()

BruhatRelations(ZZ):= List => (N)->(
     P:=apply(permutations toList(1..N), i-> permutation i);
     PR:= partition(p-> lengthOfPermutation p, P);
     H:=flatten join values PR;
     m:= max keys PR;
     CH:= flatten apply( P, h-> apply( P, i-> {h,i}));
     CP:= flatten apply( #P, h-> apply( #P, i-> {h,i}));
     R:= flatten apply(toList(0..m-1), i-> cartesianProduct(PR#i,PR#(i+1)));
     GL:=select(R, r-> coveringPair(first r, last r));
     apply(positions(CH, r-> member(r,GL)), i-> CP_i)
     )


BruhatOrder = method()

BruhatOrder(ZZ):= Poset => (N) ->(
     B:= BruhatRelations N;
     H:= unique flatten B;
     S:= toList(0..(#H-1));
     poset(S, B)
     )


beginDocumentation()


---------------------------------------------------------
---------------------------------------------------------
-- Simple Doc information
---------------------------------------------------------
---------------------------------------------------------

--*******************************************************
-- DOCUMENTATION FOR PACKAGE
--*******************************************************

doc ///
	Key
		Permutations
       	Headline
		A package for working with permutations, partitions, and combinatorics of various objects.
	Description
		Text
			{@EM "Permutations"@ is a package that implements many algorithms for the permutations or partitions of sets,
			along with various other combinatorial functions.}
///


doc///
     Key
     	Permutation
     Headline
        a class for permutations
     Description
        Text
	   	     This class represents permutations of a finite set.  One way to describe a permutation is
		     just as a finite list.  In this case, permutation L will be the map from the entries in L,
		     sorted from least to greatest, to the ordered list L.
     	Example
	     	  M={2,4,5,1,3,7,6}
		  permutation M
		  peek M
	Text
	     	  Permutations are stored as a hash table of maps from items in the list to other items in the list.
		  A second way to enter a permutation then is to take two different orderings of a list, and let the
		  permutation take the first element of the first list to the first element of the second list, and so
		  on.  The displayed permutation vector will have put the keys of the first list
		  into increasing order.
	Example
	     	  M={2,4,5,1,3,7,6}
		  L={5,3,2,6,4,7,1}
		  permutation(M,L)
		  
	Text
	     	  As Macaulay 2 will already enumerate all permutations of a list L in the lexicographic
		  order, a third way of entering a partition is to give a list L and an integer n,
		  which will pick out the (n+1)st permutation of the list under that ordering.
		  
	Example
	     	  M={3,2,1,4}
		  permutations M
		  permutation(M,0)
		  permutation(M,23)

	Text
	     	  A final way of entering a partition is via a pair of numbers n and m.  This will
		  output (m+1)st permutation, under the lexicographic order, of the set {1,2,..,n}.
	
	Example
	     	  permutation(5,0)
     	       	  permutation(5,10)
	     	  permutation(5,119)
	
	Text
	     	  The permutation is being stored as a map containing a set of keys (the base set L) 
		  and where they go under the permutation.  We can have these permutations act on a list 
		  in one of two key ways.  First, we could take elements in the list to their images under
		  the permutation vector.
	
	Example
	     	  P=permutation{5,4,3,2,1}
		  peek P
		  S={3,4,5,1,2}
		  permute(S,P)
		  T={cat, dog, 1,2,3}
		  permute(T,P)
     	
	Text
	     	  Alternately, we could have the permutation act on the ordering of elements in the list.
	
	Example
	     	  P=permutation{5,4,3,2,1}
		  S={3,4,5,1,2}
		  permuteSet(S,P)
     	
	Text
	     	  The list can contain just about anything, including symbols, rings, functions, or repeated elements.
	
	Example
	    	  P=permutation{5,4,3,2,1};
		  permuteSet({cat, dog, 1,2,3},P)
		  permuteSet({A,B,C,A,D},P)
		  permuteSet({ZZ, ZZ/10007[a,b,c],QQ, CC[x,y], ZZ/2},P)
	
	Text
	      	  One specific additional function included with Permutations is applying a permutation 
		  to the rows or columns of a matrix M.
	Example
	      	  M=matrix{{1,2,3,4,5},{6,7,8,9,10},{11,12,13,14,15}}
		  P=permutation{3,2,1,5,4}
		  permuteRows(M,P)
		  P*M
		  permuteColumns(M,P)
		  M*P
		  
     SeeAlso
          permutation

///
doc///
	Key
     		permutation
		(permutation, List)
		(permutation, List, List)
		(permutation, List, ZZ)
		(permutation, ZZ, ZZ)
		(permutation, HashTable)
	Headline
     		returns a permutation of a list
	Usage
     		P = permutation L
		P = permutation(M,L)
		P = permutation(L,n)
		P = permutation(m,n)
     	Inputs
     		L: List
     			list of permuted elements
		M: List
			list of original elements
		n: ZZ
			the nth permutation of L under the lex order
		m: ZZ
			the set of elements from 1 to m
     	Outputs
      		P:Permutation
			a hashtable with keys corresponding to elements of a list, and values describing 
			where the keys go under the permutation
	Description
      		Text
			This method returns a particular permutation of a set L.
		Example
	   		M={1,2,3,4,5,6,7}
	       		L={5,3,2,6,4,7,1}
			permutation L
			permutation(M,L)
			cycle permutation(M,L)
///

doc///
     Key
          Cycle
     Headline
          a class for cycles
     Description
          Text
	       This class represents all cycles.  Given any permutation P, we can 
	       compute the cycle structure directly.
          Example
	       P=permutation{7, 10, 14, 4, 3, 1, 8, 6, 11, 12, 2, 5, 15, 9, 13}
	       C= cycle P
	  Text
	       A cycle can be created from any list of lists, so long each individual list
	       contains no repeated elements.  It can then be converted to the minimal cycle
	       representation.
	  Example
	       L={{1,2,3,4},{3,4,5},{5,1,2},{6,5}};
	       C=cycle L
     	       M=minimalCycles C
	  Text
	       Two cycles can be concatenated or composed, where they are viewed as acting on the
	       left.  Concatenation will not necessarily return a minimal structure,
	       whereas composing cycles will return a minimal cycle.
	  Example
	       C=cycle {{1,2,3,4},{3,4,5}}
	       D=cycle{{5,1,2},{6,5,3}}
     	       C*D
	       C**D
     SeeAlso
          permutation
	  cycle
	  minimalCycles


///

doc///
     Key
     	  cycle
	  (cycle, List)
     Headline
     	  returns a cycle
     Usage
     	  C = cycle L
     Inputs
     	  L: List
	       list of lists of cycles
     Outputs
     	  C: Cycle
	       a type of list with elements corresponding to cycles of a permutation,
	       not necessarily disjoint
     Description
     	  Text
	       Given any list of lists of disjoint elements, we can create a cycle permuting
	       the elements.  We can also create a cycle from a permutation via cycle.
	  Example
     	       C=cycle{{5,3,1},{6,2},{10,9,8,7,4}}
     	       cycle permutation {3,7,5,1,4,2,8,9,6,10}
	       D=cycle{{5,6,1},{4,5,2},{1,4,10,9}}
     	       minimalCycles D
     SeeAlso
     	  minimalCycles
	  Cycle

///


doc///
     Key
     	  permute
	  (permute, List, Permutation)
     Headline
     	  permutes a set via the permutation map
     Usage
     	  S=permute(L,P)
     Inputs
     	  L: List
	       list of elements to be permuted
	  P: Permutation
     Outputs
     	  S: List
     Description
     	  Text
	       Permute will take elements of a list and map them to their images
	       under the permutation.  If the list contains elements which are not in
	       the keys of the map of permutation P, they will map back to themselves.
	  Example
	       L={A,B,1,2,C,4}
	       P=permutation {4,5,1,2,3} ;
	       P.map
	       permute(L,P)
     SeeAlso
     	  permuteSet
	  (permuteSet, List, Permutation)
///

doc///
     Key
     	  permutationVector
	  (permutationVector, Permutation)
     Headline
     	  returns the ordered list of values of the permutation map
     Usage
     	  permutationVector P
     Inputs
     	  P: Permutation
     Outputs
     	  L: List
     Description
     	  Text
	       A permutation can be thought about as acting on a base set of elements.
	  Example
	       P=permutation({9,4,2,10,15,1},{10,9,1,2,4,15})
	       K={9,4,2,10,15,1}
	       B=sort K
	  Text
	       The list of values of these keys, in order, is the permutation vector.  It is already
	       displayed as the net of a permutation.
	  Example
	       P=permutation({9,4,2,10,15,1},{10,9,1,2,4,15})
	       B=sort {9,4,2,10,15,1}
	       P(B)
     SeeAlso
     	  permutation
///	  

doc///
     Key
     	  minimalCycles
     Headline
     	  returns the minimal cycle decomposition of a cycle
     Usage
     	  minimalCycles C
     Inputs
     	  C: Cycle
	       any set of cycles, possibly nondisjoint
     Outputs
     	  D: Cycle
	       the minimal cycle decomposition of C
     Description
     	  Text
	       Given any set of cycles, this
     SeeAlso
///

--doc///
--     Key
--     Headline
--     Usage
--     Inputs
--     Outputs
--     Description
--     SeeAlso
--///
--doc///
--     Key
--     Headline
--     Usage
--     Inputs
--     Outputs
--     Description
--     SeeAlso
--///
--doc///
--     Key
--     Headline
--     Usage
--     Inputs
--     Outputs
--     Description
--     SeeAlso
--///
-------------------------------------
-- Test Permutation Maker
-------------------------------------


-------------------------------------
-- Test Single List
-------------------------------------

TEST///
L={7,6,5,4,3,2,1}
P=permutation L
L=toString L
assert(toString L=== net P)
assert(net P === toString reverse toList(1..7))
///

TEST///
L={1,2,3,4,5,6,7}
P=permutation L
assert(toString L===net P)
assert(net P === toString toList (1..7))
///

TEST///
L={5,6,70,1,3,4,2,10}
P=permutation L
assert(toString L=== net P)
///


-------------------------------------
-- Test Conversion of Permutation to Cycles
-------------------------------------

TEST///
L={9, 5, 2, 3, 7, 4, 6, 8, 1, 10}
C=cycle permutation L
assert(net C=== "(9 1)(7 6 4 3 2 5)")
D=cycle (permutation L)^-1
assert(net D==="(9 1)(7 5 2 3 4 6)")
P=permutation {11,3,10,6,13,5,8,1,7,12,2,4,14,15,9}
assert(P===toPermutation cycle P)
///
-------------------------------------
-- Test Permutation Inverses
-------------------------------------

TEST///
L={9, 5, 2, 3, 7, 4, 6, 8, 1, 10}
P=permutation L
P^-1
assert(toString net P^-1=== toString {9,3,4,6,2,7,5,8,1,10})
///

-------------------------------------
-- Test Cycle & Transposition Checks
-------------------------------------
TEST///
L=cycle{{5,1,2},{6,5}}
M=minimalCycles L
assert(net M=== "(6 1 2 5)")
J=cycle{{3,4,5},{5,1,2},{6,5}}
K=cycle{{3,4,5},{6,1,2,5}}
assert(net minimalCycles J=== net minimalCycles K)
///

end

installPackage "Permutations"
loadPackage "Permutations"

shiftIndex = method()

shiftIndex(List):= List => (L)->(
apply(L, i->apply(i, r->r+1))
     )

shiftIndex permutations 5


isPermutation = method()

isPermutation(List):= Boolean => (L) -> (
     if 
     )

loadPackage "Permutations"
(P,Q) = (randomPermutation 6, randomPermutation 6)
bruhatComparison(P,Q)


P = permutation {3, 1, 4, 5, 7, 2, 6}
Q = permutation {5, 7, 1, 3, 4, 6, 2}
L = reverse apply({{6, 7},{2, 5},{2, 4},{2, 3},{1, 4},{1, 3}}, i -> permutation cycle {i})
lengthOfPermutation(P)
lengthOfPermutation(P*L_0)
lengthOfPermutation(P*L_0*L_1)
lengthOfPermutation(P*L_0*L_1*L_2)
lengthOfPermutation(P*L_0*L_1*L_2*L_3)
lengthOfPermutation(P*L_0*L_1*L_2*L_3*L_4)
lengthOfPermutation(P*L_0*L_1*L_2*L_3*L_4*L_5)
P*L_0*L_1*L_2*L_3*L_4*L_5
bruhatComparison(P,Q)
