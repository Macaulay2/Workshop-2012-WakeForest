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
     Cycle,
     cycle,
     cycleDecomposition,
     displayPermutation,
     permute,
     permuteRows,
     permuteColumns,
     permutationMatrix,
     inverseOfPermutation,
     minimalCycles,
     identityPermutation,
     isIdentity,
     rotateRight,
     rotateLeft,
     permutationVector,
     inversionVector,
     permutationFromInversionVector,
     lengthOfPermutation,
     countOrbits,
     countFixedPoints,
     sign
};

----------------------------------------------------------------------------------------
--
-- TYPES
--
----------------------------------------------------------------------------------------
-----
---Ways of defining permutations (Array form and Cycle form)
-----
----------------------------------------------------------------------------------------

Permutation = new Type of HashTable
Cycle = new Type of List


------------------------------------------------------------------
------------------------------------------------------------------
--Net for Displaying Permutations
------------------------------------------------------------------
------------------------------------------------------------------
net Permutation := P -> toString P

------------------------------------------------------------------
--Function to display permutation in array form.
------------------------------------------------------------------

displayPermutation = method()
displayPermutation(Permutation) := Net => (P) -> (
	L := apply(sort keys P.map, k -> (toString(k) || toString(P(k))) | (" "||" "));
	L = {"| " || "| "}  | L | {"|"||"|"};
	horizontalJoin L
)

------------------------------------------------------------------
------------------------------------------------------------------
--Various Constructors for "Permutations"
------------------------------------------------------------------
------------------------------------------------------------------

permutation = method()
------------------------------------------------------------------
--Function to convert permutations to strings
------------------------------------------------------------------

toString Permutation := P -> toString(apply(sort keys P.map,i->(P.map)#i))

------------------------------------------------------------------
-- This converts a hash table to a permutation.
-- Used to construct permutations from lists.
------------------------------------------------------------------

permutation(HashTable) := Permutation => (H) -> 
	new Permutation from hashTable {symbol map => H, symbol cache => new CacheTable}

------------------------------------------------------------------
--This constructs an array from a pair of lists, checking if
--that gives a permutation of {0..n-1}.
------------------------------------------------------------------


permutation(List,List) := Permutation => (M,L) -> (
	if (set L === set M) then( --checks if sets are the same
	     if (unique L === L) and (unique M === M) then ( -- checks if M and L are sets.
		  if (sort L == toList(0..#L-1)) then ( -- checks if M/L are {0..n-1}
		       permutation hashTable apply(#M, i -> M#i=>L#i)
		  )
	     	  else error "Not a permutation of {0..n-1}."
	     )
	     else error "Lists contain nonunique elements."
	)
   	else error "Not a permutation of same set."
)

------------------------------------------------------------------
--Constructs a permutation in array form from a list.
--Input:  L = lower row of (sorted) array form of permutation
------------------------------------------------------------------

permutation(List):= Permutation => L -> (     
	if unique L === L and (sort L == toList(0..#L-1))then
	(
		M := sort L;
		permutation hashTable apply(#M, i -> M#i=>L#i)
	) else error "Not a permutation."
)

------------------------------------------------------------------
-- This constructs a permutation (in array form) from a cycle.
------------------------------------------------------------------

permutation(Cycle) := Permutation => (L) -> (
	S := apply(L, l -> orbitToPermutation l);
	fold(S, (i,j) -> composePermutations(i,j))     
)


----------------------------------------------------------------------------------------
-----
---Cycles
-----
----------------------------------------------------------------------------------------

------------------------------------------------------------------
--Function to display cycles in cycle form.
------------------------------------------------------------------

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

------------------------------------------------------------------
--Function to convert permutations to strings
------------------------------------------------------------------
toString Cycle := (C) -> concatenate apply(C, toCycleString)

------------------------------------------------------------------
------------------------------------------------------------------
--Net for Displaying Cycles
------------------------------------------------------------------
------------------------------------------------------------------
net Cycle := (C) -> toString C


------------------------------------------------------------------
--Functions for Creating Cycles
------------------------------------------------------------------
cycle = method()


------------------------------------------------------------------
--Creates a cycle from a list of lists.
------------------------------------------------------------------
cycle(List):= Cycle => (L)-> (     
	L = apply(L, toList);
	if all(L, l -> l === unique l) and all(flatten L, l -> instance(l,ZZ)) then
		new Cycle from L
	else
		error "Not a set of cycles of integers."
)

------------------------------------------------------------------
--Creates minimal cycle decomposition.
------------------------------------------------------------------

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


------------------------------------------------------------------
-- Converting Cycles to Permutations
------------------------------------------------------------------

----------------------------------------
--Helper Function for permutation(Cycle)
--Converts a list representing one orbit 
--of a cycle decomposition into a permutation.
--This pads a cycle C into a permutation of
-- {0..max element in C}.
---------------------------------------------

orbitToPermutation = (L) -> (
     origH := hashTable flatten apply(#L, i-> L#i => L#((i+1) %#L));
     m := max keys origH;
     identH := hashTable flatten apply(toList(0..m), i-> i => (i+1) % (m+1));
     permutation hashTable apply(keys identH, i -> if member(i,keys origH) then ( i => origH#i ) else (i => i))
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
-- Methods to allow permutations to act on lists, integers, or matrices.
----------------------------------------------------------------------------------------

permute = method()

----------------------------------------------------------------------------------------
--These methods allow permutations to act on lists.
--Require both permutation and list to be of the same length.
----------------------------------------------------------------------------------------

permute(List, Permutation) := List => (L,P) -> toList apply(0..#L-1, m -> L_(P.map#m))
List / Permutation := List => (L,P)-> permute(L,P)
Permutation List := List => (P,L)-> permute(L,P)

---------------------------------------------------------------------
-- This returns a list, permuted by the ith lexicographic permutation.
---------------------------------------------------------------------
permute(List,ZZ) := List => (L,i) -> (
     if 0 <= i and i <= (#L)!-1 then
           permutationByIndex(L, i)
     else
           error("Permutation index (" | i | ") too large for list size (" | #L | ").") 
) 

----------------------------------------------------------------------------------------
--These methods allow permutations to act on indices.
--If a set index is outside of the range of P, then
--the index will return itself, i.e. for P= {3,1,0,2},
--we have P(4)=4.
----------------------------------------------------------------------------------------

permute(ZZ, Permutation) := ZZ => (z,P) -> if member(z,keys P.map) then P.map#z else z
ZZ / Permutation := ZZ => (z,P) -> permute(z,P)
Permutation ZZ := (P,z) -> permute(z,P)

----------------------------------------------------------------------------------------
--Method to permute rows and columns of a matrix.
----------------------------------------------------------------------------------------

permuteRows = method()
permuteRows(Matrix,Permutation):= Matrix => (M,P) -> (
	matrix permute(entries M,P)
)

permuteColumns = method()
permuteColumns(Matrix, Permutation):= Matrix => (M,P) -> (
	matrix transpose permute(entries transpose M,P)
)


Permutation * Matrix := Matrix => (P,M) -> permuteRows(M,P)
Matrix * Permutation := Matrix => (M,P) -> permuteColumns(M,P)

----------------------------------------------------------------------------------------
--Construct permutation matrix of a given P
----------------------------------------------------------------------------------------

permutationMatrix = method()
permutationMatrix(Permutation) := Matrix => (P) -> (
		n := max keys P.map;
		matrix apply(toList(0..n-1), i -> 
			apply(toList(0..n-1), j -> if P(j) === i then 1 else 0))
)

----------------------------------------------------------------------------------------
--Methods to compose permutations or cycles.
----------------------------------------------------------------------------------------

composePermutations = method()
composePermutations(Permutation,Permutation):= Permutation => (P,M) -> (
     permutation hashTable apply(keys M.map | keys P.map, i-> i=> P(M(i)))
     )


Permutation * Permutation := composePermutations

--Product = Concatenation
Cycle ** Cycle := Cycle => (C,D) -> C|D

--Pairwise minimal product
Cycle * Cycle := Cycle => (C,D) -> minimalCycles(C|D)


----------------------------------------------------------------------------------------
--Methods to compute minimal cycles of a permutation P.
----------------------------------------------------------------------------------------

minimalCycles = method()
minimalCycles(Permutation) := Cycle => (P) -> 
	cycle P

----------------------------------------------------------------------------------------
--Converts a cycle or list of cycles into a minimal cycle decomposition.
----------------------------------------------------------------------------------------

minimalCycles(List) := Cycle => (M) -> 
	cycle permutation cycle M

--------------------------------------------------
-- Permutation Inverse
--------------------------------------------------

inverseOfPermutation = method()

inverseOfPermutation(Permutation):= Permutation => (P) -> (
	M := P.map;
	A := hashTable apply(keys M, i-> M#i=>i);
	permutation A
)

--------------------------------------------------
-- Powers of a permutation (positive or negative).
--------------------------------------------------

Permutation ^ ZZ := (P,N)->(
	if N === 0 then return identityPermutation keys P.map;
	if N === 1 then return P;
	if N < 0 then return (inverseOfPermutation P)^(-N);
	if N % 2 === 0 then 
		(P*P)^(floor(N/2))
	else
		P * ((P*P)^(floor(N/2)))
)

----------------------------------------
-- Identity and rotation permutations.
----------------------------------------

identityPermutation = method()
identityPermutation(ZZ) := Permutation => (N) -> permutation toList(0..N-1)
identityPermutation(List) := Permutation => (L) -> permutation(L,L)

isIdentity = method()
isIdentity(Permutation) := Boolean => (P) ->
	all(keys P.map, k -> k == P(k))

rotateRight = method();
rotateRight(ZZ) := Permutation => (N) -> permutation cycle {toList(0..N-1)}

rotateLeft = method();
rotateLeft(ZZ) := Permutation => (N) -> permutation cycle reverse {toList(0..N-1)}


----------------------------------------
-- Permutation Identity
----------------------------------------

Permutation == Permutation := Boolean => (P,S) -> 
	isIdentity((P^-1)*S)


----------------------------------------
-- cartesianProduct helper function
----------------------------------------

cartesianProduct = method()
cartesianProduct(List,List):= List => (H,J) -> (
     flatten apply(H, h-> apply(J, i-> {h,i}))
     )

----------------------------------------------------------------------------------------
--Basic Permutation Operations
----------------------------------------------------------------------------------------

----------------------------------------
-- Generates a random permutation
----------------------------------------
randomPermutation = method()
randomPermutation(ZZ) := Permutation => (N) -> (
	L := toList (0..N-1);
	M := toList random L;
	permutation(L,M)
)


---------------------------------------------------------
-- Returns the bottom row of a permutation in array form.
---------------------------------------------------------

permutationVector = method()
permutationVector(Permutation):= List => (P) -> 
	apply(sort keys P.map, k -> P(k))


---------------------------------------------------------
-- Returns inversion vector of a permutation.
-- The number of elements greater than i to the left of i 
-- in a permutation gives the ith element of the 
-- inversion vector 
---------------------------------------------------------

inversionVector = method()
inversionVector(Permutation):= List => (P) ->(
	if P.cache.?inversionVector then return P.cache.inversionVector;
	L := permutationVector P;
	P.cache.inversionVector = apply(#L, i -> number(take(L, i), p -> p > L#i))
)


permutationFromInversionVector = method();
permutationFromInversionVector(List) := (L) -> (
	N := reverse toList(0..#L-1);
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
	
	
beginDocumentation()


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
			@EM "Permutations"@ is a package for handling permutations in $\sigma\in S_n$, group actions by $S_n$ on various
			objects, and a variety of related combinatorics of posets and the Bruhat order.
		Text
		
		
		Text
		     	The primary way to enter a permutation by hand is via the lower row of the array
			representation of $\sigma$.
		
		Text
		
		
		
		Example
		     	P = permutation {2,4,5,0,1,3,7,6}
			sigma = displayPermutation P
			
///


doc///
     Key
     	Permutation
     Headline
        a class for permutations
     Description
        Text
	   	     This class represents permutations of sets {0,1,...,n-1}.  One way to input a permutation
		     by entering the bottom row of the array form of the permutation.
	Text
	
	
     	Example
	     	  P = permutation {2,0,4,5,1,3,7,6}
		  displayPermutation P
		  peek P
	Text
	
	Text
	     	  Permutations are stored as a hash table of maps from integers in the list to other integers in the list.
		  A second way to enter a permutation then is to take two different orderings of a list of integers, and let the
		  permutation take the first element of the first list to the first element of the second list, and so
		  on.  The displayed permutation vector will have put the keys of the first list
		  into increasing order.
		  
	Text
	
	Example
	     	  M={2,4,0,5,1,3,7,6}
		  L={5,3,2,0,6,4,7,1}
		  permutation(M,L)
		  
	Text
	
	Text
	     	  The permutation is being stored as a map containing a set of keys (the base set L) 
		  and where they go under the permutation.  We can have these permutations act on a list 
		  in one of two key ways.  We take an element in position i of our list to the position
		  P(i) in the image.
		  
	Text
	
	Example
	     	  P=permutation{5,4,3,2,1,0}
		  peek P
		  S={3,4,0,5,1,2}
		  permute(S,P)
		  T={cat, dog, horse, 1,2,3}
		  permute(T,P)
	Text
     	
	Text
	      	  One specific additional function included with Permutations is applying a permutation 
		  to the rows or columns of a matrix M.
	Text
	
	Example
	      	  M=matrix{{1,2,3,4,5,6},{7,8,9,10,11,12},{13,14,15,16,17,18}}
		  P1=permutation{3,2,1,5,0,4}
		  P2=permutation{2,1,0}
		  permuteColumns(M,P1)
		  M*P1
		  permuteRows(M,P2)
		  P2*M
	Text
		  
     SeeAlso
          permutation

///

doc ///
	Key
     		permutation
		(permutation, List)
		(permutation, List, List)
		(permutation, HashTable)
	Headline
     		returns a permutation of a list
	Usage
     		P = permutation L
		P = permutation(M,L)
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
      		P: Permutation
			a hashtable with keys corresponding to elements of a list, and values describing 
			where the keys go under the permutation
	Description
      		Text
			This method returns a particular permutation of a set L.
		Example
	   		M={1,2,3,4,5,0,6,7}
	       		L={5,3,2,6,0,4,7,1}
			permutation L
			permutation(M,L)
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
	       Given any list of lists of unique integers, we can create a cycle permuting
	       the elements.  We can also create a cycle from a permutation via cycle.
	  Example
     	       C=cycle{{5,3,1,0},{6,2},{10,9,8,7,4}}
     	       cycle permutation {3,7,5,1,4,2,8,9,0,6,10}
	       D=cycle{{5,6,1,0},{4,5,2},{1,4,10,9}}
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
	       Permute will act on an (ordered) list L by permuting the elements.
	  Example
	       P=permutation {4,5,1,2,3,0}
	       P.map
	       L={A,B,1,2,C,4}
	       permute(L,P)
	       P(L)
	  Text
	       Note that a permutation P will ONLY act on a list of the same size as P.
     SeeAlso

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
	       The lower row in the (sorted) permutation array is the permutation vector.
	  Example
	       P=permutation({3,2,1,4,5,0},{4,3,0,1,2,5})
	       K={3,2,1,4,5,0}
	       B=sort K
	  Text
	       The list of values of these keys, in order, returns the permutation vector.  It is already
	       displayed as the net of a permutation.
	  Example
	       P=permutation({3,2,1,4,5,0},{4,3,0,1,2,5})
	       B=sort {3,2,1,4,5,0}
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
	       Given any set of cycles C, this function returns the minimal cycle
	       decomposition of C as a permutation.
	  Example
	       C = cycle({{0,4,2,1},{1,2,3},{4,5,10}})
	       C' = minimalCycles C
     SeeAlso
///
