-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- ITERATIVE COMBINATORIAL GENERATORS ------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Copyright 2012 Zach Teitler
--
-- NOT for public distribution at this time.
-- (okay to distribute among participants of WFU workshop
--  and M2 developers, for experimental use only; please
--  do not distribute more widely than that)
--------------------------------------------------------------------------------

newPackage(
  "IterativeCombinatorialGenerators",
      Version => "0.1",
      Date => "August 8, 2012",
      Authors => {
       {Name => "Zach Teitler"}
       },
      Headline => "generators for some combinatorial objects",
      DebuggingMode=>false
      )

export {
  nextSubset,
  prevSubset,
  nextPartition,
  prevPartition,
  nextPermutation,
  prevPermutation,
  Size
  }



-- nextSubset
-- Given a subset of {0..n-1}, returns another one.
-- The iterator starts at {} and ends at {0..n-1}.
-- If S is a set with n elements, you can get subsets of S via take(S,P) where P is from this routine.
-- Based on code by Brian Duggan <bduggan@matatu.org> posted on CPAN at
--   http://search.cpan.org/~bduggan/Algorithm-ChooseSubsets-0.02/ChooseSubsets.pm
-- retrieved August 7, 2012
-- and an answer by runnerup posted on StackOverflow at
--   http://stackoverflow.com/questions/7794638/to-generate-a-subset-of-size-n-one-by-one-to-reduce-the-complexity
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
--
-- Desired behavior:
--   subsets(<0,k) = error for all k
--   subsets(0,<0) = {}
--   subsets(0,0) = {{}}
--   subsets(0,>0) = {}
--   subsets(>0,<0) = {}
--   subsets(>0,0) = {{}}
--   subsets(>0,>0) = usual list of subsets ({} if k>n)
nextSubset = method(Options=>{Size=>null})
nextSubset ZZ := o -> (n) -> (
  if n < 0 then error "size of set must be greater than or equal to zero"
  else if o.Size === null or o.Size == 0 then return {}
  else if n == 0 or o.Size > n or o.Size < 0 then return null
  else return new List from (0..(o.Size-1));
)
nextSubset (ZZ,Nothing) := o -> (n,P) -> null
nextSubset (ZZ,List) := o -> (n,P) -> (
  if (o.Size =!= null) and (o.Size != #P) then
    if (n >= 0 and o.Size >= 0) then (
      error "current subset not the expected size";
    ) else ( -- n < 0 or o.Size < 0
      return null;
    );
  
  if o.Size =!= null then (
    -- Last one?
    if (o.Size <= 0) or (P#0 == n-o.Size) then return null;
    
    -- Find the position to change.
    p := 0;
    while ( p < #P-1 and (P#p)+1 == P#(p+1) ) do p = p+1;
    P = replace(p,(P#p)+1,P);
    while ( (p = p-1) >= 0 ) do P = replace(p,p,P);
    return P;
    
  ) else (
  
    -- o.Size === null means generate subsets of all sizes.
    -- To conform with Macaulay2's existing 'subsets',
    -- generate in binary counting order.
    
    index := sum(P, i -> 2^i) + 1;
    if ( index >= 2^n ) then (
      return null;
    ) else (
      return (for i from 0 to n-1 list if (2^i & index != 0) then i else continue);
    );
  );
)

-- prevSubset
-- opposite of nextSubset
-- given a subset of {0..n-1}, return the previous one
prevSubset = method(Options=>{Size=>null})
prevSubset ZZ := o -> (n) -> (
  if n < 0 then error "size of set must be greater than or equal to zero"
  else if o.Size === null then return new List from (0..n-1)
  else if o.Size == 0 then return {}
  else if n == 0 or o.Size > n or o.Size < 0 then return null
  else return new List from ((n-o.Size)..(n-1));
)
prevSubset (ZZ,Nothing) := o -> (n,P) -> null
prevSubset (ZZ,List) := o -> (n,P) -> (
  if (o.Size =!= null) and (o.Size != #P) then
    if (n >= 0 and o.Size >= 0) then (
      error "current subset not the expected size";
    ) else ( -- n < 0 or o.Size < 0
      return null;
    );
  
  if o.Size =!= null then (
    -- Find the position to change
    p := 0;
    while ( p <= #P-1 and P#p == p ) do p = p+1;
    if ( p == #P ) then return null;
    P = replace(p,(P#p)-1,P);
    while ( (p=p-1) >= 0 ) do P = replace(p,(P#(p+1))-1,P);
    return P;
    
  ) else (
  
    -- o.Size === null means generate subsets of all sizes.
    -- To conform with Macaulay2's existing 'subsets',
    -- generate in binary counting order.
    
    index := sum(P, i -> 2^i) - 1;
    if ( index < 0 ) then (
      return null;
    ) else (
      return (for i from 0 to n-1 list if (2^i & index != 0) then i else continue);
    );
  );
)

-- nextPartition
-- Given a partition of n written in non-increasing order,
-- returns another one. The iterator starts at {n} and ends at {1,..,1}.
-- Based on code by blokhead posted on PerlMonks at
--   http://www.perlmonks.org/?node_id=621859
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
--
-- "rev lex" order of http://oeis.org/wiki/Orderings_of_partitions
--
-- nextPartition(n,k): partition of n with blocks of size at most k
-- 
-- Desired behavior:
--   partitions(<0) = partitions(<0,k) = {}
--   partitions(0) = partitions(0,k) = {Partition{}}
--   partitions(>0,<0) = error "recursion limit of 300 exceeded"
--   partitions(>0,0) = {}
--   partitions(>0) = partitions(>0,>0) = usual list of partitions
nextPartition = method()
nextPartition ZZ := n -> (
  if n < 0 then (
    return null;
  ) else if n == 0 then (
    return new Partition from {};
  ) else (
    return new Partition from {n};
  );
)
nextPartition (ZZ,ZZ) := (n,k) -> (
  if n < 0 then (
    return null;
  ) else if n == 0 then (
    return new Partition from {};
  ) else if k < 0 then (
    error "cannot partition a positive integer into parts with negative size";
  ) else if k == 0 then (
    return null;
  ) else (
    return new Partition from select(flatten append( floor(n/k):k , n % k ), i->i!=0);
  );
)
nextPartition Nothing := P -> null
nextPartition Partition := P -> (
  PL := new List from P;
  -- Collect all the trailing 1s
  x := 0;
  while #PL > 0 and PL#-1 == 1 do (x = x+1; PL = drop(PL,-1););
  if #PL == 0 then return null;
  -- Collect 1 from the rightmost remaining guy
  PL = replace(-1,(PL#-1)-1,PL);
  x = x+1;
  -- re-distribute the collected amount in increments of PL#-1
  lastpiece := PL#-1;
  while ( x > lastpiece ) do (
    PL = append(PL,lastpiece);
    x = x - lastpiece;
  );
  PL = append(PL,x);
  return new Partition from PL;
)

-- prevPartition
-- opposite of nextPartition
-- given an integer partition of n, return the previous one in revlex order
-- i.e., next one in lex order
-- http://www.site.uottawa.ca/~ivan/F49-int-part.pdf
prevPartition = method()
prevPartition ZZ := n -> (
  if n < 0 then (
    return null;
  ) else if n == 0 then (
    return new Partition from {};
  ) else (
    return new Partition from n:1;
  );
)
prevPartition (Nothing) := P -> null
prevPartition Partition := P -> (
  if #P <= 1 then return null;
  
  T := tally toList P;
  U := new MutableHashTable;
  minpart := min keys T;
  if T#minpart > 1 then (
    -- collect & remove T#minpart parts 
    -- add a part of size minpart+1
    -- add (T#minpart - 1)*minpart-1 1's
    for k in keys T do (
      if k > minpart+1 then U#k = T#k;
    );
    
    if T#?(minpart+1) then U#(minpart+1) = (T#(minpart+1))+1 else U#(minpart+1) = 1;
    
    U#1 = (T#minpart - 1)*minpart-1;
  ) else (
    -- collect & remove T#minpart part and T#secondminpart parts
    -- add a part of size secondminpart+1
    -- add (T#minpart)*minpart+(T#secondminpart-1)*secondminpart-1 1's
    secondminpart := (sort(keys T))#1;
    for k in keys T do (
      if k > secondminpart+1 then U#k = T#k;
    );
    
    if T#?(secondminpart+1) then U#(secondminpart+1) = (T#(secondminpart+1))+1 else U#(secondminpart+1) = 1;
    
    U#1 = (T#minpart)*minpart+(T#secondminpart-1)*secondminpart-1;
  );
  return partitionFromTally U;
)

partitionFromTally = (T) -> (
  new Partition from rsort flatten apply(keys T, k -> toList(T#k:k))
)


-- nextPermutation
-- Given a permutation of a list, returns another one.
-- The iterator starts at {0..n-1} and ends at {n-1..0}.
-- The code can handle lists with repetition, e.g., {1,1,2,2}
-- and it can handle any entries that can be compared
-- with <, e.g., {a,b,c}
-- however this functionality is NOT documented and NOT maintained
-- Based on code by tye posted on PerlMonks at
--   http://www.perlmonks.org/?node_id=29374
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
-- also helpful:
-- http://stackoverflow.com/questions/11483060/stdnext-permutation-implementation-explanation
nextPermutation = method()
nextPermutation ZZ := n -> new List from (0..n-1)
nextPermutation Nothing := P -> null
nextPermutation List := P -> (
  -- Find last item not in reverse-sorted order
  i := #P-2;
  while i >= 0 and P#i >= P#(i+1) do i = i-1;
  -- If complete reverse sort, we are done!
  if i < 0 then return null;
  -- Re-sort the reversely-sorted tail of the list:
  if P#(i+1) > P#-1 then
    P = join(take(P,{0,i}),reverse take(P,{i+1,#P-1}));
  -- Find next item that will make us "greater":
  j := i+1;
  while ( P#i >= P#j ) do j = j+1;
  -- Swap:
  return switch(i,j,P);
)

-- prevPermutation
-- opposite of nextPermutation
-- given a permutation, return the previous one
prevPermutation = method()
prevPermutation ZZ := n -> reverse new List from (0..(n-1))
prevPermutation Nothing := P -> null
prevPermutation List := P -> (
  -- Find last item not in sorted order
  i := #P-2;
  while i >= 0 and P#i <= P#(i+1) do i = i-1;
  -- If complete sort, we are done
  if i < 0 then return null;
  -- Find last item greater than P#i
  j := #P-1;
  while ( P#i < P#j ) do j = j-1;
  -- Swap:
  P = switch(i,j,P);
  -- Re-sort the tail of the list:
  P = join(take(P,{0,i}),reverse take(P,{i+1,#P-1}));
  return P;
)




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

document {
  Key => { IterativeCombinatorialGenerators },
  Headline => "Iterative generators for combinatorial objects",
  PARA { EM "IterativeCombinatorialGenerators", " is a package for ",
  "generating combinatorial objects including partitions, permutations, ",
  "and subsets. Objects are generated one by one: enter in an object ",
  "to get back the next one." },
  PARA { "The primary purpose is for sums or other operations indexed by ",
  "partitions, permutations, or subsets, in which it does not make sense ",
  "to generate the full list and store it all in memory. ",
  "Rather, one may initialize a variable with the first partition, ",
  "permutation, or subset, and repeatedly (with a for loop) iterate ",
  "the 'next' functions to visit all of the partitions, permutations, or subsets ",
  "exactly once each." },
  PARA { "One may also go backward with 'prev' functions." }
}

document {
  Key => {
    nextSubset,
    (nextSubset, ZZ, List),
    (nextSubset, ZZ, Nothing),
    (nextSubset, ZZ),
    Size,
    [nextSubset, Size]
  },
  Headline => "Generate the next subset",
  Usage => "nextSubset(n,S) or nextSubset(n)",
  Inputs => {
    "n" => ZZ => "the size of the containing set",
    "S" => List => "list of elements of the current subset",
  },
  Outputs => {
    List => "the next subset after S"
  },
  CODE "nextSubset(n,S)", " returns the next subset of ",
  TEX ///$\{0,\dots,n-1\}$///, " after S ",
  "in binary counting order ",
  "(the same order used by Macaulay2's ", TO "subsets", "). ",
  CODE "nextSubset(n)", " returns the first subset, namely ",
  TEX ///$\{\}$///, ", the empty set.",

  EXAMPLE lines ///
    S = nextSubset 5
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = {1,3,4};
    S = nextSubset(5,S)
  ///,
    
  "If S is the last subset ",
  "(the whole set ", TEX ///$\{0,\dots,n-1\}$///, ") then ",
  CODE "nextSubset(n)", " returns ", CODE "null", " and subsequent ",
  "calls continue to return ", CODE "null", ". ",
  
  EXAMPLE lines ///
    Z = {0,1,2,3,4}; -- the last subset
    nextSubset(5,Z)
  ///,

  "The optional argument Size restricts the size of the subsets. ",
  
  EXAMPLE lines ///
    T = nextSubset(5,Size=>3)
    T = nextSubset(5,T,Size=>3)
    T = nextSubset(5,T,Size=>3)
  ///,
  
  SeeAlso => { prevSubset, subsets }
}

document {
  Key => {
    prevSubset,
    (prevSubset, ZZ, List),
    (prevSubset, ZZ, Nothing),
    (prevSubset, ZZ),
    [prevSubset, Size]
  },
  Headline => "Generate the previous subset",
  Usage => "prevSubset(n,S) or prevSubset(n)",
  Inputs => {
    "n" => ZZ => "the size of the containing set",
    "S" => List => "list of elements of the current subset",
  },
  Outputs => {
    List => "the previous subset before S"
  },
  CODE "prevSubset(n,S)", " returns the previous subset of ",
  TEX ///$\{0,\dots,n-1\}$///, " after S. ",
  CODE "prevSubset(n)", " returns the last subset, namely ",
  TEX ///$\{0,\dots,n-1\}$///,
  "the whole set.",
  
  EXAMPLE lines ///
    S = prevSubset 5
    S = prevSubset(5,S)
    S = prevSubset(5,S)
    S = {1,3,4};
    S = prevSubset(5,S)
  ///,
  
  "If S is the last subset ",
  "(the empty set ", TEX ///$\{\}$///, ") then ",
  CODE "prevSubset(n)", " returns ", CODE "null", " and subsequent ",
  "calls continue to return ", CODE "null", ". ",
  
  EXAMPLE lines ///
    Z = {}; -- the first subset
    prevSubset(5,Z)
  ///,
  
  "The optional argument Size restricts the size of the subsets. ",

  EXAMPLE lines ///
    T = prevSubset(5,Size=>3)
    T = prevSubset(5,T,Size=>3)
    T = prevSubset(5,T,Size=>3)
  ///,
  
  SeeAlso => { nextSubset, subsets }
}

document {
  Key => {
    nextPartition,
    (nextPartition, Partition),
    (nextPartition, Nothing),
    (nextPartition, ZZ),
    (nextPartition, ZZ, ZZ)
  },
  Headline => "Generate the next partition",
  Usage => "nextPartition(P) or nextPartition(n) or nextPartition(n,k)",
  Inputs => {
    "P" => Partition => "a partition"
  },
  Outputs => {
    Partition => {}
  },
  "Given a partition of a positive integer, ",
  "returns the next partition of the integer if there is one, ",
  "or null otherwise. ",
  "It starts at the partition with one part and ends at the partition ",
  "of all ones. ",
  
  EXAMPLE lines ///
    P = nextPartition 5
    P = nextPartition P
    P = nextPartition P
    Z = new Partition from {1,1,1,1,1}; -- the last partition of 5
    nextPartition Z
  ///,
  
  "Given two integers n and k, returns the first partition of n ",
  "into integers less than or equal to k. ",
  "Subsequent calls to nextPartition maintain this property ",
  "(all parts less than or equal to k). ",
  
  EXAMPLE lines ///
    T = nextPartition(10,3)
    T = nextPartition T
    T = nextPartition T
  ///,
  
  SeeAlso => { prevPartition, partitions }
}


document {
  Key => {
    prevPartition,
    (prevPartition, Partition),
    (prevPartition, Nothing),
    (prevPartition, ZZ),
  },
  Headline => "Generate the previous partition",
  Usage => "prevPartition(P) or prevPartition(n)",
  Inputs => {
    "P" => Partition => "a partition"
  },
  Outputs => {
    Partition => {}
  },
  "Given a partition of a positive integer, ",
  "returns the previous partition of the integer if there is one, ",
  "or null otherwise. ",
  "It starts at the partition of all ones and ends at the partition ",
  "with one part. ",
  
  EXAMPLE lines ///
    P = prevPartition 5
    P = prevPartition P
    P = prevPartition P
    Z = new Partition from {5}; -- the first partition of 5
    prevPartition Z
  ///,
  
  SeeAlso => { nextPartition, partitions }
}


document {
  Key => {
    nextPermutation,
    (nextPermutation, List),
    (nextPermutation, Nothing),
    (nextPermutation, ZZ),
  },
  Headline => "Generate the next permutation",
  Usage => "nextPermutation(P) or nextPermutation(n)",
  Inputs => {
    "P" => List => "a permutation of {0,...,n-1}"
  },
  Outputs => {
    List => {}
  },
  "Given a permutation of {0,...,n-1}, ",
  "returns the next permutation if there is one, ",
  "or null otherwise. ",
  "It starts at the ordered permutation {0,...,n-1} ",
  "and ends at the antiordered permutation {n-1,...,0}. ",
  
  EXAMPLE lines ///
    P = nextPermutation 5
    P = nextPermutation P
    P = nextPermutation P
    Z = {4,3,2,1,0} -- the last permutation of {0..4}
    nextPermutation Z
  ///,
  
  SeeAlso => { prevPermutation, permutations }
}


document {
  Key => {
    prevPermutation,
    (prevPermutation, List),
    (prevPermutation, Nothing),
    (prevPermutation, ZZ),
  },
  Headline => "Generate the previous permutation",
  SYNOPSIS (
       Usage => "prevPermutation P",
       Inputs => {
    	    "P" => List => "a permutation of {0,...,n-1}, for some n"
  	    },
       Outputs => {
    	    List => {"the previous permutation of {0,...,n-1}, or ", TO "null", ", if there is none, which is
		 the case if ", TT "P", " is {0,...,n-1}"}
  	    }
       ),
  SYNOPSIS (
       Usage => "prevPermutation n",
       Inputs => {
    	    "n" => List => {"the last permutation of {0,...,n-1}, which is {n-1,...,0}"}
  	    },
       Outputs => {
    	    List => {}
  	    }
       ),
  EXAMPLE lines ///
    P = prevPermutation 5
    P = prevPermutation P
    P = prevPermutation P
    Z = {0,1,2,3,4} -- the first permutation of {0..4}
    prevPermutation Z
  ///,
  
  SeeAlso => { nextPermutation, permutations }
}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{*
  nextSubset,
  prevSubset,
*}

TEST ///
  S = nextSubset(5);
  assert( S == {} );
  S = nextSubset(5,S);
  assert( S == {0} );
  S = nextSubset(5,{0,1,2,3,4});
  assert( S === null );
  S = nextSubset(5,S);
  assert( S === null );
///

TEST ///
  for n from 0 to 12 do (
    S = nextSubset(n);
    subsetList = {};
    while ( S =!= null ) do (
      subsetList = append(subsetList,S);
      S = nextSubset(n,S);
    );
    assert( subsetList === subsets(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from -2 to n+2 do (
      S = nextSubset(n,Size=>k);
      subsetList = {};
      while ( S =!= null ) do (
        subsetList = append(subsetList,S);
        S = nextSubset(n,S,Size=>k);
      );
      assert( subsetList === subsets(n,k) );
    );
  );
///

TEST ///
  assert( (try nextSubset(-1)) === null );
  assert( (try nextSubset(-1,Size=>-1)) === null );
  assert( (try nextSubset(-1,Size=>0)) === null );
  assert( (try nextSubset(-1,Size=>1)) === null );
///



TEST ///
  S = prevSubset(5);
  assert( S == {0,1,2,3,4} );
  S = prevSubset(5,S);
  assert( S == {1,2,3,4} );
  S = prevSubset(5,{});
  assert( S === null );
  S = prevSubset(5,S);
  assert( S === null );
///

TEST ///
  for n from 0 to 12 do (
    S = prevSubset(n);
    subsetList = {};
    while ( S =!= null ) do (
      subsetList = append(subsetList,S);
      S = prevSubset(n,S);
    );
    assert( subsetList === reverse subsets(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from -2 to n+2 do (
      S = prevSubset(n,Size=>k);
      subsetList = {};
      while ( S =!= null ) do (
        subsetList = append(subsetList,S);
        S = prevSubset(n,S,Size=>k);
      );
      assert( subsetList === reverse subsets(n,k) );
    );
  );
///

TEST ///
  assert( (try prevSubset(-1)) === null );
  assert( (try prevSubset(-1,Size=>-1)) === null );
  assert( (try prevSubset(-1,Size=>0)) === null );
  assert( (try prevSubset(-1,Size=>1)) === null );
///


{*
  nextPartition,
  prevPartition,
*}

TEST ///
  S = nextPartition(5);
  assert( S === new Partition from {5} );
  S = nextPartition(S);
  assert( S === new Partition from {4,1} );
  S = nextPartition(new Partition from {1,1,1,1,1});
  assert( S === null );
  S = nextPartition(S);
  assert( S === null );
///

TEST ///
  for n from 0 to 12 do (
    S = nextPartition(n);
    partitionList = {};
    while ( S =!= null ) do (
      partitionList = append(partitionList,S);
      S = nextPartition(S);
    );
    assert( partitionList === partitions(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from 1 to n+2 do (
      S = nextPartition(n,k);
      partitionList = {};
      while ( S =!= null ) do (
        partitionList = append(partitionList,S);
        S = nextPartition(S);
      );
      assert( partitionList === partitions(n,k) );
    );
  );
///

TEST ///
  assert( nextPartition(-1) === null );
  assert( nextPartition(-1,-1) === null );
  assert( nextPartition(-1,0) === null );
  assert( nextPartition(-1,1) === null );
  assert( nextPartition(0) === new Partition from {} );
  assert( nextPartition(0,-1) === new Partition from {} );
  assert( nextPartition(0,0) === new Partition from {} );
  assert( nextPartition(0,1) === new Partition from {} );
  assert( (try nextPartition(1,-1)) === null );
  assert( nextPartition(1,0) === null );
///


TEST ///
  S = prevPartition(5);
  assert( S === new Partition from 5:1 );
  S = prevPartition(S);
  assert( S === new Partition from {2,1,1,1} );
  S = prevPartition(new Partition from {5});
  assert( S === null );
  S = prevPartition(S);
  assert( S === null );
///

TEST ///
  for n from 0 to 12 do (
    S = prevPartition(n);
    partitionList = {};
    while ( S =!= null ) do (
      partitionList = append(partitionList,S);
      S = prevPartition(S);
    );
    assert( partitionList === reverse partitions(n) );
  );
///

TEST ///
  assert( prevPartition(-1) === null );
  assert( prevPartition(0) === new Partition from {} );
///


{*
 nextPermutation,
  prevPermutation,
*}

TEST ///
  P = nextPermutation(5);
  assert( P == {0,1,2,3,4} );
  P = nextPermutation(P);
  assert( P == {0,1,2,4,3} );
  P = nextPermutation({4,3,2,1,0});
  assert( P === null );
  P = nextPermutation(P);
  assert( P === null );
///

TEST ///
  for n from 0 to 7 do (
    P = nextPermutation(n);
    permutationList = {};
    while ( P =!= null ) do (
      permutationList = append(permutationList,P);
      P = nextPermutation(P);
    );
    assert( permutationList === permutations(n) );
  );
///


TEST ///
  P = prevPermutation(5);
  assert( P == {4,3,2,1,0} );
  P = prevPermutation(P);
  assert( P == {4,3,2,0,1} );
  P = prevPermutation({0,1,2,3,4});
  assert( P === null );
  P = prevPermutation(P);
  assert( P === null );
///

TEST ///
  for n from 0 to 7 do (
    S = prevPermutation(n);
    permutationList = {};
    while ( S =!= null ) do (
      permutationList = append(permutationList,S);
      S = prevPermutation(S);
    );
    assert( permutationList === reverse permutations(n) );
  );
///


end

--------------------------------------------------------------------------------


restart
loadPackage "IterativeCombinatorialGenerators"
check oo
installPackage oo
