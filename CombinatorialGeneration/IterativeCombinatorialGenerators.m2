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
nextSubset = method(Options=>{Size=>null})
nextSubset ZZ := o -> (n) -> (
  if o.Size === null or o.Size == 0 then return {}
  else if o.Size <= n then return new List from (0..(o.Size-1))
  else return null;
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
    lastone := (#P == 0) or (P#0 == n-#P);
    if lastone then return null;
    
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
  if o.Size === null or o.Size == 0 then return new List from (0..(n-1))
  else if o.Size <= n then return new List from ((n-o.Size)..(n-1))
  else return null;
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
nextPartition = method()
nextPartition ZZ := n -> new Partition from {n}
nextPartition (ZZ,ZZ) := (n,k) ->
  new Partition from select(flatten append( floor(n/k):k , n % k ), i->i!=0)
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
-- given an integer partition of n, return the previous one
prevPartition = method()
prevPartition ZZ := n -> new Partition from n:1
prevPartition (Nothing) := P -> null
prevPartition Partition := P -> (
  C := nextPartition conjugate P;
  if C === null then return null else return conjugate C;
)


-- nextPermutation
-- Given a permutation of a list, returns another one.
-- The iterator starts at {0..n-1} and ends at {n-1..0}.
-- It can handle lists with repetition, e.g., {1,1,2,2}
-- and it can handle any entries that can be compared
-- with <, e.g., {a,b,c}.
-- Based on code by tye posted on PerlMonks at
--   http://www.perlmonks.org/?node_id=29374
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
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
  C := nextPermutation reverse P;
  if C === null then return null else return reverse C;
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
  Usage => "prevPermutation(P) or prevPermutation(n)",
  Inputs => {
    "P" => List => "a permutation of {0,...,n-1}"
  },
  Outputs => {
    List => {}
  },
  "Given a permutation of {0,...,n-1}, ",
  "returns the previous permutation if there is one, ",
  "or null otherwise. ",
  "It starts at the antiordered permutation {n-1,...,0} ",
  "and ends at the ordered permutation {0,...,n-1}. ",
  
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
  needsPackage("IterativeCombinatorialGenerators");
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
  for n from -1 to 12 do (
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
  for n from -1 to 12 do (
    for k from -1 to n+1 do (
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
  needsPackage("IterativeCombinatorialGenerators");
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
  for n from -1 to 12 do (
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
  for n from -1 to 12 do (
    for k from -1 to n+1 do (
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

{*
  nextPartition,
  prevPartition,
*}

TEST ///
  needsPackage("IterativeCombinatorialGenerators");
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
  for n from -1 to 12 do (
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
  for n from -1 to 12 do (
    for k from -1 to n+1 do (
      S = nextPartition(n,k);
      partitionList = {};
      while ( S =!= null ) do (
        partitionList = append(partitionList,S);
        S = nextPartition(n,S);
      );
      assert( partitionList === partitions(n,k) );
    );
  );
///


{*
 nextPermutation,
  prevPermutation,
*}


end

--------------------------------------------------------------------------------


restart
loadPackage "IterativeCombinatorialGenerators"
check oo
installPackage oo
