-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- COMBINATORIAL ITERATION -----------------------------------------------------
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
  "CombinatorialIteration",
      Version => "0.1",
      Date => "August 8, 2012",
      Authors => {
        {
          Name => "Zach Teitler",
          Email => "zteitler@member.ams.org",
          HomePage => "http://math.boisestate.edu/~zteitler/"
        }
      },
      Headline => "generators for some combinatorial objects",
      DebuggingMode=>false
      )

export {
  nextSubset,
  prevSubset,
  Size,
  nextPartition,
  prevPartition,
  nextPermutation,
  prevPermutation,
  YoungDiagram,
  Filling,
  shape,
  isStandardTableau,
  nextStandardTableau,
  prevStandardTableau,
  collectIterations,
  CollectInitializer
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
nextSubset (ZZ,Nothing) := o -> (n,P) -> nextSubset(n,Size=>o.Size)
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
prevSubset (ZZ,Nothing) := o -> (n,P) -> prevSubset(n,Size=>o.Size)
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




YoungDiagram = new Type of BasicList

net YoungDiagram := D -> netList({apply(toList D, c->stack apply(c, e->net "."))},
  Boxes=>false);

conjugate YoungDiagram := D ->
  new YoungDiagram from apply(0..<(D#0), i -> (
    # select( D , r -> r > i )
  ))



Filling = new Type of BasicList

net Filling := T -> netList {apply(toList T, c->stack apply(c, e->net e))};

conjugate Filling := (T) -> (
  a := #T#0;
  new Filling from apply(0..a-1, i -> (
    -- the i th element of each list (until length is too big)
    for j from 0 to #T-1 when #T#j > i list T#j#i
  ))
)

Filling _ List := (T,l) -> new Filling from (toList T)_l

Filling ^ List := (T,l) -> new Filling from (toList conjugate T)_l

shape = method();
shape Filling := T -> new YoungDiagram from apply(toList T, i -> #i)
shape List := L -> new YoungDiagram from L
shape Partition := P -> new YoungDiagram from toList P

isIncreasing = L -> all(#L-1, i -> (L#i < L#(i+1)))

isNonDecreasing = L -> all(#L-1, i -> (L#i <= L#(i+1)))

isDecreasing = L -> all(#L-1, i -> (L#i > L#(i+1)))

isNonIncreasing = L -> all(#L-1, i -> (L#i >= L#(i+1)))

isStandardTableau = L -> (
  return (
    all(L,c -> isIncreasing c) and
    all(conjugate L, r -> isIncreasing r)
  )
)

fillingFromPermutation = (shape,perm) -> (
  L := {};
  for c in toList shape do (
    L = append(L,take(perm,c));
    perm = drop(perm,c);
  );
  return new Filling from L;
)

permutationFromFilling = T -> flatten toList T

-- For a filling T and integer j, which column of T contains j
whichColumn = (T,j) -> (
  col := 0;
  while not member(j, T#col) do col = col + 1;
  return col;
)

-- For a filling T and integer j, which row of T contains j
whichRow = (T,j) -> whichColumn(conjugate T, j)

nextStandardTableau = method()
nextStandardTableau(Filling) := (T) -> (
  n := sum toList shape T;
  -- Find element that needs to be moved: least j such that row(j) < row(j-1)
  j := 1;
  rowprev := 0; -- this is whichRow(T,0), or else T is an illegal filling
  while ( j < n and rowprev <= (rowcurr := whichRow(T,j)) ) do (
    j = j+1;
    rowprev = rowcurr;
  );
  if j >= n then return null;
  
  -- determine the shape of subtableau to be changed: subtableau of entries <= j
  subdiagram := apply(
    apply(toList T, c -> select(c, x -> (x <= j))),
    c -> #c);
  
  -- find corner square closest to j to j's left:
  -- rightmost column strictly longer than j's current column
  whichcol := whichColumn(T,j);
  currcollen := subdiagram#whichcol;
  while( subdiagram#whichcol == currcollen ) do whichcol = whichcol - 1;
  
  -- remove next corner (bottom) square left of j
  -- fill in remaining subdiagram with 1..j-1 in lex order
  subsubdiagram := replace(whichcol, subdiagram#whichcol - 1, subdiagram);
  newsubtableau := nextStandardTableau(subsubdiagram);
  
  -- add j to bottom of column it's moved into
  newsubtableau = replace(whichcol, append(newsubtableau#whichcol, j), toList newsubtableau);
  
  -- now, put back all the rest of the diagram (entries > j)
  newtableau := apply(# toList T, c -> (
    flatten join(newsubtableau#c, drop(T#c,subdiagram#c))
  ));
  
  return new Filling from newtableau;
)
nextStandardTableau(YoungDiagram) := D -> (
  n := sum toList D;
  perm := nextPermutation n;
  return fillingFromPermutation(D,perm);
)
nextStandardTableau(Partition) :=
nextStandardTableau(List) := L ->
  nextStandardTableau new YoungDiagram from L
nextStandardTableau(Nothing) := n -> null


prevStandardTableau = method()
prevStandardTableau(Filling) := T -> (
  Tnext' := nextStandardTableau(conjugate T);
  if Tnext' === null then return null else return conjugate Tnext';
)
prevStandardTableau(YoungDiagram) := D ->
  conjugate(nextStandardTableau(conjugate D))
prevStandardTableau(Partition) := 
prevStandardTableau(List) := L ->
  prevStandardTableau new YoungDiagram from L
prevStandardTableau(Nothing) := n -> null



collectIterations = method( Options => {LengthLimit => 10000, CollectInitializer => false} )
collectIterations(Function,Thing) := o -> (f,initializer) -> (
  local l;
  if o.CollectInitializer then l = 1 else l = 0;
  t := f initializer;
  L :=
    while ( t =!= null and l < o.LengthLimit ) list (
      if t =!= null then t
    ) do (
      l = l + 1;
      t = f t;
    );
  if o.CollectInitializer then L = prepend(initializer,L);
  return L;
)
collectIterations(Function) := o -> f ->
  collectIterations(f, null, LengthLimit=>o.LengthLimit, CollectInitializer=>false)
  

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

document {
  Key => { CombinatorialIteration },
  Headline => "Iterative generators for combinatorial objects",
  PARA {
    EM "CombinatorialIteration",
    " is a package for generating combinatorial objects including 
    partitions, permutations, subsets, and standard tableaux.
    Objects are generated one by one: enter in an object to get the next one."
  },
  PARA {
    "The primary purpose is to traverse a list of
    partitions, permutations, subsets, or tableaux
    without generating and storing the full list.
    This arises in, for example, sums indexed by partitions;
    iteration allows one to compute the terms of the sum one-by-one
    by initializing a variable with the first partition
    and repeatedly (with a for loop) iterating
    the 'next' function to visit all of the partitions
    exactly once each."
  },
  PARA {
    "One may also go backward with 'prev[ious]' functions,
    reversing the order of traversal of the 'next' functions."
  },
  SUBSECTION { "References" },
  PARA {
    "[NW] Nijenhuis, Albert; Wilf, Herbert S. ",
    EM "Combinatorial algorithms.",
    "Second edition. 1978."
  }
}

document {
  Key => {
    nextSubset,
    (nextSubset, ZZ, List),
    (nextSubset, ZZ, Nothing),
    (nextSubset, ZZ),
    prevSubset,
    (prevSubset, ZZ, List),
    (prevSubset, ZZ, Nothing),
    (prevSubset, ZZ),
  },
  Headline => "Generate the next and previous subsets",
  SYNOPSIS {
    Usage => "nextSubset(n,S)",
    Inputs => {
      "n" => ZZ => "the size of the containing set",
      "S" => List => "list of elements of a subset of {0..n-1}",
    },
    Outputs => {
      List => "the next subset after S, or null if S is the last subset"
    },
    PARA {
      "Given a subset S of {0..n-1}, this function returns the next one.
      Subsets are ordered lexicographically in the sense of Nijenhuis-Wilf
      ([NW, Chapter 13]).
      Concretely, this is the `binary counting' order, in which a subset
      is encoded as a bit sequence and subsets are ordered by the numerical
      value of their encodings."
    },
    PARA {
      "This is the same order as the list generated by ",
      TO subsets,
      "."
    },
    PARA {
      "This is `lexicographic' in the sense of sorting the bit-strings
      lexicographically.
      Note, this is different than sorting the subsets by their lists
      of elements."
    }
  },
  SYNOPSIS {
    Usage => "nextSubset(n)",
    Inputs => {
      "n" => ZZ => "the size of the containing set",
    },
    Outputs => {
      List => "the first subset of {0..n-1} (the empty subset)"
    },
    PARA {
      "This function returns the first subset of {0..n-1},
      namely the empty subset."
    }
  },
  SYNOPSIS {
    Usage => "prevSubset(n,S)",
    Inputs => {
      "n" => ZZ => "the size of the containing set",
      "S" => List => "list of elements of a subset of {0..n-1}",
    },
    Outputs => {
      List => "the subset before S, or null if S is the first subset"
    },
    PARA {
      "Given a subset S of {0..n-1}, this function returns the previous one
      in Nijenhuis-Wilf's lexicographic order."
    }
  },
  SYNOPSIS {
    Usage => "prevSubset(n)",
    Inputs => {
      "n" => ZZ => "the size of the containing set",
    },
    Outputs => {
      List => "the last subset of {0..n-1} (the whole set)"
    },
    PARA {
      "This function returns the last subset of {0..n-1},
      namely the set {0..n-1} itself."
    }
  },

  EXAMPLE lines ///
    S = nextSubset 5
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = nextSubset(5,S)
    S = {1,3,4};
    S = nextSubset(5,S)
    S = prevSubset(5,S)
  ///,
  
  SeeAlso => { subsets, Size }
}

document {
  Key => {
    Size
  },
  Headline => "name for an optional argument"
}

document {
  Key => {
    [nextSubset, Size],
    [prevSubset, Size]
  },
  Headline => "Restrict to subsets of a particular size",
  SYNOPSIS {
    Usage => "nextSubset(n,S,Size=>k)",
  },
  SYNOPSIS {
    Usage => "prevSubset(n,S,Size=>k)",
  },
  PARA {
    "Given a subset S of {0..n-1} having k elements,
    these functions return the next or previous subset also having k elements.
    Subsets are ordered lexicographically in the sense of Nijenhuis-Wilf.
    Concretely, this is the `binary counting' order, in which a subset
    is encoded as a bit sequence and subsets are ordered by the numerical
    value of their encodings.
    For subsets of a fixed size k, this coincides with the ordering
    of the subsets by lexicographically sorting their lists of elements."
  },
  PARA {
    "This is the same order as the list generated by ",
    TO "subsets(n,k)",
    "."
  },
  PARA {
    "The default value, null, corresponds to subsets of unrestricted size."
  },

  EXAMPLE lines ///
    T = nextSubset(5,Size=>3)
    T = nextSubset(5,T,Size=>3)
    T = nextSubset(5,T,Size=>3)
    U = prevSubset(5,Size=>3)
    U = prevSubset(5,U,Size=>3)
    U = prevSubset(5,U,Size=>3)
  ///
}

document {
  Key => {
    nextPartition,
    (nextPartition, Partition),
    (nextPartition, Nothing),
    (nextPartition, ZZ),
    (nextPartition, ZZ, ZZ),
  },
  Headline => "Generate the next partition",
  SYNOPSIS {
    Heading => "Generate the next partition",
    Usage => "nextPartition(P)",
    Inputs => {
      "P" => Partition => "a partition"
    },
    Outputs => {
      Partition => "the next partition after P, or null if P is the last partition"
    },
    PARA {
      "Given a partition of a positive integer,
      returns the next partition of the integer if there is one,
      or null otherwise. "
    },
    PARA {
      "Partitions are ordered lexicographically in the sense of Nijenhuis-Wilf.
      This is the same as the order generated by ",
      TO partitions,
      "."
    }
  },
  SYNOPSIS {
    Heading => "the first partition of an integer",
    Usage => "nextPartition(n)",
    Inputs => {
      "n" => ZZ => "an integer"
    },
    Outputs => {
      Partition => "the first partition of n"
    },
    PARA {
      "The first partition of n (the one-part partition {n})."
    }
  },
  
  SYNOPSIS {
    Heading => "the first partition with parts of bounded size",
    Usage => "nextPartition(n,k)",
    Inputs => {
      "n" => ZZ => "an integer",
      "k" => ZZ => "a bound for the size of parts in a partition"
    },
    Outputs => {
      Partition => "the first partition of n with parts of size at most k"
    },
    PARA {
      "The first partition of n with parts of size at most k.
      Subsequent iterations of nextPartition generate further partitions
      of n, still with parts of size at most k."
    }
  },
  
  EXAMPLE lines ///
    P = nextPartition 5
    P = nextPartition P
    P = nextPartition P
    Z = new Partition from {1,1,1,1,1}; -- the last partition of 5
    nextPartition Z
  ///,
  
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
  SYNOPSIS {
    Heading => "Generate the previous partition",
    Usage => "prevPartition(P)",
    Inputs => {
      "P" => Partition => "a partition"
    },
    Outputs => {
      Partition => "the partition before P, or null if P is the first partition"
    },
    "Given a partition of a positive integer, ",
    "returns the previous partition of the integer if there is one, ",
    "or null otherwise. ",
  },
  SYNOPSIS {
    Heading => "the last partition",
    Usage => "prevPartition(n)",
    Inputs => {
      "n" => ZZ => "an integer"
    },
    Outputs => {
      Partition => "the last partition of n"
    },
    PARA {
      "The last partition of n (the all-ones partition)."
    }
  },
  
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
  SYNOPSIS {
    Heading => "Generate the next permutation",
    Usage => "nextPermutation(P)",
    Inputs => {
      "P" => List => "a permutation of {0,...,n-1}"
    },
    Outputs => {
      List => "the next permutation after P, or null if P is the last permutation"
    },
    PARA {
      "Given a permutation of {0,...,n-1}, this function returns
      the next permutation if there is one, or null otherwise."
    },
    PARA {
      "Permutations are ordered lexicographically in the sense of Nijenhuis-Wilf.
      This is the same as the order generated by ",
      TO permutations,
      ". It starts at the ordered permutation {0,...,n-1}
      and ends at the antiordered permutation {n-1,...,0}."
    }
  },
  
  SYNOPSIS {
    Heading => "the first permutation",
    Usage => "nextPermutation(n)",
    Inputs => {
      "n" => ZZ => "an integer"
    },
    Outputs => {
      List => "the first permutation of {0,..,n-1}"
    },
    PARA {
      "Returns the first permutation of {0,..,n-1},
      namely the integers {0,..,n-1} in order
      (the identity permutation)."
    }
  },

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
  SYNOPSIS {
    Heading => "Generate the previous permutation",
    Usage => "prevPermutation(P)",
    Inputs => {
      "P" => List => "a permutation of {0,...,n-1}"
    },
    Outputs => {
      List => "the permutation before P, or null if P is the first permutation"
    },
    PARA {
      "Given a permutation of {0,...,n-1}, this function returns
      the previous permutation if there is one, or null otherwise."
    }
  },
  
  SYNOPSIS {
    Heading => "the last permutation",
    Usage => "prevPermutation(n)",
    Inputs => {
      "n" => ZZ => "an integer"
    },
    Outputs => {
      List => "the last permutation of {0,..,n-1}"
    },
    PARA {
      "Returns the last permutation of {0,..,n-1},
      namely the integers {n-1,..,0} in decreasing order."
    }
  },

  EXAMPLE lines ///
    P = prevPermutation 5
    P = prevPermutation P
    P = prevPermutation P
    A = {0,1,2,3,4} -- the first permutation of {0..4}
    nextPermutation A
  ///,
  
  SeeAlso => { nextPermutation, permutations }
}


document {
  Key => {
    Filling,
    (conjugate, Filling),
    (symbol ^,Filling,List),
    (symbol _,Filling,List),
    shape
  },
  Headline => "the class of all fillings of Young diagrams",
  "A filling is an assignment of a value (typically an integer)
  to each cell of a Young diagram.",
  
  EXAMPLE lines ///
    T = new Filling from {{10,9,8},{10,8,5},{4,3},{4,1},{0}}
  ///,
  
  "The conjugate of a filling is obtained by transposition.",
  
  EXAMPLE lines ///
    conjugate T
  ///,
  
  "Rows and columns of a filling can be selected with the same
  syntax as choosing rows and columns of a matrix.
  Individual entries ",
  
  EXAMPLE lines ///
    T^{0,2} -- select rows
    T_{0,2,3} -- select columns
  ///,
  
  "The underlying Young diagram can be extracted with ",
  CODE "shape",
  ", yielding a partition.",
  
  EXAMPLE lines ///
    shape T
  ///

}


-- XXXXXX



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
  assert( S === {} );
///

TEST ///
  for n from 0 to 12 do (
    assert( collectIterations(s -> nextSubset(n,s)) === subsets(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from -2 to n+2 do (
      assert( collectIterations(s -> nextSubset(n,s,Size=>k)) === subsets(n,k) );
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
  assert( S === {0,1,2,3,4} );
///

TEST ///
  for n from 0 to 12 do (
    assert( collectIterations(s -> prevSubset(n,s)) === reverse subsets(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from -2 to n+2 do (
      assert( collectIterations(s -> prevSubset(n,s,Size=>k)) === reverse subsets(n,k) );
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
    assert( collectIterations(nextPartition, n) === partitions(n) );
  );
///

TEST ///  
  for n from 0 to 12 do (
    for k from 1 to n+2 do (
      assert( collectIterations(nextPartition, nextPartition(n,k),
        CollectInitializer=>true) === partitions(n,k) );
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
    assert( collectIterations(prevPartition, n) === reverse partitions(n) );
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
    assert( collectIterations(nextPermutation, n) === permutations(n) );
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
    assert( collectIterations(prevPermutation, n) === reverse permutations(n) );
  );
///



TEST ///
  scan({ {1,1} , {2,2} , {4,3,2,2} }, l -> (
    D = new YoungDiagram from l;
    T = nextStandardTableau D;
    assert( shape T === D );
    assert( isStandardTableau T );
    T' = prevStandardTableau D;
    assert( shape T' === D );
    assert( isStandardTableau T' );
  ))
///

TEST ///
assert( collectIterations(nextStandardTableau,{1,1}) === {
  new Filling from {{0},{1}}} );

assert( collectIterations(nextStandardTableau,{2,2}) === {
  new Filling from {{0,1},{2,3}},
  new Filling from {{0,2},{1,3}}} );

assert( collectIterations(nextStandardTableau,{3,3}) === {
  new Filling from {{0,1,2},{3,4,5}},
  new Filling from {{0,1,3},{2,4,5}},
  new Filling from {{0,2,3},{1,4,5}},
  new Filling from {{0,1,4},{2,3,5}},
  new Filling from {{0,2,4},{1,3,5}}} );

assert( collectIterations(nextStandardTableau,{3,1,1}) === {
  new Filling from {{0,1,2},{3},{4}},
  new Filling from {{0,1,3},{2},{4}},
  new Filling from {{0,2,3},{1},{4}},
  new Filling from {{0,1,4},{2},{3}},
  new Filling from {{0,2,4},{1},{3}},
  new Filling from {{0,3,4},{1},{2}}} );

assert( collectIterations(nextStandardTableau,{3,2}) === {
  new Filling from {{0,1,2},{3,4}},
  new Filling from {{0,1,3},{2,4}},
  new Filling from {{0,2,3},{1,4}},
  new Filling from {{0,1,4},{2,3}},
  new Filling from {{0,2,4},{1,3}}} );

assert( collectIterations(nextStandardTableau,{4,3}) === {
  new Filling from {{0,1,2,3},{4,5,6}},
  new Filling from {{0,1,2,4},{3,5,6}},
  new Filling from {{0,1,3,4},{2,5,6}},
  new Filling from {{0,2,3,4},{1,5,6}},
  new Filling from {{0,1,2,5},{3,4,6}},
  new Filling from {{0,1,3,5},{2,4,6}},
  new Filling from {{0,2,3,5},{1,4,6}},
  new Filling from {{0,1,4,5},{2,3,6}},
  new Filling from {{0,2,4,5},{1,3,6}},
  new Filling from {{0,1,2,6},{3,4,5}},
  new Filling from {{0,1,3,6},{2,4,5}},
  new Filling from {{0,2,3,6},{1,4,5}},
  new Filling from {{0,1,4,6},{2,3,5}},
  new Filling from {{0,2,4,6},{1,3,5}}} );

assert( collectIterations(nextStandardTableau,{4,2,1}) === {
  new Filling from {{0,1,2,3},{4,5},{6}},
  new Filling from {{0,1,2,4},{3,5},{6}},
  new Filling from {{0,1,3,4},{2,5},{6}},
  new Filling from {{0,2,3,4},{1,5},{6}},
  new Filling from {{0,1,2,5},{3,4},{6}},
  new Filling from {{0,1,3,5},{2,4},{6}},
  new Filling from {{0,2,3,5},{1,4},{6}},
  new Filling from {{0,1,4,5},{2,3},{6}},
  new Filling from {{0,2,4,5},{1,3},{6}},
  new Filling from {{0,1,2,3},{4,6},{5}},
  new Filling from {{0,1,2,4},{3,6},{5}},
  new Filling from {{0,1,3,4},{2,6},{5}},
  new Filling from {{0,2,3,4},{1,6},{5}},
  new Filling from {{0,1,2,5},{3,6},{4}},
  new Filling from {{0,1,3,5},{2,6},{4}},
  new Filling from {{0,2,3,5},{1,6},{4}},
  new Filling from {{0,1,4,5},{2,6},{3}},
  new Filling from {{0,2,4,5},{1,6},{3}},
  new Filling from {{0,3,4,5},{1,6},{2}},
  new Filling from {{0,1,2,6},{3,4},{5}},
  new Filling from {{0,1,3,6},{2,4},{5}},
  new Filling from {{0,2,3,6},{1,4},{5}},
  new Filling from {{0,1,4,6},{2,3},{5}},
  new Filling from {{0,2,4,6},{1,3},{5}},
  new Filling from {{0,1,2,6},{3,5},{4}},
  new Filling from {{0,1,3,6},{2,5},{4}},
  new Filling from {{0,2,3,6},{1,5},{4}},
  new Filling from {{0,1,4,6},{2,5},{3}},
  new Filling from {{0,2,4,6},{1,5},{3}},
  new Filling from {{0,3,4,6},{1,5},{2}},
  new Filling from {{0,1,5,6},{2,3},{4}},
  new Filling from {{0,2,5,6},{1,3},{4}},
  new Filling from {{0,1,5,6},{2,4},{3}},
  new Filling from {{0,2,5,6},{1,4},{3}},
  new Filling from {{0,3,5,6},{1,4},{2}}} );
///

TEST ///
assert( collectIterations(prevStandardTableau,{1,1}) === {
  new Filling from {{0},{1}}} );

assert( collectIterations(prevStandardTableau,{2,2}) === {
  new Filling from {{0,2},{1,3}},
  new Filling from {{0,1},{2,3}}} );

assert( collectIterations(prevStandardTableau,{3,3}) === {
  new Filling from {{0,2,4},{1,3,5}},
  new Filling from {{0,1,4},{2,3,5}},
  new Filling from {{0,2,3},{1,4,5}},
  new Filling from {{0,1,3},{2,4,5}},
  new Filling from {{0,1,2},{3,4,5}}} );

assert( collectIterations(prevStandardTableau,{3,1,1}) === {
  new Filling from {{0,3,4},{1},{2}},
  new Filling from {{0,2,4},{1},{3}},
  new Filling from {{0,1,4},{2},{3}},
  new Filling from {{0,2,3},{1},{4}},
  new Filling from {{0,1,3},{2},{4}},
  new Filling from {{0,1,2},{3},{4}}} );

assert( collectIterations(prevStandardTableau,{3,2}) === {
  new Filling from {{0,2,4},{1,3}},
  new Filling from {{0,1,4},{2,3}},
  new Filling from {{0,2,3},{1,4}},
  new Filling from {{0,1,3},{2,4}},
  new Filling from {{0,1,2},{3,4}}} );

assert( collectIterations(prevStandardTableau,{4,3}) === {
  new Filling from {{0,2,4,6},{1,3,5}},
  new Filling from {{0,1,4,6},{2,3,5}},
  new Filling from {{0,2,3,6},{1,4,5}},
  new Filling from {{0,1,3,6},{2,4,5}},
  new Filling from {{0,1,2,6},{3,4,5}},
  new Filling from {{0,2,4,5},{1,3,6}},
  new Filling from {{0,1,4,5},{2,3,6}},
  new Filling from {{0,2,3,5},{1,4,6}},
  new Filling from {{0,1,3,5},{2,4,6}},
  new Filling from {{0,1,2,5},{3,4,6}},
  new Filling from {{0,2,3,4},{1,5,6}},
  new Filling from {{0,1,3,4},{2,5,6}},
  new Filling from {{0,1,2,4},{3,5,6}},
  new Filling from {{0,1,2,3},{4,5,6}}} );

assert( collectIterations(prevStandardTableau,{4,2,1}) === {
  new Filling from {{0,3,5,6},{1,4},{2}},
  new Filling from {{0,2,5,6},{1,4},{3}},
  new Filling from {{0,1,5,6},{2,4},{3}},
  new Filling from {{0,2,5,6},{1,3},{4}},
  new Filling from {{0,1,5,6},{2,3},{4}},
  new Filling from {{0,3,4,6},{1,5},{2}},
  new Filling from {{0,2,4,6},{1,5},{3}},
  new Filling from {{0,1,4,6},{2,5},{3}},
  new Filling from {{0,2,3,6},{1,5},{4}},
  new Filling from {{0,1,3,6},{2,5},{4}},
  new Filling from {{0,1,2,6},{3,5},{4}},
  new Filling from {{0,2,4,6},{1,3},{5}},
  new Filling from {{0,1,4,6},{2,3},{5}},
  new Filling from {{0,2,3,6},{1,4},{5}},
  new Filling from {{0,1,3,6},{2,4},{5}},
  new Filling from {{0,1,2,6},{3,4},{5}},
  new Filling from {{0,3,4,5},{1,6},{2}},
  new Filling from {{0,2,4,5},{1,6},{3}},
  new Filling from {{0,1,4,5},{2,6},{3}},
  new Filling from {{0,2,3,5},{1,6},{4}},
  new Filling from {{0,1,3,5},{2,6},{4}},
  new Filling from {{0,1,2,5},{3,6},{4}},
  new Filling from {{0,2,3,4},{1,6},{5}},
  new Filling from {{0,1,3,4},{2,6},{5}},
  new Filling from {{0,1,2,4},{3,6},{5}},
  new Filling from {{0,1,2,3},{4,6},{5}},
  new Filling from {{0,2,4,5},{1,3},{6}},
  new Filling from {{0,1,4,5},{2,3},{6}},
  new Filling from {{0,2,3,5},{1,4},{6}},
  new Filling from {{0,1,3,5},{2,4},{6}},
  new Filling from {{0,1,2,5},{3,4},{6}},
  new Filling from {{0,2,3,4},{1,5},{6}},
  new Filling from {{0,1,3,4},{2,5},{6}},
  new Filling from {{0,1,2,4},{3,5},{6}},
  new Filling from {{0,1,2,3},{4,5},{6}}} );
///

TEST ///
  scan( {
  {1,1},
  {2,2},
  {3,3},
  {3,1,1},
  {3,2},
  {4,3},
  {4,2,1}
  },
  x -> assert ( collectIterations(nextStandardTableau,x) === reverse collectIterations(prevStandardTableau,x) )
)
///

end

--------------------------------------------------------------------------------


restart
loadPackage "CombinatorialIteration"
installPackage oo
check oo

gentest = l -> (
  prefixString = "assert( collectIterations(nextStandardTableau,";
  listString = toExternalString l;
  middleString = ") === ";
  resultString = replace("new","\n  new",toExternalString collectIterations(nextStandardTableau,l));
  postfixString = " );\n";
  
  concatenate(prefixString,listString,middleString,resultString,postfixString)
)

scan( {
  {1,1},
  {2,2},
  {3,3},
  {3,1,1},
  {3,2},
  {4,3},
  {4,2,1}
  },
  x -> print gentest x
)

