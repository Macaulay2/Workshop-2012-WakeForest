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
-- Sample usage:
{*
S = nextSubset(5)
P = nextSubset (S,P)
P = nextSubset (S,P)
P = nextSubset (S,P)
*}
nextSubset = method(Options=>{Size=>0,IncludingGreater=>true})
nextSubset ZZ := o -> (n) -> new List from (0..(o.Size-1))
nextSubset (ZZ,Nothing) := o -> (n,P) -> null
nextSubset (ZZ,List) := o -> (n,P) -> (
  currentSize := #P;
  wantedSize := o.Size;
  -- Last one?
  lastone := ((o.Size == 0 and currentSize == 0) or (P#0 == n-currentSize));
  if lastone and not o.IncludingGreater then return null;
  if lastone and o.IncludingGreater then (
    wantedSize = currentSize + 1;
    if wantedSize > n then return null else return nextSubset(n,Size=>wantedSize)
  );
  
  -- impossible?
  if wantedSize > n then return null;
  
  -- Find the position to change.
  p := 0;
  while ( p < currentSize-1 and (P#p)+1 == P#(p+1) ) do p = p+1;
  P = replace(p,(P#p)+1,P);
  while ( (p = p-1) >= 0 ) do P = replace(p,p,P);
  
  return P;
)
