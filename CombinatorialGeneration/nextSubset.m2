-- nextSubset
-- Given a subset of a list, returns another one.
-- The iterator starts at {} and ends at the whole list.
-- It can handle lists with repetition, e.g., {1,1,2,2}.
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
nextSubset (List) := o -> (S) -> take(S,o.Size)
nextSubset (List,Nothing) := o -> (S,P) -> null
nextSubset (List,List) := o -> (S,P) -> (
  currentSize := #P;
  wantedSize := o.Size;
  -- Last one?
  lastone := ((o.Size == 0 and currentSize == 0) or (P == take(S,-currentSize)));
  if lastone and not o.IncludingGreater then return null;
  if lastone and o.IncludingGreater then (
    wantedSize = currentSize + 1;
    if wantedSize > #S then return null else return nextSubset(S,Size=>wantedSize)
  );
  
  -- impossible?
  if wantedSize > #S then return null;
  
  -- Find the position to change.
  p := 0;
  while ( p < #P-1 and (P#p)+1 == P#(p+1) ) do p = p+1;
  
  return replace(p,(P#p)+1,P);
)
