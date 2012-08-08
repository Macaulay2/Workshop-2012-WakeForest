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
nextSubset = method(Options=>{Size=>null})
nextSubset ZZ := o -> (n) -> (
  if o.Size === null then return {}
  else if o.Size <= n then return new List from (0..(o.Size-1))
  else return null;
)
nextSubset (ZZ,Nothing) := o -> (n,P) -> null
nextSubset (ZZ,List) := o -> (n,P) -> (
  if ((o.Size =!= null) and (o.Size != #P)) then error "current subset not the expected size";
  -- Last one?
  lastone := (#P == 0) or (P#0 == n-#P);
  if lastone and o.Size =!= null then return null;
  if lastone and o.Size === null then return nextSubset(n,Size=>(#P+1));
  
  -- Find the position to change.
  p := 0;
  while ( p < #P-1 and (P#p)+1 == P#(p+1) ) do p = p+1;
  P = replace(p,(P#p)+1,P);
  while ( (p = p-1) >= 0 ) do P = replace(p,p,P);
  
  return P;
)
