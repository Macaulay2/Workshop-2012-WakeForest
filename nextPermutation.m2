-- nextPermutation
-- Given a permutation of {1..n} returns another one.
-- The iterator starts at {1..n} and ends at {n..1}.
-- Based on code by tye posted on PerlMonks at
--   http://www.perlmonks.org/?node_id=29374
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
-- Sample usage:
{*
P = nextPermutation(5)
P = nextPermutation P
P = nextPermutation P
P = nextPermutation P
*}
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
