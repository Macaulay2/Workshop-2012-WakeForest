-- nextPartition
-- Given a partition of n written in non-increasing order,
-- returns another one. The iterator starts at {n} and ends at {1,..,1}.
-- Based on code by blokhead posted on PerlMonks at
--   http://www.perlmonks.org/?node_id=621859
-- retrieved August 7, 2012
-- and adapted for Macaulay2 by Zach Teitler.
-- Sample usage:
{*
P = nextPartition(5)
P = nextPartition P
P = nextPartition P
P = nextPartition P
*}
nextPartition = method()
nextPartition ZZ := n -> new Partition from {n}
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
