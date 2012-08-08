---------------
---Compositions
---------------
local ncomp;
local lcomp;
local tempcomp;

compositions(List,ZZ) := (l,n) ->
(
     k := #l;
     d := sum(l)-l#(k-1);
     ncomp = 0;
     lcomp = new MutableList;
     tempcomp = new MutableList;
     comp(l,n,d);
     toList lcomp
     )

comp = method()
comp(List,ZZ,ZZ) := (l,n,d) ->
(
     k := #l;
     if k == 1 then 
     (
	  tempcomp#0 = n;
	  if n<=l#0 then
	  (
	       lcomp#ncomp = toList tempcomp;
	       ncomp = ncomp + 1;
	       );
	  )
     else for p from max(n-d,0) to min(l#(k-1),n) do     
     (
	  tempcomp#(k-1) = p;
	  comp(drop(l,-1),n-p,d-l#(k-2));
	  );
     )

---------------------
----Standard Tableaux
---------------------

--tableaux are given by lists of their column entries
--assumed to be skew symmetric within columns

local tempTab
local tempLam
local auxlam
local auxrho
local auxc
local auxk
local listOfTableaux

standardTableaux = method()
standardTableaux(List,List) := (lam,rho) ->
(
     auxlam = lam;
     auxrho = rho;
     auxc = lam#0;
     auxk = #lam;
     tempTab = new MutableList from auxk:{};--partially constructed tableau
     tempLam = new MutableList from auxk:0;--lengths of rows of tempTab     
     nc := join({auxc},splice{auxk:0});--number of columns of a given size
     listOfTableaux = {};
     stdTabRec(nc,0);
     listOfTableaux               
     )

stdTabRec = method()
stdTabRec(List,ZZ) := (nc,i) ->
(
if i == #auxrho then listOfTableaux = listOfTableaux | {tabTranspose(toList tempTab)} else
(     
  bdscomp := new MutableList from auxk:0;
  cate := nc#auxk;
  for j from 1 to auxk do
  (
       bdscomp#(auxk-j) = min(auxlam#(auxk-j)-cate,nc#(auxk-j));
       cate = cate + nc#(auxk-j);
       );
  for comp in compositions(toList bdscomp,auxrho#i) do
  (
       for j from 0 to #auxlam-1 do 
       (
	    tempTab#j = tempTab#j | toList(comp#j:i+1);
	    tempLam#j = tempLam#j + comp#j;
	    );
       stdTabRec(nc-(comp|{0})+({0}|comp),i+1);
       for j from 0 to #auxlam-1 do 
       (
	    tempLam#j = tempLam#j - comp#j;
	    tempTab#j = drop(tempTab#j,-comp#j);
	    );
       );
     )
)

tabTranspose = method()
tabTranspose(List) := tab ->
(
     lam := apply(tab,i->#i);
     newTab := new MutableList from (lam#0:{});
     for i from 0 to #lam-1 do
     	  for j from 0 to lam#i-1 do
	       newTab#j = newTab#j | {tab#i#j};
     toList newTab
     )

perTab = method()
perTab(List,List) := (per,tab) ->
(
     apply(tab,i->apply(i,j->per#(j-1)))
     )

end