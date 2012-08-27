-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2012  Gregory G. Smith
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------
newPackage(
  "SpectralSequences",
  Version => "0.3",
  Date => "8 August 2012",
  Authors => {
       {
      Name => "David Berlekamp", 
      Email => "daffyd@math.berkeley.edu", 
      HomePage => "http://www.math.berkeley.edu/~daffyd"},
    {
      Name => "Adam Boocher", 
      Email => "aboocher@math.berkeley.edu", 
      HomePage => "http://www.math.berkeley.edu/~aboocher"},
       {
      Name => "Nathan Grieve", 
      Email => "nathangrieve@mast.queensu.ca"},             
    {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"},
 {
      Name => "Thanh Vu", 
      Email => "vqthanh@math.berkeley.edu",
      HomePage => "http://math.berkeley.edu/~thanh"}},
  Headline => "spectral sequences",
  DebuggingMode => true
  )

export {
  "FilteredComplex",
  "filteredComplex",
  "SpectralSequence",
  "spectralSequence",
  "SpectralSequenceSheet",
  "see", "computeErModules","computeErMaps", "spots",
  "nonReducedChainComplex", "SpectralSequencePage", "spectralSequencePage"
  }

-- symbols used as keys
protect minF
protect maxF
protect minH
protect maxH
protect inducedMaps
protect pageNumber
protect pageModules
protect pageMaps
needsPackage "SimplicialComplexes"
needsPackage "ChainComplexExtras"

------------------------------------------------------
-- Hash table functions--
------------------------------------------------------
-- Retrieves the sorted integer keys of a hash table. 
spots =method ()
spots HashTable := K -> sort select(keys K, i -> class i === ZZ)

-- selects the largest integer value in the key of a hash table
max HashTable := K -> max spots K
--selects the least integer vaule in the key of a hash table
min HashTable := K -> min spots K

------------------------------------------------------
------------------------------------------------------

--------------------------------------------------------------------------------
Module + Module := Module => (M,N) -> (
  if ring M =!= ring N  then error "expected modules over the same ring";
  if ambient M != ambient N
  or M.?relations and N.?relations and M.relations != N.relations
  or M.?relations and not N.?relations
  or not M.?relations and N.?relations
  then error "expected submodules of the same module";
  subquotient(
    ambient M,
    if not M.?generators or not N.?generators then null else M.generators | N.generators,
    if M.?relations then M.relations else null))

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
-- I need the following method in my examples. 
--(Surely someting like it exists elsewhere.)
-- Many of the examples I computed by
-- hand arose from "simplicial complexes without the empty face."
-- the out of the box chain complex code for simplicial complexes produces chain complexes
-- which include the empty face.
-- 
-----------------------------------------------------------------------------------
nonReducedChainComplex=method()
nonReducedChainComplex(ChainComplex):= K->(l:=apply(drop(sort spots K,1),i-> i);
    p:= (for i from 1 to #l-1 list K.dd_i);
chainComplex(p)
 )

---
-- The sections  '"Core" filtered complex code' and '"Core spectral sequence code'
-- all are based on homological indexing conventions and have been tested on 
-- Nathan's examples.
--
-------------------------------------------------------------------------------------
-- "Core" filtered complex code. --
-------------------------------------------------------------------------------------
-- We want to use homological indexing for the filtration.  
--THE CONVENTION WE WANT TO FOLLOW IS IF C IS A COMPLEX WHOSE DIFFERENTIAL HAS
-- DEGREE -1 THEN THE FILTRATION SHOULD HAVE THE SHAPE
-- F_nC > F_(n-1)C. (See section 5.4 of Weibel.) 
-- Q:  IS THIS ASSCENDING OR DESCENDING?? (I always forget the terminology.)
 

FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"


filteredComplex = method(TypicalValue => FilteredComplex)

-- Primitive constructor, takes a list eg {m_n,m_(n-1), ...,m_0} 
-- defining inclusion maps C=F_(n+1)C > F_(n-1)C > ... > F_0 C 
-- of subcomplexes of a chain complex (or simplicial complexes) 
-- and produces a filtered complex with integer keys the
-- corresponing chain complex.
-- If F_0C is not zero then by default F_(-1)C is added and is 0.
-- I THINK THIS IS THE CONVENTION WE WANT BY DEFAULT.  SEE 
-- THE HOPF FIBRATION EXAMPLE.  TO GET THE CORRECT INDICIES ON THE E2 PAGE
-- WE WANT THE ZERO COMPLEX TO HAVE "FILTRATION DEGREE -1".


filteredComplex List := L -> (
  local maps;
  local C;
  if #L === 0 
  then error "expected at least one chain complex map or simplicial complex";
  if all(#L, p -> class L#p === SimplicialComplex) then (
    kk := coefficientRing L#0;
    C = chainComplex L#0; -- By default the ambient simplicial complex is the first element of the list
    maps = apply(#L-1, p -> map(C, chainComplex L#(p+1), 
        i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))))
  else (
    maps = L;
    if any(#maps, p-> class maps#p =!= ChainComplexMap) then (
      error "expected sequence of chain complexes");
    C = target maps#0;-- By default the ambient chain complex is target of first map.
    if any(#maps, p-> target maps#p != C) then (
      error "expected all map to have the same target"));     
  Z := image map(C, C, i -> 0*id_(C#i)); -- make zero subcomplex as a subcomplex of ambient complex 
 P := {(#maps) => C} | apply (#maps,  p -> #maps - (p+1) => image maps#p);
  if (last P)#1 != Z then P = P | {(-1) => Z};
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})


FilteredComplex _ InfiniteNumber :=
FilteredComplex _ ZZ := ChainComplex => (K,p) -> (
  if K#?p then K#p else if p < min K then K#(min K) else if p > max K then K#(max K)
  )

-- since we are using "homologicial indexing" by default the relationship
-- we want to preserve is F_p C_q = F^(-p)C^(-q) for all p and q.

FilteredComplex ^ InfiniteNumber :=
FilteredComplex ^ ZZ := ChainComplex => (K,p) -> ( K_(-p)
  )

----------------------------------------------------
--- I think we are going to want "shift of a filtered complex."  I'm suggesting
-- that it should look like  K[a,b] and 
-- have the property that K_p _ q [a,b] = K_(p+q)  _(q+b)
-----------------------------------------------------------

chainComplex FilteredComplex := ChainComplex => K -> K_infinity


FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
  all(min(min C,min D)..max(max C,max D),i-> C_i == D_i))

net FilteredComplex := K -> (
  v := between("", apply(sort spots K, p -> p | " : " | net K_p));
  if #v === 0 then "0" else stack v)
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------
-------------------------------------------------------------------------
-- "Core" spectral sequence code. --------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
-- below are the methods which compute the
-- individual terms on a page of a spectral sequence
-- WE ARE USING HOMOLOGICAL INDEXING CONVENTIONS.
---------------------------------------------------------------------
-- By default of the primitative homological constructor above, 
--the maximum integer key
-- of the filtered complex corresponds to the ambient complex.
-- This is used in the formula's below but should be made more "fool proof" in 
-- what follows.

-- the formula's below are the homological versions of the ones in I.2.4 of Danilov's 
-- treatment of spectral sequences in Shafarevich's Encyolpaedia of 
-- Math Algebraic Geometry II.  
-- In any event it is easy enough to prove directly that they satisfy the requirments 
-- for a spectral sequence.

zpq:= (K,p,q,r)->(
ker inducedMap((K_(max K))_(p+q-1) / K_(p-r) _ (p+q-1), 
     K_p _ (p+q), K_(max K).dd_(p+q))
     )



bpq:= (K,p,q,r) ->(
    ( image (K_(p+r-1).dd_(p+q+1))) + (K_(p-1) _ (p+q))
      )

-- the following will compute the pq modules on the rth page explicitly.

epq:=(K,p,q,r)->(  ((zpq(K,p,q,r)+bpq(K,p,q,r)) / bpq(K,p,q,r)) )


-- the following computes all modules on the r-th page.

computeErModules=method()

computeErModules(FilteredComplex,ZZ):= (K,r) -> (myList:={};
     for p from min K to max K do (
	  for q from -p to length K_(max K) do (
	       myList=append(myList, {p,q}=> epq(K,p,q,r)); )
	       	    );
	       new HashTable from myList
      )

-- the following will compute the pq maps on the rth page explicitly.
epqrMaps:=(K,p,q,r)-> (
     inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r),K_(max K).dd_(p+q)))


--Compute all maps on the Er page as we did above for the modules.

computeErMaps=method()

computeErMaps(FilteredComplex,ZZ):= (K,r) -> (myList:={};
     for p from min K to max K do (
	  for q from -p to length K_(max K) do (
	       myList=append(myList, {p,q}=> epqrMaps(K,p,q,r)); )
	       	    );
	       new HashTable from myList
      )



-------------------------------------------------------------------------------------
-- End of tested code ---
-------------------------------------------------------------------------------------


----------------------------------------------------------------------------------
-- begining of partially tested code. ---------
---------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- spectral sequence pages
--------------------------------------------------------------------------------
-- Following Hatcher's terminology and the terminology I first learned,
-- I prefer to use spectral sequence page rather than spectral sequence sheet.
-------------------------------------------------------------------------------
-- I also wanted to add certain keys to a spectral sequence page / sheet
-- might want to make this a hash table instead of a mutable hash table.
SpectralSequencePage = new Type of MutableHashTable
SpectralSequencePage.synonym = "spectral sequence page"

spectralSequencePage = method ()
spectralSequencePage(FilteredComplex, ZZ):= (K,r) ->( 
new SpectralSequencePage from 
 {symbol filteredComplex=> K, symbol pageNumber =>r, 
      symbol pageModules => computeErModules(K,r), symbol dd => computeErMaps(K,r), 
     symbol zero => (ring K_infinity)^0})



-- in the following we are assuming that user is inputing a list of 
-- pairs of integers.
-- should return an error message if this isn't the case.

SpectralSequencePage _ List := Module => (E,i)-> if (E.pageModules)#?i then 
 (E.pageModules)#i else image(0*id_((E.filteredComplex_infinity)_(sum i)))  

SpectralSequencePage ^ List := Module => (E,i)-> E_(apply(i, j-> -j))    

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- spectral sequences ----------------------------------------------------------
--------------------------------------------------------------------------------
SpectralSequence = new Type of MutableHashTable
SpectralSequence.synonym = "spectral sequence"
SpectralSequence.GlobalAssignHook = globalAssignFunction
SpectralSequence.GlobalReleaseHook = globalReleaseFunction
describe SpectralSequence := E -> net expression E
net SpectralSequence := E -> (
  if hasAttribute(E, ReverseDictionary) 
  then toString getAttribute(E, ReverseDictionary) 
  else net expression E)
expression SpectralSequence := E -> stack(
  "  .-.  ", " (o o) ", " | O \\   Unnamed spectral sequence! ..ooOOOooooOO", 
  "  \\   \\  ", "   `~~~` ")

----------------------------------------------------------------------------
-- I'm also not sure if we need or want a degree option.

spectralSequence = method(Options => {Degree => 1})
spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
     new SpectralSequence from {
	  symbol filteredComplex => K,
	  symbol zero => K.zero,
	  symbol cache => CacheTable})

-- In the following we are still going to want E^infinity etc. --

  SpectralSequence ^ ZZ := SpectralSequencePage => (E,r) -> (
       if E#?r then E#r else E#r= spectralSequencePage(E.filteredComplex,r);
       E#r
       )

SpectralSequence _ ZZ := SpectralSequencePage => (E,r) -> ( E^r       )

-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- end of partially tested code. --------------------------------------------------
-----------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
-- Retrieves (or lazily constructs) the inclusion map from the pth subcomplex to the top
inducedMap (FilteredComplex, ZZ) := ChainComplexMap => opts -> (K,p) -> (
  if not K.cache#?inducedMaps then K.cache.inducedMaps = new MutableHashTable;
  if not K.cache.inducedMaps#?p then K.cache.inducedMaps#p = inducedMap(K^-infinity, K^p);
  K.cache.inducedMaps#p)

project := (K,p) -> (
     f:= i -> map(K^p_i,K^-infinity_i,1);
     map(K^p,K^-infinity,f)
     )



-- Method for looking at all of the chain subcomplexes pleasantly
see = method();
see FilteredComplex := K -> (
     -- Eliminate the duplication of the homological indices
  (minK, maxK) := (min K, max K);
  T := table(reverse toList(min K^-infinity .. max K^-infinity), 
    toList(minK .. maxK), (p,i) ->
    if i === minK then p | " : " | net prune K^p_i else
    " <-- " | net prune K^p_i);
  T = T | {toList(minK .. maxK)};
  netList T)




------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
-- ChainComplexExtraExtras  --------------------------------------------------------

--------------------------------------------------------------------------------------

--truncate C above ith spot, i.e. set everything weakly above homological degree i to 0
truncate (ChainComplex, ZZ) := ChainComplex => (C,i) -> (
  complete C;
  if i < min C then chainComplex gradedModule (ring C)^0
  else chainComplex apply(drop(spots C,1), k -> if k < i then C.dd_k else if k===i then 
       map(C_(k-1), 0*C_k, 0) else map(0*C_(k-1),0*C_k,0)))   
    
-- Computes the graded pieces of the total complex of a Hom double complex 
-- (just as a graded module, so no maps!)
Hom (GradedModule, GradedModule) := GradedModule => (C,D) -> (
  R := C.ring;  if R =!= D.ring then error "expected graded modules over the same ring";
  (c,d) := (spots C, spots D);
  pairs := new MutableHashTable;
  scan(c, i -> scan(d, j -> (
        k := j-i;
	p := if not pairs#?k then pairs#k = new MutableHashTable else pairs#k;
	p#(i,j) = 1;)));
  scan(keys pairs, k -> pairs#k = sort keys pairs#k);
  E := new GradedModule;
  E.ring = R;
  scan(keys pairs, k-> (
      p := pairs#k;
      E#k = directSum(apply(p, v -> v => Hom(C_(v#0), D_(v#1) )));));
  E)

Hom(Matrix, Module) := Matrix => (f,N) -> (
     g:= (f * map(source f,cover source f,1)) // map(target f,cover target f,1);
     inducedMap(Hom(source f, N),Hom(target f, N), transpose g ** N))

Hom(Module, Matrix) := Matrix => (N,f) -> (inducedMap(Hom(N,target f),Hom(N,source f), (dual cover N) ** f))
     
cover ChainComplex := ChainComplex => C -> (
     minC := min spots C;
     maxC := max spots C;
     P:= apply(toList(minC..maxC),i-> cover C#i);
     chainComplex apply(toList(minC..maxC-1), i-> C.dd_(i+1) * map(C_(i+1),P_(i+1),1) // map(C_i,P_i,1)))

isWellDefined ChainComplexMap := Boolean => f -> (
     (F,G):= (source f, target f);
     all(drop(spots F,1), i -> G.dd_i * f#i == f#(i-1) * F.dd_i))

-- Computes the total complex of the Hom double complex of two chain complexes
Hom (ChainComplex, ChainComplex) := ChainComplex => (C,D) -> (
  if C.ring =!= D.ring then error "expected chain complexes over the same ring";
  E := chainComplex (lookup( Hom, GradedModule, GradedModule))(C,D);
  scan(spots E, i -> if E#?i and E#?(i-1) then E.dd#i = 
    map(E#(i-1), E#i, 
      matrix table(
        E#(i-1).cache.indices, E#i.cache.indices, 
	(j,k) -> map(E#(i-1).cache.components#(E#(i-1).cache.indexComponents#j), 
	  (E#i).cache.components#((E#i).cache.indexComponents#k),
	  if j#0 === k#0 and j#1 === k#1-1 then (-1)^(k#0)*Hom(C_(k#0),D.dd_(k#1))
	  else if j#0 === k#0 + 1 and j#1 === k#1 then Hom(C.dd_(j#0),D_(k#1))
	  else 0))));
  E)	    		    

Hom (ChainComplex, ChainComplexMap) := ChainComplexMap => (C,f) -> (
  (F,G) := (Hom(C,source f),Hom(C,target f)); 
  map(G,F, i -> map(G_i,F_i, matrix table( G_i.cache.indices,F_i.cache.indices, 
      (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
        F#i.cache.components#(F#i.cache.indexComponents#k),
	if j === k then Hom(C_(j#0), f_(j#1)) 
	else 0)))))

Hom (ChainComplexMap, ChainComplex) := ChainComplexMap => (f,C) -> (
  (F,G) := (Hom(target f, C),Hom(source f, C));
  map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
        (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
	  F#i.cache.components#(F#i.cache.indexComponents#k),
	  if j === k then Hom(f_(j#0), C_(j#1)) 
	  else 0)))))
  
ChainComplexMap ** ChainComplex := ChainComplexMap => (f,C) -> (
  (F,G) := ((source f) ** C, (target f) ** C); 
  map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
        (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
	  F#i.cache.components#(F#i.cache.indexComponents#k),
	  if j === k then f_(j#0) ** C_(j#1) 
	  else 0)))))

ChainComplex ** ChainComplexMap := ChainComplexMap => (C,f) -> (
  (F,G) := (C ** source f, C ** target f); 
  map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
        (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
	  F#i.cache.components#(F#i.cache.indexComponents#k),
	  if j === k then C_(j#0) ** f_(j#1) 
	  else 0)))))





--------------------------------------------------------------------------------
-- constructing filtered complexes ---------------------------------------------
--------------------------------------------------------------------------------


-- Gives the naive filtration on a chain complex

-- there is a bug in this code.  See example. ---
filteredComplex ChainComplex := C -> (
     complete C;
     filteredComplex apply(drop(rsort spots C,1), i -> inducedMap(C,truncate(C,i))))  

prune FilteredComplex := FilteredComplex => opts -> F -> 
  new FilteredComplex from 
  apply(keys F, p -> if class p =!= Symbol then p => prune F#p else p => F#p)

Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
  filteredComplex for p from min K to max K list Hom(project(K,p),C))

Hom (ChainComplex, FilteredComplex):= FilteredComplex => (C,K) -> (
  filteredComplex for p from min K to max K list Hom(C,inducedMap(K,p)))

FilteredComplex ** ChainComplex := FilteredComplex => (K,C) -> (
  filteredComplex for p from min K to max K list inducedMap(K,p) ** C)

ChainComplex ** FilteredComplex := FilteredComplex => (C,K) -> (
  filteredComplex for p from min K to max K list C ** inducedMap(K,p))



filteredComplex SpectralSequence := FilteredComplex => E -> E.filteredComplex

chainComplex SpectralSequence := ChainComplex => E -> chainComplex filteredComplex E




-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- get the inverse image of C under the map d
-- invSubmodule := (d,C) -> ker (inducedMap ((target d)/C,target d) * d)

-- internal functions (creating approximate cycle & boundary subquotients)

-- pageZ := (r, F,p,q) -> 
--     (invSubmodule (F^p.dd_(-p-q),F^(p+r)_(-p-q-1)) + F^(p+1)_(-p-q))/F^(p+1)_(-p-q)

-- pageB := (r, F,p,q) -> 
--     (intersect (image F^(p-r+1).dd_(1-p-q),F^p_(-p-q)) + F^(p+1)_(-p-q)) / F^(p+1)_(-p-q)

--- pageE := (r, F,p,q) -> (
---     if r < 1 then F^p_(-p-q)/F^(p+1)_(-p-q) else 
---     if r == 1 then ker F^p.dd_(-p-q) / image F^p.dd_(1-p-q)
---     else pageZ(r,F,p,q)/pageB(r,F,p,q))


--differential = method ();
--differential (ZZ,FilteredComplex,ZZ,ZZ):=Matrix => (r,F,p,q) -> 
--    inducedMap(pageZ(r,F,p+r,q-r+1),pageZ(r,F,p,q),F^p.dd_(-p-q))

-----------------------------------------------------------------------
-----------------------------------------------------------------------

SpectralSequenceSheet = new Type of MutableHashTable
SpectralSequenceSheet.synonym = "spectral sequence sheet"


SpectralSequenceSheet ^ List := Module => (Er,L) -> if Er#?L then Er#L else Er.zero


support SpectralSequenceSheet := List => E -> 
  apply (select(keys E,i -> class i === List), j -> j => prune E^j)
  
SpectralSequenceSheet == SpectralSequenceSheet := Boolean => (E,F) -> 
  all(keys E, i-> F#?i and E#i == F#i)
     
changeofRing = method ();
changeofRing (Module,Module):= SpectralSequence => (M,N) -> 
     spectralSequence ((filteredComplex ((res M) ** ring N)) ** (res N))


load "Doc/SpectralSequencesDoc.m2"
end

--------------------------------------------------------------------------------
restart
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
viewHelp SpectralSequences
-------------------------------------------------------------------
-- the following is very experimental code.  Once the bugs are worked out
-- this should be included and exported.  Basically I want to 
-- compute the "homology of a spectral sequence page" and then
-- express the isomorphism between this and the modules on the next page.


restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[a,b,c,d]

D=simplicialComplex {a*d*c, a*b, a*c, b*c}

F2D=D

F1D= simplicialComplex {a*c, d}

F0D = simplicialComplex {a,d}

KK= filteredComplex {F2D, F1D, F0D}

K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i))|{symbol zero => KK.zero} 

-- need to add zero to K to use the spectral sequence constructor.

E0Modules = computeErModules(K,0)

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0)
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)
prune ker E0Maps#{2,-1}


E=spectralSequence(K)

E_0


-- want to compute homology of a spectral sequence page...  
-- the out put of such a function should be a hash table "isomorphic" to the 
-- modules on the next page.

rpqHomology :=(p,q,r,Er) -> ( (ker(Er.dd #{p,q})) / (image(Er.dd #{p+r,q-r+1}) ) )

(ker (E_0).dd #{2,0}) / image (E_0).dd #{2,1}


rpqHomology(2,0,0, E_0)

K_infinity


E_1 . filteredComplex _infinity
keys E_1

E_1 .pageModules #{2,0}

inducedMap(rpqHomology(2,0,0,E_0), E_1 .pageModules #{2,0}, id_(K_infinity _2))

-- want to compute the isomorphism from the homology of the rth page with
-- the r+1 th page.

rpqIsomorphism :=(p,q,r,page,nextPage) -> (
inducedMap(rpqHomology(p,q,r,page), nextPage.pageModules #{p,q}, id_(nextPage.filteredComplex _infinity _(p+q)))
  )


 
isIsomorphism rpqIsomorphism(2,0,0,E_0,E_1)

-- so the above seems to be working OK.

L=keys E_0 .dd

L#0 #0
L#0 #1


apply(keys E_0 .dd, i-> rpqIsomorphism(i#0,i#1,0,E_0,E_1))

-- so there is a bug in the above.

rpqIsomorphism(-1,2,0,E_0,E_1)

-- I think the bug is in rpqHomology.  {-1,3} is not in keys E_0 .dd .
-- Need to handle this case.

rpqHomology :=(p,q,r,Er) -> ( 
     if Er.dd #?{p+r,q-r+1} then 
     (ker(Er.dd #{p,q})) / (image(Er.dd #{p+r,q-r+1}) ) 
 else (ker(Er.dd #{p,q})) / (image(0*id_(Er.filteredComplex _infinity _ (p+q)) ))
     )
rpqHomology(-1,2,0,E_0)

rpqIsomorphism :=(p,q,r,page,nextPage) -> (
inducedMap(rpqHomology(p,q,r,page), nextPage.pageModules #{p,q}, id_(nextPage.filteredComplex _infinity _(p+q)))
  )


rpqIsomorphism(-1,2,0,E_0,E_1)

-- so the above seemed to work better.

apply(keys E_0 .dd, i-> isIsomorphism rpqIsomorphism(i#0,i#1,0,E_0,E_1))

-- so the above seems to work!! Cool!!

apply(keys E_1 .dd, i->  rpqIsomorphism(i#0,i#1,1,E_1,E_2))

-- so there seems to be a problem in the above.

keys E_1 .dd

 E_1 .pageModules
 E_2 .filteredComplex

rpqIsomorphism(2,1,1,E_1,E_2)

 rpqHomology(1,-1,1,E_1)

K_infinity _0

prune E_2 .pageModules #{1,-1}

inducedMap(rpqHomology(1,-1,1,E_1), E_2 .pageModules #{1,-1}, id_ (K_infinity) _0)

-- so the above seems to be the problem.

-- try instead
inducedMap(E_2 .pageModules #{1,-1}, rpqHomology(1,-1,1,E_1), id_ (K_infinity) _0)

-- on the otherhand, the above seems to be ok.

rpqHomology :=(p,q,r,Er) -> ( 
     if Er.dd #?{p+r,q-r+1} then 
     (ker(Er.dd #{p,q})) / (image(Er.dd #{p+r,q-r+1}) ) 
 else (ker(Er.dd #{p,q})) / (image(0*id_(Er.filteredComplex _infinity _ (p+q)) ))
     )
rpqHomology(-1,2,0,E_0)

rpqIsomorphism :=(p,q,r,page,nextPage) -> (
inducedMap(nextPage.pageModules #{p,q},rpqHomology(p,q,r,page), id_(nextPage.filteredComplex _infinity _(p+q)))
  )


rpqIsomorphism(1,-1,1,E_1, E_2)


isIsomorphism rpqIsomorphism(1,-1,1,E_1,E_2)

apply(keys E_1 .dd, i->  rpqIsomorphism(i#0,i#1,1,E_1,E_2))

apply(keys E_1 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,1,E_1,E_2))
-- cool.

apply(keys E_0 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,0,E_0,E_1))
-- cool.

apply(keys E_2 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,2,E_2,E_3))
--cool.

-- should investigate the above further.

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

------------------------------------------------------------------
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;


--try to test some aspects of SpectralSequence Code. --

A=QQ[a,b,c,d]

D=simplicialComplex {a*d*c, a*b, a*c, b*c}

F2D=D

F1D= simplicialComplex {a*c, d}

F0D = simplicialComplex {a,d}

K= filteredComplex {F2D, F1D, F0D}

E=spectralSequence K

E^infinity

E0=E^0

HH E0

E0.dd

E0 _ {2,-1}

E0 ^ {-2,1}

keys E

E1= E_1

keys E

E^infinity

-- we might want to add "ambient spectral sequence or some such thing to a spectral
-- sequence page.
-- I think we will also want to overload HH to go from one spectral sequence page
-- to another.

------------------------------------------------------------------------------------

------------------------------------------------------------------
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;


--test SpectralSequencePage Code. --

A=QQ[a,b,c,d]

D=simplicialComplex {a*d*c, a*b, a*c, b*c}

F2D=D

F1D= simplicialComplex {a*c, d}

F0D = simplicialComplex {a,d}

K= filteredComplex {F2D, F1D, F0D}

E0=spectralSequencePage(K,0)
(E0.dd)#{0,0}
E0.filteredComplex
E0.pageNumber
E0.pageModules
E0.zero

E1=spectralSequencePage(K,1)
E1.dd #{0,0}
-- We might want to add the capaility of E1.dd _{0,0} or some such thing --

E1.filteredComplex
E1.pageNumber
E1.pageModules
E1.dd
E1.zero

------------------------------------------------------------------------------------

------------------------------------------------------------
-----------------------------------------------------------

-------------------------------------------------------------
-- another example to try and which can be computed by hand.
--------------------------------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[a,b,c,d]

D=simplicialComplex {a*d*c, a*b, a*c, b*c}

F2D=D

F1D= simplicialComplex {a*c, d}

F0D = simplicialComplex {a,d}

KK= filteredComplex {F2D, F1D, F0D}

K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i))|{symbol zero => KK.zero} 

E=spectralSequence(K)

E0=E_0

E1=E_1

E2=E_2



E0Modules = computeErModules(K,0)

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0)
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)
prune ker E0Maps#{2,-1}

E1Modules=computeErModules(K,1)
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps=computeErMaps(K,1)
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)


E2Modules=computeErModules(K,2)
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

prune HH K_infinity
---------------
-- using the above we conclude that the map with source 2,-1 on the E2 page
-- must have a 1-diml image and 1-diml kernel.
-------------

E2Maps=computeErMaps(K,2)
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

prune ker E2Maps#{2,-1}

E3Modules=computeErModules(K,3)
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

---------------------------------------------------
-- the above aggrees with my calculations by hand.
---------------------------------------------------

--
-- let's try now to test the following code which seemed to work on an eariler example.

-- on the otherhand, the above seems to be ok.


rpqHomology :=(p,q,r,Er) -> ( 
     if Er.dd #?{p+r,q-r+1} then 
     (ker(Er.dd #{p,q})) / (image(Er.dd #{p+r,q-r+1}) ) 
 else (ker(Er.dd #{p,q})) / (image(0*id_(Er.filteredComplex _infinity _ (p+q)) ))
     )

rpqIsomorphism :=(p,q,r,page,nextPage) -> (
inducedMap(nextPage.pageModules #{p,q},rpqHomology(p,q,r,page), id_(nextPage.filteredComplex _infinity _(p+q)))
  )

apply(keys E_0 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,0,E_0,E_1))
-- cool.

apply(keys E_1 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,1,E_1,E_2))
-- cool.

apply(keys E_2 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,2,E_2,E_3))
-- cool.

E_2 .pageNumber

E_2 .pageModules




-----------------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[a,b,c]

-- another example which can be checked by hand.  Will try to test the code which
-- computes the "naive truncation" of a complex.

D=simplicialComplex {a*b*c}

F2D=D
F1D=simplicialComplex {a*b,a*c,b*c}
F0D=simplicialComplex {a,b,c}

K=filteredComplex {F2D,F1D,F0D}

C=K_infinity
--------------------------------------------------------------------------
-- The following shows that there is a bug in the code which is suppose to 
-- compute the naive filtration of a chain complex.
filteredComplex C
---------------------------------------------------------------------------

-- Let's try to test truncate(C,p) --

spots C
(truncate(C,1)).dd

spots C

spots truncate(C,1)

-- the above shows that there is a bug in trucate as well.  -- 

-- truncate(C,1) needs to to shifted appropriately. --

-- we also need to decide if trucate(C,p) should set all homological degrees >=p 
-- to zero
-- all homological degrees > p to zero, all degrees <= p to zero or all degrees <p to
-- zero.  

-- This will require a moments thought.


prune K

-- so prune of a filtered complex seems to be OK.
-----------------------------------------------
-- Let's check the spectral sequence code on this example
--
--
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[a,b,c]


D=simplicialComplex {a*b*c}

F2D=D
F1D=simplicialComplex {a*b,a*c,b*c}
F0D=simplicialComplex {a,b,c}

KK=filteredComplex {F2D,F1D,F0D}

-- the example I did by hand was done using non-reduced homology. --
-- should go back and try it with reduced homology later. --

K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i)) |{symbol zero => KK.zero}


C=K_infinity

prune HH C

E0Modules=computeErModules(K,0)

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0)
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)


E1Modules=computeErModules(K,1)
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps=computeErMaps(K,1)
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)
C.dd

E2Modules=computeErModules(K,2)
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

E2Maps=computeErMaps(K,2)
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

E3Modules=computeErModules(K,3)
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

----------------------------------------------------
-- the above agrees with my caclulations by hand. --
----------------------------------------------------

E=spectralSequence(K)
E_0
E_1
E_2

E_0 .pageModules

E_1 .pageModules

E_0 .pageNumber

-- let's try now to test the following code which seemed to work on an eariler example.

-- on the otherhand, the above seems to be ok.


rpqHomology :=(p,q,r,Er) -> ( 
     if Er.dd #?{p+r,q-r+1} then 
     (ker(Er.dd #{p,q})) / (image(Er.dd #{p+r,q-r+1}) ) 
 else (ker(Er.dd #{p,q})) / (image(0*id_(Er.filteredComplex _infinity _ (p+q)) ))
     )

rpqIsomorphism :=(p,q,r,page,nextPage) -> (
inducedMap(nextPage.pageModules #{p,q},rpqHomology(p,q,r,page), id_(nextPage.filteredComplex _infinity _(p+q)))
  )

apply(keys E_0 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,0,E_0,E_1))
-- cool.

apply(keys E_1 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,1,E_1,E_2))
--cool.

apply(keys E_2 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,2,E_2,E_3))
--cool.

--------------------------------------------------------
--------------------------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[x,y,z]


F3=simplicialComplex {x*y*z}

filteredComplex({F3})

simplicialComplex({})
-- I guess the simplicial complex code doesn't allow for the "empty simplicial complex"

F2=simplicialComplex {y*z, x}

filteredComplex({F3,F2})

K=filteredComplex({F3,F2})

C=chainComplex F3

m=chainComplexMap(C,C,apply(spots C, i->id_(C_i)))

L=filteredComplex({m})

K_1==K^(-1)

L_1==L^1

--------------------------------------------------




--Nathan's first example
restart
needsPackage "SpectralSequences";
needsPackage "ChainComplexExtras";
debug SpectralSequences;




-- This is the first example I studied.
-- It has the advantage that we can compute everything explicitly by hand.


k=QQ
d2=matrix(k,{{1},{0}})
d1=matrix(k,{{0,1}})

-- make a chain complex with these maps
-- throughout this example I'm thinking homologically (by default this is how M2
-- thinks of an displays chain complexes).  
-- NAMELY THE DIFFERENTIAL HAS DEGREE -1.  


C=chainComplex({d1,d2})

prune HH C

-- the above shows that C is acyclic.  
--Hence whatever spectral sequences associated to filtrations of C 
-- we compute they should abut to zero.

-- first make subcomplexes of C which will allow us to make a filtered complex


-- I want to make a filtration of the form
-- C=F3C > F2C > F1C > F0C =0.

-- first make the modules.

F3C2=image matrix(k,{{1}})
F3C1=image matrix(k,{{1,0},{0,1}})
F3C0=image matrix(k,{{1}})


-- The F3C complex. (Which should be isomorphic to C.  I want to explicitly make
-- computer realize all terms in this complex as appropriate sub-quotients.)

F3C=chainComplex({inducedMap(F3C0,F3C1,C.dd_1),inducedMap(F3C1,F3C2,C.dd_2)})
F3C==C
-- so I seem to have inputed things correctly.
-- The F2C complex. 
-- first make the modules 

F2C2= image matrix(k,{{1}})
F2C1=image matrix(k,{{1,0},{0,0}})
F2C0=image matrix(k,{{1}})
-- The F2C complex.  (Which should be a sub complex of F3C.)
F2C=chainComplex({inducedMap(F2C0,F2C1,C.dd_1),inducedMap(F2C1,F2C2,C.dd_2)})


-- It is clear that the F2C complex is a sub complex of F3C in the most obvious way.
--  Now try to construct an explicit chain complex map yielding this inclusion
-- of chain complexes.

-- Want to construct a chain complex map defining the inclusion F2C --> F3C.
-- we will label such maps by the source. (The number 2 in this case.) 


m2=chainComplexMap(F3C,F2C,{inducedMap(F3C_0,F2C_0,id_(F3C_0)), inducedMap(F3C_1,F2C_1,id_(F3C_1)),inducedMap(F3C_2,F2C_2,id_(F3C_2))})

-------------------------------------------------------------
-- The F1C complex.  (Which should satisfy the relation F3C>F2C>F1C.)

-- make the modules.

F1C2=image matrix(k,{{0}})
F1C1= image matrix(k,{{1,0},{0,0}})
F1C0 = image matrix(k,{{1}})

--  The F2C complex.  (Which should be a sub complex of F2C and F3C.  For now
-- I will make it an explicit subcomplex of F3C which will be the "ambient complex".)

F1C = chainComplex({inducedMap(F1C0,F1C1,C.dd_1),inducedMap(F1C1,F1C2,C.dd_2)})

m1=chainComplexMap(F3C,F1C,{inducedMap(F3C_0,F1C_0,id_(F3C_0)), inducedMap(F3C_1,F1C_1,id_(F3C_1)),inducedMap(F3C_2,F1C_2,id_(F3C_2))})


-- the terms / modules corresponding to the F0C complex. 
F0C2= image matrix(k,{{0}})
F0C1 = image matrix(k,{{0,0},{0,0}})
F0C0= image matrix(k,{{0}})


F0C=  chainComplex({inducedMap(F0C0,F0C1,C.dd_1),inducedMap(F0C1,F0C2,C.dd_2)})

-- try to make a chain complex map expressing F0C as a subcomplex of F3C.
m0=chainComplexMap(F3C,F0C,{inducedMap(F3C_0,F0C_0,id_(F3C_0)), inducedMap(F3C_1,F0C_1,id_(F3C_1)),inducedMap(F3C_2,F0C_2,id_(F3C_2))})

----------------------------------------------------------------------
-- Now test Nathan's spectral sequence code --------------------------
----------------------------------------------------------------------

K= filteredComplex{m2,m1,m0}


E0Modules=computeErModules(K,0)

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0)

E1Modules=computeErModules(K,1)
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps=computeErMaps(K,1)
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)


E2Modules=computeErModules(K,2)
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

E2Maps=computeErMaps(K,2)
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

E3Modules=computeErModules(K,3)
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

------------------------------------------------------------------------
--- All of the above coincidies with what I have computed by hand. -----
------------------------------------------------------------------------

--more examples--

L=filteredComplex {m2,m1}



e0modules=computeErModules(L,0)
new HashTable from apply(keys e0modules, i-> i=>prune e0modules#i)
e0maps = computeErMaps(L,0)
new HashTable from apply(keys e0maps, i-> i=> prune e0maps#i)
e1modules = computeErModules(L,1)
new HashTable from apply(keys e1modules, i-> i=>prune e1modules#i)
e1maps = computeErMaps(L,1)
new HashTable from apply(keys e1maps, i-> i=> prune e1maps#i)
e2modules = computeErModules(L,2)
new HashTable from apply(keys e2modules, i-> i=>prune e2modules#i)
e2maps = computeErMaps(L,2)
new HashTable from apply(keys e2maps, i-> i=> prune e2maps#i)
e3modules = computeErModules(L,3)
new HashTable from apply(keys e3modules, i-> i=>prune e3modules#i)

-- the above seems to work correctly.
----------------------------------------
----------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[x,y,z,w]

help SimplicialComplexes
help simplicialComplex

help simplicialComplex

F3=simplicialComplex {x*y*z*w}

filteredComplex({F3})

F2=simplicialComplex {x*y*z, x*w}

F1 = simplicialComplex {z,w}

filteredComplex({F3,F2,F1})

K=filteredComplex({F3,F2,F1})


--------------------------------------------------------------------------
--------------------------------------------------------------------------
restart
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
viewHelp SpectralSequences
--------------------------------------------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes";


-- the following is the input data for the hopf fibration--
-- This example is using a minimial triangualtion of the hopf map
-- S^1 --> S^3 -->> S^2 --
-- S^2 is the sphere on vertex set a,b,c,d.  
-- the map S^3 --> S^2 is defined by a_i --> a etc.
-- the example is
-- from a paper of Madahr, Sarkaria "Geometriae Dedicata 2000".  
-- it was a motivating example to try at the start of this project.

-- the idea is that if D is the simplicial complex associated to S^3 then
-- the fibration allows us to construction a filtration on the chain complex of D.
 

-- The simplicial complex associated to S^3 is dednoted by D below. 
-- In the above mentioned paper D is described as the simplicial complex generated by
-- The faces of the simplicial complexes I am denoting by L1, L2, L3, L4, L5.

-- Of course I'm claiming that I have inputed the data correctly -- I have checked
-- this carefully before.


-- In this example it is importation to compute the homology of the 
-- simplicial complexes without regarding the empty set as a face of the 
--simplicial complex.  I am refering to this as "non-reduced homology".
-- (I always get the terminology mixed up.)  In any event the key point is
-- that we want H_0 to compute the number of connected components.  

B=QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2]



l1={a_0*b_0*b_1*c_1,a_0*b_0*c_0*c_1,a_0*a_1*b_1*c_1,b_0*b_1*c_1*d_1,b_0*c_0*c_1*d_2,a_0*a_1*c_1*d_2,
     a_0*c_0*c_1*d_2,
     b_0*c_1*d_1*d_2}

L1=simplicialComplex(l1)
l2={b_1*c_1*c_2*a_2,b_1*c_1*a_1*a_2,b_1*b_2*c_2*a_2,c_1*c_2*a_2*d_1,c_1*a_1*a_2*d_2,b_1*b_2*a_2*d_2,b_1*a_1*a_2*d_2,c_1*a_2*d_1*d_2}

L2=simplicialComplex(l2)
l3={c_2*a_2*a_0*b_0,c_2*a_2*b_2*b_0,c_2*c_0*a_0*b_0,a_2*a_0*b_0*d_1,a_2*b_2*b_0*d_2,c_2*c_0*b_0*d_2,c_2*b_2*b_0*d_2,a_2*b_0*d_1*d_2}

L3=simplicialComplex(l3)
l4={a_0*b_0*b_1*d_1,a_0*b_1*d_0*d_1,b_1*c_1*c_2*d_1,b_1*c_2*d_0*d_1,a_0*a_2*c_2*d_1,a_0*c_2*d_0*d_1}
L4=simplicialComplex(l4)
l5={a_0*b_1*d_0*d_2,a_0*a_1*b_1*d_2,b_1*c_2*d_0*d_2,b_1*b_2*c_2*d_2,a_0*c_2*d_0*d_2,a_0*c_0*c_2*d_2}
L5=simplicialComplex(l5)

D=simplicialComplex(join(l1,l2,l3,l4,l5))
-- assuming I've entered things correctly D is supposed to be a triangulation of S^3
-- the 3 sphere.

prune HH chainComplex(D)
-- so there is homology ZZ in degree 3 so I think the above
-- input is OK.

-- We now construct filtrations of D corresponding to p-sketeltons of the fibration.
-- Again describe these in pieces.

-- For example, if pp:S^3 --> S^2 is denotes the map, then to compute
-- f1l1 below, we observe that pp^{-1}(ab) = a_0b_0b_1, a_0a_1b_1 etc.
-- (I computed these all by hand previously.) 

f1l1={a_0*b_0*b_1,a_0*a_1*b_1,a_0*c_0*c_1,a_0*a_1*c_1,a_0*a_1*d_2,d_1*d_2,b_0*b_1*c_1,b_0*c_0*c_1,
     b_0*b_1*d_1,b_0*d_1*d_2,c_1*d_1*d_2,c_0*c_1*d_2}

f1l2={b_1*a_1*a_2,b_1*b_2*a_2,c_1*c_2*a_2,c_1*a_1*a_2,a_1*a_2*d_2,a_2*d_1*d_2,b_1*c_1*c_2,b_1*b_2*c_2,b_1*b_2*d_2,d_1*d_2,c_1*d_1*d_2,c_1*c_2*d_1}


f1l3={a_2*a_0*b_0,a_2*b_2*b_0, c_2*a_2*a_0,c_2*c_0*a_0,a_2*a_0*d_1,a_2*d_1*d_2,b_2*b_0*c_2,c_2*c_0*b_0,b_2*b_0*d_2,b_0*d_1*d_2,c_2*c_0*d_2,d_1*d_2 }

f1l4={a_0*b_0*b_1,a_0*a_2,a_0*a_2*c_2,c_1*c_2,a_0*d_0*d_1,a_0*a_2*d_1,b_1*c_1*c_2,b_0*b_1,b_0*b_1*d_1,b_1*d_0*d_1,c_1*c_2*d_1,c_2*d_0*d_1}


f1l5={a_0*a_1*b_1,b_1*b_2,a_0*c_0*c_2,a_0*a_1,a_0*d_0*d_2,a_0*a_1*d_2,b_1*b_2*c_2,c_0*c_2,b_1*d_0*d_2,b_1*b_2*d_2,c_2*d_0*d_2,c_0*c_2*d_2 }

F1D=simplicialComplex(join(f1l1,f1l2,f1l3,f1l4,f1l5))
-- So F1D corresponds to filtration of D by considering the inverse images of the
-- 1-dim'l faces of the triangulation of S^2. 
-- (D corresponds to the filtration of D by considering inverse images
-- of the two dimensional faces of the triangulation of S^2.)


f0l1={a_0*a_1,b_0*b_1,c_0*c_1,d_1*d_2}


f0l2={a_1*a_2,b_1*b_2,c_1*c_2,d_1*d_2}

f0l3={a_0*a_2,b_0*b_2,c_0*c_2,d_1*d_2}
f0l4={a_0*a_2,b_0*b_1,c_1*c_2,d_0*d_1}
f0l5={a_0*a_1,b_1*b_2,c_0*c_2,d_0*d_2}

F0D=simplicialComplex(join(f0l1,f0l2,f0l3,f0l4,f0l5))

-- So F0D corresponds to the filtration of D by considering the inverse images of the 
-- 0-dimensional faces of the triangulation of S^2.

KK=filteredComplex({D,F1D,F0D});


-- to compute the serre spectral sequence of the hopf fibration S^1-> S^3 -> S^2 
-- "correctly" meaning that we get the E2 page as asserted in the theorem
-- with non-reduced homology we need the following method which removes the empty face
-- from the chain complex


KK_2
nonReducedChainComplex(KK_2)
nonReducedChainComplex(KK_1)
prune oo
prune nonReducedChainComplex(KK_0)

nonReducedChainComplex(KK_(-1))

spots KK
K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i)) 

K_2
K_1
prune K_(-1)
(chainComplex(D)).dd_1

prune HH K_2

-- Now try to compute the various pages of the spectral sequence.

-- I have not made any serious attempt to compute the E0 and E1 page by hand. --

E0Modules=computeErModules(K,0);

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0);
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)

E1Modules=computeErModules(K,1);
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps=computeErMaps(K,1);
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)


E2Modules=computeErModules(K,2);
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

-- note that the modules on the E2 page appear to have been computed correctly.  
-- the Serre spectral sequence (see for example, Theorem 1.3 p. 8 of 
-- Hatcher's Spectral Sequence book) claims that E^_{p,q}= HH_p(S^2,HH_q(S^1,QQ)).
-- This is exactly what we are suppose to get.

E2Maps=computeErMaps(K,2);
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)
-- the maps on the E2 page also seem to be computed correctly as the spectral sequence
-- will abut to the homology of S^3.


E3Modules=computeErModules(K,3);
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

E3Maps=computeErMaps(K,3);
new HashTable from apply(keys E3Maps, i-> i=> prune E3Maps#i)
----------------------------------------------------------------
-- the E3 page appears to have been computed correctly. --------
----------------------------------------------------------------

-- New example to try.  Everything in this example can be computed easily by hand. --

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes";

B=QQ[a,b,c];

D=simplicialComplex({a*b*c})

F3D=D;

F2D=simplicialComplex({a*b,a*c,b*c})
F1D=simplicialComplex({a*b,c})
F0D=simplicialComplex({a,b})

chainComplex F3D

-- the order for the filtration is given by
--  F3D>F2D>F1D>F0D >F(-1)D = 0

KK=filteredComplex {F3D,F2D,F1D,F0D}

-- in order to get the example I did by hand want to remove the
-- contribution of the empty face from these
-- chain complexes.

K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i)) 

K
prune HH K_3

E0Modules=computeErModules(K,0);

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps=computeErMaps(K,0);
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)

E1Modules=computeErModules(K,1);
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps=computeErMaps(K,1);
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)
E1Maps#{1,0}
prune ker E1Maps#{2,-1}

prune ker E1Maps#{3,-1}

E2Modules=computeErModules(K,2);
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

E2Maps=computeErMaps(K,2);
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

E3Modules=computeErModules(K,3);
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

E3Maps=computeErMaps(K,3);
new HashTable from apply(keys E3Maps, i-> i=> prune E3Maps#i)

prune HH K_3
K_3

----------------------------------------------------------------
-- All of the above agrees with what I've calculated by hand. --
----------------------------------------------------------------

-- I think that the betti table of the modules on the rth page would
-- be something meaningfull to output to user.

prune E3Modules#{0,0}

betti E3Modules#{0,0}
betti prune E3Modules#{0,0}

help betti

betti prune E3Modules#{1,0}


-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- examples by other people. ------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
restart
needsPackage "SpectralSequences";
debug SpectralSequences;
R = QQ[x,y,z]
M = R^1/ideal(vars R)
F = res M
G = res ideal(x*y,y*z,z^3)

-- Example of spectral sequence for Ext
H = Hom(F,filteredComplex G)
E = spectralSequence H
netList support E_0
netList support E_1
netList support E_infinity
lim = 10
netList apply(lim, k -> prune Ext^k(M,R^1/ideal(x*y,y*z,z^3)))

-- Example of spectral sequence for Tor
H = F ** (filteredComplex G)
E = spectralSequence H
netList support E_0
netList support E_1
netList support E_infinity
netList apply(lim, k -> prune Tor_k(M,R^1/ideal(x*y,y*z,z^3)))

-- Example of change of ring spectral sequence for Tor
S = R/(x^2-y^2)
N = S^1 /ideal(x^3,x*y^2,y^3)
G = res (N, LengthLimit => lim)
g = max G
J=ker G.dd_lim
G#(lim+1) = J
G.dd#(lim+1) = inducedMap(G_lim,G_(lim+1))
H = filteredComplex(F ** S)
see (K = H ** G)
E = spectralSequence K
netList apply(lim, k -> prune Tor_k(M,pushForward(map(S,R),N)))
netList support E_0
netList support E_1
netList support E_infinity


