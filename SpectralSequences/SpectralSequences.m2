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
  "see"
  }

-- symbols used as keys
protect minF
protect maxF
protect minH
protect maxH
protect inducedMaps

needsPackage "SimplicialComplexes"

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
-- constructing filtered complexes
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"

-- Retrieves the sorted integer keys of a hash table. 
spots = K -> sort select(keys K, i -> class i === ZZ)
max FilteredComplex := K -> max spots K
min FilteredComplex := K -> min spots K

-- Returns the pth subcomplex in a filtration of a chain complex 
-- (our filtrations are descending)
FilteredComplex ^ InfiniteNumber :=
FilteredComplex ^ ZZ := ChainComplex => (K,p) -> (
     -- We assume that spots form a consecutive sequence of integers
  (maxK, minK) := (max K, min K);  -- all filtrations are assumed separated & exhaustive
  if K#?p then K#p else if p < minK then K#minK else if p > maxK then K#maxK
  else error "expected no gaps in filtration")

chainComplex FilteredComplex := ChainComplex => K -> K^-infinity

-- Retrieves (or lazily constructs) the inclusion map from the pth subcomplex to the top
inducedMap (FilteredComplex, ZZ) := ChainComplexMap => opts -> (K,p) -> (
  if not K.cache#?inducedMaps then K.cache.inducedMaps = new MutableHashTable;
  if not K.cache.inducedMaps#?p then K.cache.inducedMaps#p = inducedMap(K^-infinity, K^p);
  K.cache.inducedMaps#p)

project := (K,p) -> (
     f:= i -> map(K^p_i,K^-infinity_i,1);
     map(K^p,K^-infinity,f)
     )

FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
  all(min(min C,min D)..max(max C,max D),i-> C^i == D^i))

net FilteredComplex := K -> (
     -- Don't want to display all filtered pieces
     -- Should we display the quotients rather than the submodules?
     -- Plan: display sequence of form "K^(min K) \supset .. \supset K^(max K)"
  v := between("", apply(sort spots K, p -> p | " : " | net K^p));
  if #v === 0 then "0" else stack v)

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

filteredComplex = method(TypicalValue => FilteredComplex)

-- Primitive constructor, takes a descending list of inclusion maps of 
-- subcomplexes of a chain complex (or simplicial complexes) 
filteredComplex List := L -> (
  local maps;
  local C;
  if #L === 0 
  then error "expected at least one chain complex map or simplicial complex";
  if all(#L, p -> class L#p === SimplicialComplex) then (
    kk := coefficientRing L#0;
    C = chainComplex L#0;	       	    -- all filtrations are exhaustive
    maps = apply(#L-1, p -> map(C, chainComplex L#(p+1), 
        i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))))
  else (
    maps = L;
    if any(#maps, p-> class maps#p =!= ChainComplexMap) then (
      error "expected sequence of chain complexes");
    C = target maps#0;	       	       	    -- all filtrations are exhaustive
    if any(#maps, p-> target maps#p != C) then (
      error "expected all map to have the same target"));     
  Z := image map(C, C, i -> 0*id_(C#i));    -- all filtrations are separated
  P := {0 => C} | apply (#maps, p -> p+1 => image maps#p);
  if (last P)#1 != Z then P = P | {#maps+1 => Z};
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})

-- Gives the homological filtration on a chain complex
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

--------------------------------------------------------------------------------
-- spectral sequences
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

filteredComplex SpectralSequence := FilteredComplex => E -> E.filteredComplex

chainComplex SpectralSequence := ChainComplex => E -> chainComplex filteredComplex E

spectralSequence = method(Options => {Degree => 1})
spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
     new SpectralSequence from {
	  symbol minF => min K,
	  symbol maxF => max K,
	  symbol maxH => - min K^-infinity,
	  symbol minH => - max K^-infinity,
	  symbol filteredComplex => K,
	  symbol zero => K.zero,
	  symbol cache => CacheTable})

-- get the inverse image of C under the map d
invSubmodule := (d,C) -> ker (inducedMap ((target d)/C,target d) * d)

-- internal functions (creating approximate cycle & boundary subquotients)

pageZ := (r, F,p,q) -> 
     (invSubmodule (F^p.dd_(-p-q),F^(p+r)_(-p-q-1)) + F^(p+1)_(-p-q))/F^(p+1)_(-p-q)

pageB := (r, F,p,q) -> 
     (intersect (image F^(p-r+1).dd_(1-p-q),F^p_(-p-q)) + F^(p+1)_(-p-q)) / F^(p+1)_(-p-q)

pageE := (r, F,p,q) -> (
     if r < 1 then F^p_(-p-q)/F^(p+1)_(-p-q) else 
     if r == 1 then ker F^p.dd_(-p-q) / image F^p.dd_(1-p-q)
     else pageZ(r,F,p,q)/pageB(r,F,p,q))


differential = method ();
differential (ZZ,FilteredComplex,ZZ,ZZ):=Matrix => (r,F,p,q) -> 
     inducedMap(pageZ(r,F,p+r,q-r+1),pageZ(r,F,p,q),F^p.dd_(-p-q))

SpectralSequenceSheet = new Type of MutableHashTable
SpectralSequenceSheet.synonym = "spectral sequence sheet"

SpectralSequence _ ZZ := SpectralSequenceSheet => (E,r) -> (
     F := filteredComplex E;
     L := for p from E.minF to E.maxF list (
	  for q from E.minH - E.maxF to E.maxH - E.minF list (
	       M := pageE(r,F,p,q);
	       if M!= 0 then {{p,q}, M} else continue));
     new SpectralSequenceSheet from flatten L | {symbol zero => E.zero})

SpectralSequenceSheet ^ List := Module => (Er,L) -> if Er#?L then Er#L else Er.zero

SpectralSequence _ InfiniteNumber := SpectralSequenceSheet => (E,r) -> (
  C:= E_0;
  if r == -infinity then C 
  else (
    maxC := max (select (keys C, i -> class i === List)/last);
    minC := min (select (keys C, i -> class i === List)/last);
    E_(maxC -minC + 1)))

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



--Nathan's first example
restart
needsPackage "SpectralSequences";
debug SpectralSequences;


-- This is the first example I studied.
-- It has the advantage that we can compute everything explicitly by hand.
-- Goal:  Try to implement the example using the current version of the code.

k=QQ
-- make some maps
d2=matrix(k,{{1},{0}})
d1=matrix(k,{{0,1}})
d1*d2



-- make a chain complex with these maps
-- throughout this example I'm thinking homologically (by default this is how M2
-- thinks of an displays chain complexes).  
-- NAMELY THE DIFFERENTIAL HAS DEGREE -1.  
--I'm assuming that the spectral sequence
-- code in this version is designed for this.


C=chainComplex({d1,d2})
(C.dd_1)*(C.dd_2)==0

C.dd_2==d2
C.dd_1==d1
prune HH C

-- the above shows that C is acyclic.  
--Hence whatever spectral sequences associated to filtrations of C 
-- we compute they should abut to zero.

-- first make subcomplexes of C which will allow us to make a filtered complex

-- We want to use homological indexing for the filtration.  

--THE CONVENTION WE WANT TO FOLLOW IS IF C IS A COMPLEX WHOSE DIFFERENTIAL HAS
-- DEGREE -1 THEN THE FILTRATION SHOULD HAVE THE SHAPE
-- F_nC > F_(n-1)C. (See section 5.4 of Weibel.) 
-- Q:  IS THIS ASSCENDING OR DESCENDING?? (I always forget the terminology.)
-- 
--We will need to implement K_n operation for a filtered complex. 
--  for now K^(-n) should produce what we want although things will be shifted.

-- For now try to make appropriate chain complex maps to test the filtered complex
-- constructor.

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

prune F2C.dd_1
prune F2C.dd_2
prune HH F2C

-- It is clear that the F2C complex is a sub complex of F3C in the most obvious way.
--  Now try to construct an explicit chain complex map yielding this inclusion
-- of chain complexes.

-- now want to construct a chain complex map defining the inclusion F2C --> F3C.
-- we will label such maps by the source. (The number 2 in this case.) 


m2=chainComplexMap(F3C,F2C,{inducedMap(F3C_0,F2C_0,id_(F3C_0)), inducedMap(F3C_1,F2C_1,id_(F3C_1)),inducedMap(F3C_2,F2C_2,id_(F3C_2))})

needsPackage "ChainComplexExtras"

m2=chainComplexMap(F3C,F2C,{inducedMap(F3C_0,F2C_0,id_(F3C_0)), inducedMap(F3C_1,F2C_1,id_(F3C_1)),inducedMap(F3C_2,F2C_2,id_(F3C_2))})

-- apparently we need the package "ChainComplexExtras"
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
--try now to make filteredComplex.
filteredComplex({m1,m2})
-- the indexing of the filtertration should be different than mine, 
-- but what should be true is that the complex with label 2 should
-- be a sub complex of the complex with label 1 which is clearly not the case.

-- try different order.
filteredComplex({m2,m1})
-- that seems to work better.  (the indexing is still different from mine which I would
-- like to change.

-- also by default the constuctor seems to add the zero complex.

-- also by default the constructor seems to add the zero complex. 
-- what happens if I explicilty add the zero complex?
K=filteredComplex({m2,m1,m0})

-- no extra terms seem to be added.  So this seems to be OK.

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
-- now let's try the existing spectral sequence code.
-- computing the spectral sequence by hand yeilds 4-nonzero modules on the E0 page
-- all maps on the E0 page are zero, 4 nonzero modules on the E1 page, one non-zero
-- map on the E1 page (which is an isomorphism), 2 nonzero modules on the E2 page, one
-- non-zero map on the E2 page (which is an isomorphism) and the spectral sequence
-- abuts to zero on the E3 page.  

E=spectralSequence K

support E_0
support E_1
-- since there are suppose to be 4 non-zero modules on the E1 page there must be an
-- error in the existing code some where.
-- I won't bother trying to compute the maps.
--------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
-- we want to have an underscore operator for filtered complexes.
-- this can be done easily as follows.
--  Essentially copying the ^ method -- I'm assuming that it works OK.

FilteredComplex _ ZZ := ChainComplex => (K,p) -> (
     -- We assume that spots form a consecutive sequence of integers
  (maxK, minK) := (max K, min K);  -- all filtrations are assumed separated & exhaustive
  if K#?p then K#p else if p < minK then K#minK else if p > maxK then K#maxK
  else error "expected no gaps in filtration")

-- examples
K_0
K_1
K_2

maps={m2,m1,m0}
#maps

 {(#maps) => C} | apply (#maps,  p -> #maps - (p+1) => image maps#p)


homologicalFilteredComplex=method()
homologicalFilteredComplex( )

-- Primitive constructor, takes a list eg {m_n,m_(n-1), ...,m_0} 
-- defining inclusion maps C=F_nC > F_(n-1)C > ... > F_0 C = 0
-- -- subcomplexes of a chain complex (or simplicial complexes) 
-- and produces a filtered complex with integer keys the
-- corresponing  chain complex.
-- this should be merged with the filtered complex constructor and should be
-- the default.  An option should allow the user to choose to
-- do things cohomologically.


homologicalFilteredComplex List := L -> (
  local maps;
  local C;
  if #L === 0 
  then error "expected at least one chain complex map or simplicial complex";
  if all(#L, p -> class L#p === SimplicialComplex) then (
    kk := coefficientRing L#0;
    C = chainComplex L#0;	       	    -- all filtrations are exhaustive
    maps = apply(#L-1, p -> map(C, chainComplex L#(p+1), 
        i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))))
  else (
    maps = L;
    if any(#maps, p-> class maps#p =!= ChainComplexMap) then (
      error "expected sequence of chain complexes");
    C = target maps#0;	       	       	    -- all filtrations are exhaustive
    if any(#maps, p-> target maps#p != C) then (
      error "expected all map to have the same target"));     
  Z := image map(C, C, i -> 0*id_(C#i));    -- all filtrations are separated
  -- THE FOLLOWING LINE HAS BEEN CHANGED FROM THE FILTERED COMPLEX CONSTRUCTOR
  P := {(#maps) => C} | apply (#maps,  p -> #maps - (p+1) => image maps#p);
  if (last P)#1 != Z then P = P | {#maps+1 => Z};
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})

K=homologicalFilteredComplex {m2,m1,m0}

K
K_0
K^0
K^1
K_1

K_1==K^1

K^infinity


-- so want the relationship between K_n and K^n is that K_n=K^(-n).


---------------------------------------------------------------
-- examples by other people.
---------------------------------------------------------------

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

