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
  Version => "0.4",
  Date => "13 September 2012",
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
  "see", 
  "computeErModules",
  "computeErMaps", 
  "spots",
  --"nonReducedChainComplex",
  "SpectralSequencePage", 
  "spectralSequencePage",
  "rpqHomology",
  "rpqIsomorphism",
  "lessThanOrEqual", 
  "Shift",
  "greaterThanOrEqual", "ReducedHomology"
  }

-- symbols used as keys
--protect minF
--protect maxF
--protect minH
--protect maxH
protect inducedMaps
--protect pageNumber
--protect pageModules
--protect pageMaps
needsPackage "SimplicialComplexes"
needsPackage "ChainComplexExtras"

--------------------------------------------------------------------------------
-- Retrieves the sorted integer keys of a hash table. 


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

--
-- I need the following method in my examples. 
--(Surely someting like it exists elsewhere.)
-- Many of the examples I computed by
-- hand arose from "simplicial complexes without the empty face."
-- the out of the box chain complex code for simplicial complexes produces chain complexes
-- which include the empty face.
-- 
-----------------------------------------------------------------------------------
nonReducedChainComplex=method()
nonReducedChainComplex(ChainComplex):= K->(
  l:=apply(drop(sort spots K,1),i-> i);
  p:= (for i from 1 to #l-1 list K.dd_i);
chainComplex(p)
 )


-------------------------------------------------------------------------------------
-- filtered complexes
-------------------------------------------------------------------------------------
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"


-- Primitive constructor, takes a list eg {m_n,m_(n-1), ...,m_0} 
-- defining inclusion maps C=F_(n+1)C > F_(n-1)C > ... > F_0 C 
-- of subcomplexes of a chain complex (or simplicial complexes) 
-- and produces a filtered complex with integer keys the
-- corresponing chain complex.
-- If F_0C is not zero then by default F_(-1)C is added and is 0.
-- I THINK THIS IS THE CONVENTION WE WANT BY DEFAULT.  SEE 
-- THE HOPF FIBRATION EXAMPLE.  TO GET THE CORRECT INDICIES ON THE E2 PAGE
-- WE WANT THE ZERO COMPLEX TO HAVE "FILTRATION DEGREE -1".

filteredComplex = method(Options => {
    Shift => 0,
    ReducedHomology => true})
filteredComplex List := FilteredComplex => opts -> L -> (
  local maps;
  local C;
  if #L === 0 
  then error "expected at least one chain complex map or simplicial complex";
  if all(#L, p -> class L#p === SimplicialComplex) then (
    kk := coefficientRing L#0;
    
    if opts.ReducedHomology == true then (
    C = chainComplex L#0; -- By default the ambient simplicial complex is the first element of the list
    maps = apply(#L-1, p -> map(C, chainComplex L#(p+1), 
        i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))))
else (C = greaterThanOrEqual(chainComplex L#0,0); -- By default the ambient simplicial complex is the first element of the list
    maps = apply(#L-1, p -> map(C, greaterThanOrEqual(chainComplex L#(p+1),0), 
        i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))))
   
 )
  else (
    maps = L;
    if any(#maps, p-> class maps#p =!= ChainComplexMap) then (
      error "expected sequence of chain complexes");
    C = target maps#0;-- By default the ambient chain complex is target of first map.
    if any(#maps, p-> target maps#p != C) then (
      error "expected all map to have the same target"));     
  Z := image map(C, C, i -> 0*id_(C#i)); -- make zero subcomplex as a subcomplex of ambient complex 
 P := {(#maps-opts.Shift) => C} | apply (#maps,  p -> #maps - (p+1) -opts.Shift => image maps#p);
  if (last P)#1 != Z then P = P | {(-1-opts.Shift) => Z};
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})


spots = method()
spots ChainComplex := List => (cacheValue symbol spots)(
  C -> sort select(keys C,i -> class i === ZZ))
spots FilteredComplex := List => (cacheValue symbol spots)(
  K -> sort select(keys K, i -> class i === ZZ))
max HashTable := K -> max spots K
min HashTable := K -> min spots K

FilteredComplex _ InfiniteNumber :=
FilteredComplex _ ZZ := ChainComplex => (K,p) -> (
  if K#?p then K#p 
  else if p < min K then K#(min K) 
  else if p > max K then K#(max K))

FilteredComplex ^ InfiniteNumber :=
FilteredComplex ^ ZZ := ChainComplex => (K,p) -> K_(-p)

chainComplex FilteredComplex := ChainComplex => K -> K_infinity



-- Retrieves (or lazily constructs) the inclusion map from the pth subcomplex to the top
inducedMap (FilteredComplex, ZZ) := ChainComplexMap => opts -> (K,p) -> (
  if not K.cache#?inducedMaps then K.cache.inducedMaps = new MutableHashTable;
  if not K.cache.inducedMaps#?p then K.cache.inducedMaps#p = inducedMap(K_infinity, K_p);
  K.cache.inducedMaps#p)


net FilteredComplex := K -> (
  v := between("", apply(spots K, p -> p | " : " | net K_p));
  if #v === 0 then "0" else stack v)



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




--------------------------------------------------------------------------------
-- spectral sequence pages
--------------------------------------------------------------------------------
SpectralSequencePage = new Type of MutableHashTable
SpectralSequencePage.synonym = "spectral sequence page"
SpectralSequencePage.GlobalAssignHook = globalAssignFunction
SpectralSequencePage.GlobalReleaseHook = globalReleaseFunction

spectralSequencePage = method ()
spectralSequencePage(FilteredComplex, ZZ):= (K,r) ->( 
new SpectralSequencePage from 
 {symbol filteredComplex=> K, 
     symbol degree =>{-r,r-1}, 
     -- maybe instead of page number we should use degree??  symbol degree = (-r,r-1).  This is the 
     -- bidegree of the differential.
   --we don't need a key with
   -- pageModules.  We can get this by
   -- looking at the source of the differential at the pq spot
      symbol dd => computeErMaps(K,r), 
     symbol zero => (ring K_infinity)^0})



-- in the following we are assuming that user is inputing a list of 
-- pairs of integers.
-- should return an error message if this isn't the case.

SpectralSequencePage _ List := Module => (E,i)-> if (E.dd)#?i then 
source(E.dd #i) else image(0*id_((E.filteredComplex_infinity)_(sum i)))  

SpectralSequencePage ^ List := Module => (E,i)-> (E_(-i))    

-- view the modules on a Spectral Sequence Page.  We are refering to these
-- as the support of the page.

support SpectralSequencePage := E->(
     new HashTable from apply(keys E.dd, i-> i=> source E.dd #i) )



--------------------------------------------------------------------------------
-- spectral sequences 
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

-- In the following we are using the rule 
-- if r> max K - min K then E^r_{p,q}=E^r'_{p,q} for all r'>=r.
SpectralSequence ^ InfiniteNumber:=
  SpectralSequence ^ ZZ := SpectralSequencePage => (E,r) -> (
       if E#?r then E#r else 
       (if r> (max E.filteredComplex) - (min E.filteredComplex) then
	    E#r= spectralSequencePage(E.filteredComplex,(max E.filteredComplex) - (min E.filteredComplex))
	    else
       E#r= spectralSequencePage(E.filteredComplex,r);); 
       E#r
       )

SpectralSequence _ InfiniteNumber :=
SpectralSequence _ ZZ := SpectralSequencePage => (E,r) -> ( E^r       )


-- the following computes the homology at the pq spot on the rth page.
rpqHomology = method()
rpqHomology(SpectralSequence,ZZ,ZZ,ZZ) :=(E,p,q,r) -> ( 
     if E^r .dd #?{p+r,q-r+1} then 
     (ker(E^ r.dd #{p,q})) / (image(E^ r.dd #{p+r,q-r+1}) ) 
 else (ker(E^ r.dd #{p,q})) / (image(0*id_(E^ r.filteredComplex _infinity _ (p+q)) ))
     )

-- the following computes the isomorphism of the homology at the pq spot
-- on the r-th page and the module on at the pq spot on the r+1-th page.
rpqIsomorphism = method()
rpqIsomorphism(SpectralSequence,ZZ,ZZ,ZZ) :=(E,p,q,r) -> (
inducedMap(source (E^(r+1) .dd #{p,q}),rpqHomology(E,p,q,r), id_(E^(r+1) .filteredComplex _infinity _(p+q)))
  ) 

--------------------------------------------------------------------------------
-- constructing filtered complexes ---------------------------------------------
--------------------------------------------------------------------------------

-- Nathan's comments.
-- The following is basically the same as truncate, except that I've
-- used different names because I think it is ambigous to use truncate.
-- also we have a choice whether to use lessThanOrEqual or simply lessThan.
-- to construct the filtraions C**C properly using Weibel's conventions
-- on p. 141 Defn 5.6.1 then I think we want to use lessThanOrEqual.

-- The following produces the chain complex C<=p.
-- i.e., this is the chain complex  
-- constings of those modules in homological degree <= p and zero in
-- homological degree >p.  I oringinally thought truncate would be a good name for 
-- this but this is ambigous.  
--I tried to overload <= but computer didn't like that. --
-- try this instead.

lessThanOrEqual = method()
lessThanOrEqual(ChainComplex,ZZ):=(C,p) -> (
    if p>= max C then return C else (
     K:=new ChainComplex;
     K.ring=C.ring;
     for i from min C +1 to max C do (
     if i <= p then K.dd_i=C.dd_i else (
if i-1>p then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
else K.dd_i=inducedMap(C_(i-1), 0*C_i, C.dd_i) );););
K ) 


-- now want to produce the chain complex constiting of 
-- modules in homolocial degrees greater than 
-- or equal to n and zero in degrees less than n.
greaterThanOrEqual = method()

greaterThanOrEqual(ChainComplex,ZZ):= (C,p)->(if p<= min C then return C else (
     K:=new ChainComplex;
     K.ring=C.ring;
     for i from min C+1  to max C do (
     if i-1 >= p then K.dd_i=C.dd_i else (
if i<p then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
else K.dd_i=inducedMap(0*C_(i-1), C_i, 0*C.dd_i) );););
K )



-- the following method truncates a chain complex -- setting all
-- modules in degrees >= p to zero.
truncate (ChainComplex, ZZ) := ChainComplex => (C,p) -> (
    if p> max C then return C else (
     K:=new ChainComplex;
     K.ring=C.ring;
     for i from min C +1 to max C do (
     if i < p then K.dd_i=C.dd_i else (
if i-1>=p then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
else K.dd_i=inducedMap(C_(i-1), 0*C_i, C.dd_i) );););
K ) 


-- the following method truncates a chain complex -- setting all 
-- modules in degrees <=p to zero.

truncate (ZZ,ChainComplex) := ChainComplex => (p,C) -> (
    if p< min C then return C else (
     K:=new ChainComplex;
     K.ring=C.ring;
     for i from min C+1  to max C do (
     if i-1 > p then K.dd_i=C.dd_i else (
if i<=p then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
else K.dd_i=inducedMap(0*C_(i-1), C_i, 0*C.dd_i) );););
K ) 



filteredComplex ChainComplex := FilteredComplex =>opts-> C -> (
     complete C;
filteredComplex (apply(drop(rsort spots C,1), i -> 
     inducedMap(C,lessThanOrEqual(C,i))), Shift => (- min C) )    -- need to account for shift
-- of course can use truncate instead of lessThanOrEqual.
    )  

-- the following is be rewritten above.
-- it will be off by a dimension shift if we are using
-- the primative constructor.
--filteredComplex ChainComplex := C -> (
--     complete C;
--     filteredComplex apply(drop(rsort spots C,1), i -> inducedMap(C,truncate(C,i+1))))  
---------------------------------------------------------------
----------------------------------------------------------------
-- the following should be rewritten to go through the primative constructor.
-- will have to either shift or add options if we re-write.
-- the following code is doing what it is supposed to.

FilteredComplex ** ChainComplex := FilteredComplex => (K,C) -> (
--  filteredComplex for p from min K to max K list inducedMap(K,p) ** C)
new FilteredComplex from (for p from min K to max K list p=> (K_p ** C) ) | {symbol zero => image (0*id_(K_infinity ** C)), symbol cache =>  new CacheTable}
)
ChainComplex ** FilteredComplex := FilteredComplex => (C,K) -> (
--  filteredComplex for p from min K to max K list C ** inducedMap(K,p))
new FilteredComplex from (for p from min K to max K list p=> (C ** K_p) ) | {symbol zero => image (0*id_(C**K_infinity)), symbol cache =>  new CacheTable}
)

Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
-- filteredComplex for p from min K to max K list Hom(project(K,p),C)))
 new FilteredComplex from (for p from min K to max K list p=> (Hom(K_p,C)  )) | {symbol zero => image (0*id_(Hom(K_infinity,C))), symbol cache =>  new CacheTable}
)
Hom (ChainComplex, FilteredComplex):= FilteredComplex => (C,K) -> (
--  filteredComplex for p from min K to max K list Hom(C,inducedMap(K,p)))
 new FilteredComplex from (for p from min K to max K list p=> (Hom(C,K_p))  ) | {symbol zero => image (0*id_(Hom(C,K_infinity))), symbol cache =>  new CacheTable}

)


prune FilteredComplex := FilteredComplex => opts -> F -> 
  new FilteredComplex from 
  apply(keys F, p -> if class p =!= Symbol then p => prune F#p else p => F#p)




filteredComplex SpectralSequence := FilteredComplex => E -> E.filteredComplex

chainComplex SpectralSequence := ChainComplex => E -> chainComplex filteredComplex E

------------------------------------------------------------------------------------
-- ChainComplexExtraExtras 
--------------------------------------------------------------------------------------

  
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



--project := (K,p) -> (
--     f:= i -> map(K^p_i,K^-infinity_i,1);
--     map(K^p,K^-infinity,f)
--     )



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


  
--FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
--  all(min(min C,min D)..max(max C,max D),i-> C_i == D_i))




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

--SpectralSequenceSheet = new Type of MutableHashTable
--SpectralSequenceSheet.synonym = "spectral sequence sheet"


--SpectralSequenceSheet ^ List := Module => (Er,L) -> if Er#?L then Er#L else Er.zero


--support SpectralSequenceSheet := List => E -> 
--  apply (select(keys E,i -> class i === List), j -> j => prune E^j)
  
--SpectralSequenceSheet == SpectralSequenceSheet := Boolean => (E,F) -> 
--  all(keys E, i-> F#?i and E#i == F#i)
     
--changeofRing = method ();
--changeofRing (Module,Module):= SpectralSequence => (M,N) -> 
--     spectralSequence ((filteredComplex ((res M) ** ring N)) ** (res N))


load "Doc/SpectralSequencesDoc.m2"
end

--------------------------------------------------------------------------------
restart
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
viewHelp SpectralSequences
--------------------------------
-- some scratch code --
-- trying to compute the differential on the "homology spectral sequence page"
-- the function/method we want is the following.  
rpqHomologyDifferential = method()

rpqHomologyDifferential(SpectralSequence,ZZ,ZZ,ZZ):= (E,p,q,r) ->(
(inverse rpqIsomorphism(E,p-r-1,q+r) ) * (E^(r+1) .dd#{p,q}) * rpqIsomorphism(E,p,q,r)
)

-- try to test this in an example. --

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



spots KK

KK

K=filteredComplex({F2D,F1D,F0D},ReducedHomology => false)

E=spectralSequence K

E^1 .dd#{0,0}
rpqIsomorphism(E,0,0,1)

rpqHomologyDifferential = method()

rpqHomologyDifferential(SpectralSequence,ZZ,ZZ,ZZ):= (E,p,q,r) ->(
(inverse rpqIsomorphism(E,p-r-1,q+r,r) ) * ((E^(r+1)) .dd#({p,q})) * rpqIsomorphism(E,p,q,r)
)

rpqHomologyDifferential(E,0,0,1)

rpqIsomorphism(E,-2,1,1)
-- so the above shows that there is a bug in rpqIsomomorphism.  Need to be more careful
-- to account for what should happen if the key is not in the HashTable.

E^2 .dd#{0,0}


keys E^1 .dd

rpqHomologyDifferential(E,2,0,1)

rpqHomologyDifferential(E,2,-1,1) 

prune rpqHomologyDifferential(E,2,-1,1) == prune E^2 .dd #{2,-1}

-- so maybe there is hope to this.


-------------------------------------------------------------------------------
-- Working Examples ----------------------------------------------
------------------------------------------------------------------
-------------------------------------
-- Balancing Tor. --
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[x,y,z,w]

help monomialCurveIdeal
I= coker gens monomialCurveIdeal(A,{1,2,3})
H=complete res I

J= coker gens monomialCurveIdeal(A,{1,3,4})
F= complete res J


H
length H
spots H
filteredComplex H
-- so the filteredComplex code is doing what it is supposed to.
-- the filtration starts at 3 and then continues.
-- perhaps its better to remove the 0 in degree 3?



prune ((filteredComplex H)** F)

E= spectralSequence ((filteredComplex H) ** F)

new HashTable from apply(keys support E_0, i-> i=> prune E_0 _i)

new HashTable from apply(keys support E_1, i-> i=> prune E_1 _i)

new HashTable from apply(keys support E_2, i-> i=> prune E_2 _i)

Tor_0(J,I) == E^2 _{0,0}

prune Tor_1(J,I)

prune E^2 _{1,0} == prune Tor_1(J,I)

(Tor_1(J,I)) == (E^2 _{1,0}) -- this resturned false for some reason.  Strange...
peek Tor_1(J,I)
peek E^2 _{1,0}

EE=spectralSequence(H**(filteredComplex F))
new HashTable from apply(keys support EE_0, i-> i=> prune EE_0 _i)

new HashTable from apply(keys support EE_1, i-> i=> prune EE_1 _i)

new HashTable from apply(keys support EE_2, i-> i=> prune EE_2 _i)

Tor_0(I,J) == EE ^2 _{0,0}

prune Tor_1(I,J)

prune E^2 _{1,0} == prune Tor_1(I,J)

Tor_1(I,J) == EE^2 _{1,0} -- this resturned false for some reason.  Strange...

---------------------------------------------------------------------
----------------------------------------------------------------------


-------------------------------------------------------------------------------
-- some more examples to test code. --
-- these are more "scratch examples" than anything else. --
------------------------------------------------------------------------------
--  test truncate(ChainComplex, ZZ) code. --

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";

A=QQ[a,b,c,d]

D=simplicialComplex {a*d*c, a*b, a*c, b*c}

filteredComplex {D}

filteredComplex({D}, ReducedHomology => false)

C=chainComplex D


greaterThanOrEqual(C,0)
truncate(-1,C)
greaterThanOrEqual(C,3)
greaterThanOrEqual(C,2)
greaterThanOrEqual(C,1)
lessThanOrEqual(C,2)
C
lessThanOrEqual(C,1)
truncate(C,1)

K= filteredComplex {id_C}
filteredComplex ({id_C}, Shift=>-1)

filteredComplex{D}
filteredComplex{D,D}


F1C=lessThanOrEqual(C,0)

m1=inducedMap(C,F1C)


K=filteredComplex {m1}


-----------
--- want to try to test rpqHomology and rpqIsomorphism code.


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


K=filteredComplex({F2D, F1D, F0D}, ReducedHomology => false)

E=spectralSequence(K)


E^0
E^1
E^2
E^3

support E^0
E^0 _{1,1}
E^0 _{2,-1}

support E^1

E^1 _{2,-2}

support E^2
support E^3



apply(keys E_1 .dd, i->  rpqIsomorphism(E,i#0,i#1,1))

E^1 .dd


apply(keys E^0 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- cool.

apply(keys E^0 .dd, i->  inverse rpqIsomorphism(E,i#0,i#1,0))
-- so this should let us return a spectral sequence page (with the maps) when we
-- take homology of a spectral sequence page.

peek inverse rpqIsomorphism(E,-1,1,0)

apply(keys E^1 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
-- cool.

apply(keys E^2 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
-- cool.

-----------------------------------------------------------------
-- end of "scratch examples"

-------------------------------------------------------------------

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

------------------------------------------------------------
-----------------------------------------------------------

-------------------------------------------------------------
-- another example to try and which can be computed by hand.
-- this is example 2 in my notes.
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

K= filteredComplex({F2D, F1D, F0D},ReducedHomology => false)

E=spectralSequence(K)


E0Modules = computeErModules(K,0)

support E_0

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

new HashTable from apply(keys (support E^0), i-> i=> prune (support E^0)#i)


E0Maps=computeErMaps(K,0)

E^0 .dd

new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)
prune ker E^0 .dd#{2,-1}

prune ker E^0 .dd#{2,0}


new HashTable from apply(keys E^0 .dd, i-> i=> prune (E^0 .dd )#i)


support E^1
E1Modules=computeErModules(K,1)
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)
new HashTable from apply(keys (support E^1), i-> i=> prune (support E^1)#i)

E^1 .dd
E1Maps=computeErMaps(K,1)
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)
new HashTable from apply(keys E^1 .dd, i-> i=> prune (E^1 .dd )#i)

support E^2
E2Modules=computeErModules(K,2)
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)
new HashTable from apply(keys (support E^2), i-> i=> prune (support E^2)#i)

prune HH K_infinity
---------------
-- using the above we conclude that the map with source 2,-1 on the E2 page
-- must have a 1-diml image and 1-diml kernel.
-------------

E^2 .dd
E2Maps=computeErMaps(K,2)
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)
new HashTable from apply(keys E^2 .dd, i-> i=> prune (E^2 .dd )#i)


prune ker E2Maps#{2,-1}

E3Modules=computeErModules(K,3)
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)
new HashTable from apply(keys (support E^3), i-> i=> prune (support E^3)#i)

new HashTable from apply(keys (support E^infinity), i-> i=> prune (support E^infinity)#i)

---------------------------------------------------
-- the above aggrees with my calculations by hand.
---------------------------------------------------



apply(keys E^0 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- cool.

apply(keys E^1 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
-- cool.

apply(keys E^2 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
-- cool.

apply(keys E^5 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,5))
-- cool.
----------------------------------------------------------

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
-- New example to try.  Everything in this example can be computed easily by hand. ---
-- This is example 1 in my notes.-----------------------------------------------------
--------------------------------------------------------------------------------------
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


K=filteredComplex({F3D,F2D,F1D,F0D}, ReducedHomology => false)

K
prune HH K_3

E=spectralSequence K
E0Modules= support E^0;


new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps= E^0 .dd;
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)

E1Modules= support E^1;
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps= E^1 .dd;
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)
prune ker E1Maps#{1,0}
prune ker E1Maps#{2,-1}

prune ker E1Maps#{3,-1}

E2Modules= support E^2;
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

E2Maps=E^2 .dd;
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

prune HH K_3
K_3

new HashTable from apply(keys support E^infinity, i->i=> prune (support E^infinity)#i) 

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

------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- Let's check the spectral sequence code in another example
--  This is example 3 in my notes.
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

K=filteredComplex({F2D,F1D,F0D}, ReducedHomology => false)


C=K_infinity

prune HH C

E=spectralSequence K

E0Modules= support E^0

new HashTable from apply(keys E0Modules, i-> i=> prune E0Modules#i)

E0Maps= E^0 .dd
new HashTable from apply(keys E0Maps, i-> i=> prune E0Maps#i)


E1Modules=support E^1
new HashTable from apply(keys E1Modules, i-> i=> prune E1Modules#i)

E1Maps= E^1 .dd
new HashTable from apply(keys E1Maps, i-> i=> prune E1Maps#i)
C.dd

E2Modules= support E^2
new HashTable from apply(keys E2Modules, i-> i=> prune E2Modules#i)

E2Maps= E^2 .dd
new HashTable from apply(keys E2Maps, i-> i=> prune E2Maps#i)

E3Modules= support E^3
new HashTable from apply(keys E3Modules, i-> i=> prune E3Modules#i)

prune HH K_infinity
----------------------------------------------------
-- the above agrees with my caclulations by hand. --
----------------------------------------------------


apply(keys E^0 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- cool.

apply(keys E^1 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
-- cool.

apply(keys E^2 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
-- cool.

apply(keys E^5 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,5))
-- cool.


--------------------------------
-- End of updated examples. --
-------------------------------
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

--------------------------------------------------
--
-------------------------------------
--Nathan's first example
-- this is example 0 in my notes.
-------------------------------------
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


E=spectralSequence(K)

apply(keys E^0 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- cool.

apply(keys E^1 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
-- cool.

apply(keys E^2 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
-- cool.

apply(keys E^5 .dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,5))
-- cool.


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

-- this example needs to be updated. --

-----------------------------------------------------


restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes";
needsPackage "ChainComplexExtras";


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

KK
nonReducedChainComplex(KK_1)
prune oo
prune nonReducedChainComplex(KK_0)

nonReducedChainComplex(KK_(-1))

spots KK
K=new FilteredComplex from apply(spots KK, i-> i=> nonReducedChainComplex(KK_i))|{symbol zero => KK.zero, symbol cache =>  new CacheTable} 

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



apply(keys E^0 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,0,E^0,E^1))
-- cool.
apply(keys E^1 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,1,E^1,E^2))
-- cool.
apply(keys E^2 .dd, i->  isIsomorphism rpqIsomorphism(i#0,i#1,2,E^2,E^3))
-- cool.



--------------------------------------------------------------------------
--------------------------------------------------------------------------


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


