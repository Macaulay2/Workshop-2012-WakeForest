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
--  AuxiliaryFiles => true,
  Version => "0.6",
  Date => "28 Aug 2013",
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
      Email => "ngrieve@math.mcgill.ca",
      HomePage => "http://www.math.mcgill.ca/ngrieve"},             
    {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"},
 {
      Name => "Thanh Vu", 
      Email => "vqthanh@math.berkeley.edu",
      HomePage => "http://math.berkeley.edu/~thanh"}},
  Headline => "spectral sequences",
  DebuggingMode => true,
  PackageImports => {"SimplicialComplexes", "ChainComplexExtras"},
  PackageExports => {"SimplicialComplexes", "ChainComplexExtras"}
  )

export {
  "FilteredComplex",
  "filteredComplex",
  "SpectralSequence",
  "spectralSequence",
--  "see", 
  "computeErModules",
  "computeErMaps", 
  "spots",
  "SpectralSequencePage", 
  "spectralSequencePage",
  "rpqHomology",
  "rpqIsomorphism",
  "Shift",
  "ReducedHomology","project",
  "SpectralSequencePageMap",
  "spectralSequencePageMap",
 -- "pprune",
  "epqrMaps",
  "pruneEpqrMaps",
  "epq",
  "connectingMorphism",
  "sourcePruningMap",
  "targetPruningMap",
   "Page", "PageMap", "InfiniteSequence", "SequenceMap", "pageMap", "page", "next",
  "prunningMaps", "DoubleChainComplex", "DoubleChainComplexMap", "xx", "yy"
  }


protect inducedMaps

--------------------------------------------------------------------------------

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

------------------------------------------------------
------------------------------------------------------


--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------

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
-- THIS IS THE CONVENTION WE WANT BY DEFAULT.  SEE 
-- THE HOPF FIBRATION EXAMPLE.  TO GET THE CORRECT INDICIES ON THE E2 PAGE
-- WE WANT THE ZERO COMPLEX TO HAVE "FILTRATION DEGREE -1".

filteredComplex = method(Options => {
    Shift => 0,
    ReducedHomology => true, Left => false, Right => false, symbol Hom => false})

filteredComplex(List) := FilteredComplex => opts -> L -> (
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
    else (C = truncate(chainComplex L#0,1); -- By default the ambient simplicial complex is the first element of the list
    maps = apply(#L-1, p -> map(C, truncate(chainComplex L#(p+1),1), 
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

-- we need to be careful with spots here!!  
-- ChainComplexes are new types of GradedModules, which are new types of MutableHashTables.
-- As such the keys of a ChainComplex are mutable.  So we probably do not
-- want to cache spots of a chain complex.
-- The keys of a FilteredComplex are not mutable, so it is OK to cache them.
-- Similarly, the support of a chain complex should not be cached, as the keys of the chain complex are not mutable.

spots = method()
spots ChainComplex := List => (cacheValue symbol spots)(
  C -> sort select(keys C,i -> class i === ZZ))
spots FilteredComplex := List => (cacheValue symbol spots)(
  K -> sort select(keys K, i -> class i === ZZ))
max HashTable := K -> max spots K
min HashTable := K -> min spots K

support ChainComplex := List => (cacheValue symbol support)(
     C -> sort select (spots C, i -> C_i != 0))


FilteredComplex _ InfiniteNumber :=
FilteredComplex _ ZZ := ChainComplex => (K,p) -> (
  if K#?p then K#p 
  else if p < min K then K#(min K) 
--  else if p > max K then image id_(K#(max K))
  else if p > max K then K#(max K)
  )

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
-- This is used in the formula's below.

-- the formula's below are the homological versions of the ones in I.2.4 of Danilov's 
-- treatment of spectral sequences in Shafarevich's Encyolpaedia of 
-- Math Algebraic Geometry II.  
-- In any event it is easy enough to prove directly that they satisfy the requirments 
-- for a spectral sequence.

zpq := (K,p,q,r)->(
ker inducedMap((K_infinity)_(p+q-1) / K_(p-r) _ (p+q-1), 
     K_p _ (p+q), K_(infinity).dd_(p+q), Verify => false)
--     K_p _ (p+q), K_(infinity).dd_(p+q))
     )



bpq := (K,p,q,r) ->(
    ( image (K_(p+r-1).dd_(p+q+1))) + (K_(p-1) _ (p+q))
      )

-- the following will compute the pq modules on the rth page explicitly.
epq = method()
epq(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r)->(  ((zpq(K,p,q,r)+bpq(K,p,q,r)) / bpq(K,p,q,r)) )


-- the following computes all modules on the r-th page.

computeErModules = method()

computeErModules(FilteredComplex,ZZ) := (K,r) -> (myList:={};
     for p from min K to max K do (
	  for q from -p + min K_(infinity) to max K_(infinity) do (--length K_(max K) do (
	       myList = append(myList, {p,q}=> epq(K,p,q,r)); )
	       	    );
	       new HashTable from myList
      )

-- the following will compute the pq maps on the rth page explicitly.
epqrMaps = method()
epqrMaps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> (
     inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r),(K_infinity).dd_(p+q), Verify => false))
--      inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r),(K_infinity).dd_(p+q)))

-- the following will prune the pq maps on the rth page explicitly. --
--  "sourcePruningMap",
--"targetPruningMap"
--- the above can probably just be replaced by prune d --- except I want to cache the 
-- pruning maps.  --

pruneEpqrMaps = method()
pruneEpqrMaps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> ( 
     d := epqrMaps(K,p,q,r);
     N := minimalPresentation(source d);
     M := minimalPresentation(target d);
     f := inverse(M.cache.pruningMap)* d * (N.cache.pruningMap);
     f.cache #(symbol sourcePruningMap) = N.cache.pruningMap;
     f.cache #(symbol targetPruningMap) = M.cache.pruningMap;
     f 
     )

ErMaps = method(Options =>{Prune => false})


ErMaps(FilteredComplex,ZZ,ZZ,ZZ) := Matrix => opts -> (K,p,q,r) -> (if opts.Prune == false then
     epqrMaps(K,p,q,r)
     else   pruneEpqrMaps(K,p,q,r))

-- the following computes the homology at the pq spot on the rth page.
rpqHomology = method()

rpqHomology(HashTable,ZZ,ZZ,ZZ) := (E,p,q,r) -> (
      (ker(E^r .dd_{p,q})) / (image(E^r .dd_{p+r,q-r+1}) )
      )

-- the following computes the isomorphism of the homology at the pq spot
-- on the r-th page and the module on at the pq spot on the r+1-th page.
rpqIsomorphism = method()
rpqIsomorphism(HashTable,ZZ,ZZ,ZZ) := (E,p,q,r) -> (
    if E.Prune == false then 
inducedMap(source (E^(r+1) .dd_{p,q}),rpqHomology(E,p,q,r), id_(E^(r+1) .filteredComplex _infinity _(p+q)))
    else
    rpqPruneIsomorphism(E,p,q,r)
  ) 

rpqPruneIsomorphism = method()
rpqPruneIsomorphism(HashTable,ZZ,ZZ,ZZ) := (E,p,q,r) -> (    
    M := rpqHomology(E,p,q,r);
    f := inducedMap(target (E^(r + 1) .dd_{p,q}) .cache.sourcePruningMap,
	    M, (E^r .dd_{p,q}).cache.sourcePruningMap);
	inverse((E^(r + 1) .dd_{p,q}) .cache.sourcePruningMap) * f    
  ) 




SpectralSequencePageMap = new Type of HashTable
SpectralSequencePageMap.synonym = "spectral sequence page map"

-- spots might need to be improved.  This will work for now.
-- spots shouldn't be cached either --- because the hash tables are mutable
spots SpectralSequencePageMap := List => (cacheValue symbol spots)(
  K ->  select(keys K, i -> class i === List))


spectralSequencePageMap = method(Options =>{Prune => false})

spectralSequencePageMap(FilteredComplex,ZZ) := SpectralSequencePageMap => opts ->
 (K,r) -> (myList:={};
           for p from min K to max K do (
		for q from -p + min K_(infinity) to max K_(infinity) -p do (
	       	     myList = 
		     append(myList, {p,q} => ErMaps(K,p,q,r, Prune => opts.Prune)) ));
	       new SpectralSequencePageMap from 
	       join (myList, {symbol cache =>  new CacheTable,
		    symbol degree => {-r,r-1}, 
		    symbol filteredComplex => K, 
		    symbol Prune => opts.Prune})
      )


-- the code for net of a SpectralSequencePageMap is based
-- off the code for net of a ChainComplexMap
lineOnTop := (s) -> concatenate(width s : "-") || s
net SpectralSequencePageMap := f -> (
     v := between("",
	  apply(spots f, 
     	       i -> horizontalJoin(
		         net (i + f.degree), " : " , net (target f#i), " <--",
		         lineOnTop net f#i,
		         "-- ", net source f#i, " : ", net i
		    )
	       )
	       );
	  stack v
)


SpectralSequencePageMap _ List := Matrix => (d,i)-> (if (d)#?i then d#i 
     	  else  
	       if d.Prune == false then 
	            epqrMaps(d.filteredComplex,i#0,i#1,- d.degree #0) 
     	       else
	       	    pruneEpqrMaps(d.filteredComplex,i#0,i#1,- d.degree #0) 	       	    		    
		    )

SpectralSequencePageMap ^ List := Matrix => (d,i)-> (d_(-i))    

--------------------------------------------------------------------------------
-- spectral sequence pages
--------------------------------------------------------------------------------
SpectralSequencePage = new Type of MutableHashTable
SpectralSequencePage.synonym = "spectral sequence page"
SpectralSequencePage.GlobalAssignHook = globalAssignFunction
SpectralSequencePage.GlobalReleaseHook = globalReleaseFunction


spectralSequencePage = method (Options =>{Prune => false})

spectralSequencePage(FilteredComplex, ZZ) := SpectralSequencePage => opts ->  (K,r) ->( 
new SpectralSequencePage from 
 {symbol filteredComplex=> K, 
       symbol Prune => opts.Prune,
       symbol number => r,
       symbol dd => spectralSequencePageMap(K,r, Prune => opts.Prune), 
       symbol zero => (ring K_infinity)^0,
       symbol cache => CacheTable}
  )

minimalPresentation SpectralSequencePage := prune SpectralSequencePage := SpectralSequencePage  => opts -> (E) -> (
     spectralSequencePage(E.filteredComplex, E.number, Prune =>true)
     )

SpectralSequencePage _ List := Module => (E,i)-> ( source(E.dd _i) 
		    )

SpectralSequencePage ^ List := Module => (E,i)-> (E_(-i))    

-- view the modules on a Spectral Sequence Page.  We are refering to these
-- as the support of the page.

support SpectralSequencePage := E->(
     new HashTable from apply(spots E.dd, i-> i=> source E.dd #i) )

-- the following two methods are used to view the modules 
-- on the r th page in grid form.  
-- this method is called in net of spectral sequence page.
-- it would be good to delete the zero rows.

net SpectralSequencePage := E->(L := select(keys E.dd, i-> class i === List 
	  and E_i !=0);
maxQ := max(apply(L, i->i#1)); minQ := min(apply(L, i-> i#1)); 
maxP := max(apply(L, i->i#0)); minP := min(apply(L,i->i#0));
K := while maxQ>= minQ list testRow(maxP,minP, maxQ, E) do maxQ = maxQ-1;
netList K)

testRow=method()
testRow(ZZ,ZZ,ZZ,SpectralSequencePage) := (maxP,minP,q,E) -> (L:={};
      apply(minP .. maxP, i-> 
	   if (E.dd) #?{i,q} then L=append(L, stack(net E_{i,q}, "  ", net {i,q}))
	   else L=append(L, stack(net 0, " ", net {i,q})));
       L)



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


spectralSequence = method (Options =>{Prune => false})

spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
     new SpectralSequence from {
	  symbol filteredComplex => K,
	  symbol zero => K.zero,
	  symbol cache => CacheTable,
     	  symbol Prune => opts.Prune}
     )

SpectralSequence ^ InfiniteNumber:=
  SpectralSequence ^ ZZ := SpectralSequencePage => (E,r) -> (
      -- the case that r is an infinite number has been rewritten
      -- and also returns a page --- with no maps!
      -- this fixes an earlier bug.  
      if class r === InfiniteNumber then (
    if r < 0 then error "expected an infinite number bigger than zero"
    else (
	myList := {};
	K := E.filteredComplex;
	s := max K - min K + 1;
	H := new Page;
	    for p from min K to max K do (
	  	for q from -p + min K_(infinity) to max K_(infinity) do (
	       	    if E.Prune == false then H#{p,q} = epq(K,p,q,s)
	       	    else H#{p,q} = prune epq(K,p,q,s)
	       );
    	   ); 
       ); 
H
)
      else (
       if E#?r then E#r else (
       E#r = spectralSequencePage(E.filteredComplex,r, Prune => E.Prune);); 
       E#r
       )
       )

SpectralSequence _ InfiniteNumber :=
SpectralSequence _ ZZ := SpectralSequencePage => (E,r) -> ( E^r )

minimalPresentation SpectralSequence := prune SpectralSequence := SpectralSequence  => opts -> (E) -> (
	  spectralSequence(E.filteredComplex, Prune => true)
	  )


--------------------------------------------------------------------------------
-- constructing filtered complexes ---------------------------------------------
--------------------------------------------------------------------------------


-- Can/Should we add options??  e.g. ker and image to return
-- the truncated complex with ker d_p in degree 0 and zero in degrees > p 
-- or the truncated complex with image d_{p+1} in degree p and zero in degrees < p ??

-- the following method truncates a chain complex 
truncate(ChainComplex,ZZ):= (C,q) ->( 
     if q == 0 then return C 
     else (
	  m:= min support C;
	  n:=max support C;
	  l:=length C;
	  if q < -l or q > l then return image(0*id_C)
	  else  K:=new ChainComplex;
	        K.ring=C.ring;
	  	if q < 0 then for i from min C + 1 to max C do (
	             if i <= n + q then K.dd_i = C.dd_i 
	       	     else if i-1 > n + q then K.dd_i = inducedMap(0*C_(i-1),0*C_i,C.dd_i)
	       	     else K.dd_i = inducedMap(C_(i-1), 0*C_i, C.dd_i) ) 
	  	else for i from min C+1  to max C do (
	       	     if i-1 >= q + m then K.dd_i = C.dd_i 
	       	     else if i < q + m then K.dd_i = inducedMap(0*C_(i-1),0*C_i,C.dd_i)
	       	     else K.dd_i = map(0*C_(i-1), C_i, 0*C.dd_i) )); 		
     K)



-- make the filtered complex associated to the "naive truncation of a chain complex"
filteredComplex ChainComplex := FilteredComplex => opts-> C->( complete C; 
     	       n := max support C;
     	       m := min support C;
	       p := length C;
	       if p > 0 then (
     	       H := for i from 1 to p list inducedMap(C,truncate(C,-i));
     	      filteredComplex(H,Shift => -m) )
	      else filteredComplex {id_C} 
	      -- now the constructor supports the zero chain complex
	      )


--produce the "x-filtration" of the tensor product complex.

FilteredComplex ** ChainComplex := FilteredComplex => (K,C) -> ( 
     xTensormodules := (p,q,T)->(apply( (T#q).cache.indices,
     i-> if (i#0) <=p then  
     image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );

     xTensorComplex := (T,p) ->(K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
		    K.dd_i = inducedMap(
			 directSum(xTensormodules(p,i-1,T)
			      ),
			 directSum(xTensormodules(p,i,T)),T.dd_i));
       	       K
		    );

     	  N := max support K_infinity;
	  P := min support K_infinity;
	  T := K_infinity ** C;
filteredComplex(reverse for i from P to (N-1) list 
     inducedMap(T, xTensorComplex(T,i)), Shift => -P)
	  )

 
--produce the "y-filtration" of the tensor product complex.
ChainComplex ** FilteredComplex := FilteredComplex => (C,K) -> ( 
     yTensorModules := (p,q,T)->(apply( (T#q).cache.indices,
     i-> if (i#1) <=p then  image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );
    yTensorComplex := (T,p) -> (K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
	     	    K.dd_i = inducedMap(directSum(yTensorModules(p,i-1,T)),
			 directSum(yTensorModules(p,i,T)),T.dd_i));
	       K
	       );
    	  N := max support K_infinity;
	  P := min support K_infinity;
	  T := C ** K_infinity;
	   filteredComplex(reverse for i from P to (N -1) list 
	       inducedMap(T, yTensorComplex(T,i)), Shift => -P)
     )

-- produce the "x-filtration" of the Hom complex.
Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
modules := (p,q,T)->(apply( (T#q).cache.indices,
     i-> if (i#0) <= p - q then  
     image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );
     complex := (T,p) -> 
     	       (K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
		    K.dd_i = inducedMap(directSum(modules(p,i-1,T)),directSum(modules(p,i,T)),T.dd_i));
	       K
	       );
     N := max support K_infinity;
     P := min support K_infinity;
     H := Hom(K_infinity,C);
     filteredComplex(reverse for i from P to (N-1) list inducedMap(H, complex(H,i)), Shift => -P)	 
      )

-- produce the "y-filtration" of the Hom complex.
Hom (ChainComplex, FilteredComplex):= FilteredComplex => (C,K) -> (    
modules := (p,q,T)->(apply( (T#q).cache.indices,
     i-> if (i#1) <= p then  image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );
complex := (T,p) ->
     (K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
	     	    K.dd_i = inducedMap(directSum(modules(p,i-1,T)),directSum(modules(p,i,T)),T.dd_i));
	       K
	       );
     N := max support K_infinity;
     P := min support K_infinity;
     H := Hom(C,K_infinity);
     filteredComplex(reverse for i from P to (N -1) list 
	       inducedMap(H, complex(H,i)), Shift => -P)
     )

prune FilteredComplex := FilteredComplex => opts -> F -> 
  new FilteredComplex from 
  apply(keys F, p -> if class p =!= Symbol then p => prune F#p else p => F#p)


filteredComplex SpectralSequence := FilteredComplex => opts -> E -> E.filteredComplex

chainComplex SpectralSequence := ChainComplex => E -> chainComplex filteredComplex E


-- given a morphism f: A --> B
-- compute the connecting map
-- HH_{n+1}( coker f) --> HH_n (im f)

connectingMorphism = method()

connectingMorphism(ChainComplexMap,ZZ) := (a,n) -> (
    K := filteredComplex ({a}) ;
    e := spectralSequence K ;
    e^1 .dd_{1, n}
    )

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

-- the following method seems to work ok, although need to test more
-- carefully.

-- maybe we no longer need this??

--Hom(Matrix, Module) := Matrix => (f,N) -> (
--     g := (f * id_(source f)) // id_(target f);
--     inducedMap(image id_(Hom(source f, N)),image id_(Hom(target f, N)), 
--	       cover((transpose cover g) ** (id_(N))))
--)


-- the following method seems to work ok, athough need to test
-- more carefully.
-- will comment the following out, and see if the M2 1.6 version works OK.
-- Hom(Module, Matrix) := Matrix => (N,f) -> (inducedMap(Hom(N,target f),
--	  Hom(N,source f),   dual id_(cover N) ** f))


-- there is/was a bug in cover chain complex -- 
-- need to test more carefully. --    
-- comment this out too for now.
 
-- cover ChainComplex := ChainComplex => C -> (
--     minC := min spots C;
--     maxC := max spots C;
--     P:= apply(toList(minC..maxC),i-> cover C#i);
--     chainComplex apply(toList(minC..maxC-1), i-> C.dd_(i+1) * map(C_(i+1),P_(i+1),1) // map(C_i,P_i,1)))

isWellDefined ChainComplexMap := Boolean => f -> (
     (F,G):= (source f, target f);
     all(drop(spots F,1), i -> G.dd_i * f#i == f#(i-1) * F.dd_i))

-- Computes the total complex of the Hom double complex of two chain complexes
-- This code is different from that in ChainComplexExtras.  We need this version
-- so that the indicies are cached.
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
  E    	    		    
)

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


  
--FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
--  all(min(min C,min D)..max(max C,max D),i-> C_i == D_i))

-----------------------------------------------------------
-- Experimental Code --------------------------------------
-----------------------------------------------------------
--- Here is some experimental types.  There utility are demonstrated 
-- in some scratch examples below.
-------------------------------------------------------
--  There are some redundancies with existing code;
-- perhaps the existing code should be rewritten in light of our new 
-- types.



---
-- this part should be ignored for now; I'm not doing anything with it at the moment.
-- on the other hand, if implemented properly, we could use this to handle
-- non-bounded chain complexes by using lazy evaluation.
---

InfiniteSequence = new Type of MutableHashTable
InfiniteSequence.synonym = "infinite sequence"
InfiniteSequence.GlobalAssignHook = globalAssignFunction
InfiniteSequence.GlobalReleaseHook = globalReleaseFunction
describe InfiniteSequence := E -> net expression E
net InfiniteSequence := E -> (
  if hasAttribute(E, ReverseDictionary) 
  then toString getAttribute(E, ReverseDictionary) 
  else net expression E)
expression InfiniteSequence := E -> stack(
  "  .-.  ", " (o o) ", " | O \\   Unnamed infinite sequence! ..ooOOOooooOO", 
  "  \\   \\  ", "   `~~~` ")

----------------------------------------------------------------------------


-- should we use infinite sequence or Book??
--InfiniteSequence ^ ZZ := Page => (E,r) -> E#r

InfiniteSequence _ InfiniteNumber :=
InfiniteSequence _ ZZ := Page => (E,r) -> ( if E#?r then E^r else E.infinity )

InfiniteSequence ^ InfiniteNumber :=
InfiniteSequence ^ ZZ := Page => (E,r) -> ("Hi" )


--------------------------------------------------------------------------------
-- PageMap
--------------------------------------------------------------------------------

PageMap = new Type of MutableHashTable
PageMap.synonym = "page map"

-- spots might need to be improved.  This will work for now.

-- spots = method()
PageMap _ List := Matrix => (f,i) ->  if f#?i then f#i else (
      de := f.degree;
      so := (f.source)_i;
      ta := (f.target)_(i+de);
      map(ta,so,0))


spots PageMap := List => (
  K) ->  (select(keys K, i -> class i === List) )

lineOnTop := (s) -> concatenate(width s : "-") || s
net PageMap := f -> (
     v := between("",
	  apply(spots f, 
     	       i -> horizontalJoin(
		         net (i + f.degree), " : " , net (target f#i), " <--",
		         lineOnTop net f#i,
		         "-- ", net source f#i, " : ", net i
		    )
	       )
	       );
	  stack v
)

-- need to write PageMap _ List

-- at present there are no constructors for pageMap
--------------------------------------------------------------------------------
-- Pages
--------------------------------------------------------------------------------
Page = new Type of MutableHashTable
Page.synonym = "Page"
Page.GlobalAssignHook = globalAssignFunction
Page.GlobalReleaseHook = globalReleaseFunction


new Page := Page => (cl) -> (
     C := newClass(Page,new MutableHashTable); -- sigh
     C.cache = new CacheTable;
     b := C.dd = new PageMap;
     b.degree = {};
     b.source = b.target = C;
     C)
ring Page := C -> C.ring
degree Page := C -> C.dd.degree

net Page := E -> (
    L := select(keys E, i -> class i === List and E#i !=0);
    maxQ := max(apply(L, i->i#1)); 
    minQ := min(apply(L, i-> i#1)); 
    maxP := max(apply(L, i->i#0));
    minP := min(apply(L,i->i#0));
    K := while maxQ >= minQ list makeRow(maxP,minP, maxQ, E) do maxQ = maxQ-1;
    netList K)

makeRow = method()
makeRow(ZZ,ZZ,ZZ,Page) := (maxP,minP,q,E)->(L:={};
      apply(minP .. maxP, i-> 
	   if E#?{i,q} then L = append(L, stack(net E#{i,q}, "  ", net {i,q}))
	   else L = append(L, stack(net 0, " ", net {i,q})));
       L)

Page _ List := (E,L) -> ( if E#?L then E#L else (ring E)^0 )

-- at present there are no constructors for Page.

page = method (Options => {Prune => false})

-- given {minP, maxP, Page} make a page.  the idea here is to make the needed keys
-- we then can make entries nonzero as needed.
page(List,List,Page) := Page => opts -> (L,M,E) -> (
    if E.?ring then (
    minP := L#0;
    maxP := L#1;
    minQ := M#0;
    maxQ := M#1;
  --  E := new Page;
  --  E.ring = A;
    for i from minP to maxP do (
	for j from minQ to maxQ do (
	    E#{i,j} = (E.ring)^0;
    )
);
E) else error "page does not have a ring"
)


-- here are some needed functions related to hilbert polynomials --
hilbertPolynomial ZZ := ProjectiveHilbertPolynomial => o -> (M) -> ( 
    new ProjectiveHilbertPolynomial from {0 => M}
    )
ProjectiveHilbertPolynomial == ZZ := (M,N) -> (M == hilbertPolynomial N)
ProjectiveHilbertPolynomial + ZZ := (P, N) -> P + hilbertPolynomial N
ZZ + ProjectiveHilbertPolynomial := (P,N) -> hilbertPolynomial P + N
ProjectiveHilbertPolynomial - ZZ := (P, N) -> P - hilbertPolynomial N
ZZ - ProjectiveHilbertPolynomial := (P,N) -> hilbertPolynomial P - N


hilbertPolynomial(SpectralSequencePage) := Page => o -> (E) -> (
    P := new Page;
    apply(spots E .dd, i -> P#i = hilbertPolynomial(E_i));
    P
    )
-- perhaps I should make a HilbertPolynomialPage as a new type of Page ?? --

prunningMaps = method()
prunningMaps(SpectralSequencePage) := (E) -> ( if E.Prune == false then error "page is not prunned"
    else
    P := new PageMap;
    P.degree = E.dd.degree;
    apply(spots E.dd, i -> P#i = E.dd_i .cache.sourcePruningMap);
    P    
    )

basis (ZZ,SpectralSequencePage) := opts -> (deg,E) -> (
    P := new Page;
    apply(spots E.dd, i -> P#i = basis(deg,E_i));
    P
    )
basis (List,SpectralSequencePage) := opts -> (deg,E) -> (
    P := new Page;
    apply(spots E.dd, i -> P#i = basis(deg,E_i));
    P
    )

-- some experimental code replated to double complexes --

DoubleChainComplex = new Type of Page

DoubleChainComplexMap = new Type of PageMap
DoubleChainComplexMap.synonym = "double chain complex map"


DoubleChainComplex.synonym = "double chain complex"
new DoubleChainComplex := DoubleChainComplex => (cl) -> (
     C := newClass(DoubleChainComplex,new MutableHashTable); -- sigh
     C.cache = new CacheTable;
   --  b := C.dd = new DoubleChainComplexMap from {(symbol xx ) => new PageMap, (symbol yy) => new PageMap};
     b := C.dd = new DoubleChainComplexMap from {symbol xx => new PageMap
	 from { symbol degree => {-1,0}, symbol source => C, symbol target => C}, 
	     symbol yy => new PageMap from {symbol degree => {0,-1}, symbol source => C,
		 symbol target => C}};
     b.degree = {-1,-1};
     b.source = b.target = C;
     C)
ring DoubleChainComplex := C -> C.ring

-----------------------------------------------------------
-----------------------------------------------------------



-----------------------------------------------------------------------
-----------------------------------------------------------------------



beginDocumentation()

undocumented {computeErModules,
     (computeErModules, FilteredComplex,ZZ),(net, Page),
    (net, PageMap),
    (net, SpectralSequence),
    (net, SpectralSequencePage),
    (net, SpectralSequencePageMap),
    (pruneEpqrMaps,FilteredComplex,ZZ,ZZ,ZZ),
    epq, epqrMaps,
    (epqrMaps,FilteredComplex,ZZ,ZZ,ZZ),
    (epq,FilteredComplex,ZZ,ZZ,ZZ),
    (expression,InfiniteSequence),
    (net, FilteredComplex),
    (expression,SpectralSequence),
    spots,
    (spots,PageMap), (spots, SpectralSequencePageMap),
    computeErMaps, xx, yy, Shift, project, next, sourcePruningMap, targetPruningMap, ReducedHomology,
    DoubleChainComplex, DoubleChainComplexMap, InfiniteSequence, Page, SpectralSequencePageMap,pruneEpqrMaps,
    prunningMaps, rpqHomology, rpqIsomorphism, spectralSequencePageMap,
    (spectralSequencePageMap,FilteredComplex,ZZ)
    }

doc ///
     Key 
          SpectralSequences
     Headline 
         a package for working with spectral sequences associated to filtered complexes
    Description
    	 Text 
	      The Spectral Sequences package allows for effective computation of spectral sequences
	      associated to separated and exhaustive filtrations of bounded chain complexes.	    
	      For an overview of how to create and manipulate filtered complexes 
	      see @TO"filtered complexes"@.	  
	      For an overview of how to create and manipulate spectral sequences see
	      @TO"spectral sequences"@.	    
	      For an overview of how to create and manipulate spectral sequence pages see
	      @TO"spectral sequence page"@.
	      associated to a filtered complex.  
	      
	      Below are some examples which illustrate this package.
	      
	      $\bullet$ @TO"Computing the Serre Spectral Sequence associated to a Hopf Fibration"@
	      
	      $\bullet$ @TO "Balancing Tor"@
	      
	      $\bullet$ @TO "Spectral sequences and hypercohomology calculations"@
	      
	      $\bullet$ @TO "Spectral sequences and connecting morphisms"@
	      
	      $\bullet$ @TO "Spectral sequences and non-Koszul syzygies"@
	      
	      $\bullet$ @TO "A spectral sequence which fails to degenerate quickly"@
///	

  doc ///
    Key
      "A spectral sequence which fails to degenerate quickly"
    Headline
     	  nonzero maps on higher page numbers
    Description
    	  Text
	       The following example is taken from p. 127, Fig 7.2 of 
	       Zomorodian's "Topology for computing".  In that figure, a filtration of a suitable
	       simplicial complex is pictured.  Here we compute the associated spectral sequence.
	       As we will see below, the spectral sequences has nonzero maps on higher page numbers.
     	  Example
	        needsPackage "SpectralSequences";
		needsPackage "SimplicialComplexes"; 
		needsPackage "ChainComplexExtras";
		A = ZZ [s,t,u,v,w] ;
		d0 = simplicialComplex {s} ;
		d1 = simplicialComplex {s,t} ;
		d2 = simplicialComplex {s,t,u} ;
		d3 = simplicialComplex {s*t, u} ;
		d4 = simplicialComplex {s*t, u, v} ;
		d5 = simplicialComplex {s*t, u, v, w} ;
		d6 = simplicialComplex {s*t, s*w ,u, v} ;
		d7 = simplicialComplex {s*t, s*w ,t * w, u, v} ;
		d8 = simplicialComplex {s*t, s*w ,t * w, u * v} ;
		d9 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v} ;
		d10 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u} ;
		d11 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w} ;
		d12 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u} ;
		d13 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w} ;
		d14 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w} ;
		d15 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u} ;
		d16 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v} ;
		d17 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v, s*t*w} ;
		L = reverse {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17} ;
		K = filteredComplex (L, ReducedHomology => false) ;
		E = prune spectralSequence K ;
		E^0
		E^0 .dd
		E^1
		E^1 .dd
		E^2
		E^2 .dd
		E^3
		E^3 .dd
		E^4
		E^4 .dd
		E^5
		E^5 .dd
		E^6
		E^6 .dd
		E^7
		E^7 .dd
		E^8
		E^8 .dd
		E^9
		E^9 .dd
		E^infinity
		prune HH K_infinity
///
  doc ///
    Key
      "Spectral sequences and non-Koszul syzygies"
    Headline
     	  using spectral sequences to compute non-Koszul syzygies
    Description
    	  Text
	       We illustrate some aspects of the paper 
	       "A case study in bigraded commutative algebra" by Cox-Dickenstein-Schenck.
	       In that paper, an appropriate term on the E_2 page of a suitable 
	       spectral sequence corresponds to non-koszul syzygies.
	       Using our indexing conventions, the E^2_{3,-1} term will be what the
	       $E^{0,1}_2$ term is in their paper.
	       We illustrate an instance of the non-generic case for non-Koszul syzygies.
	       This is acheived by looking at the three polynomials used in their Example 4.3.
    	       The behaviour that we expect to exhibit is predicted by their Proposition 5.2.
	  Example
		needsPackage "SpectralSequences"
		R = QQ[x,y,z,w, Degrees => {{1,0},{1,0},{0,1},{0,1}}]
		B = ideal(x*z, x*w, y*z, y*w)
		p_0 = x^2*z
		p_1 = y^2*w
		p_2 = y^2*z+x^2*w
		I = ideal(p_0,p_1,p_2)
		-- make the frobenious power of the irrelevant ideal
		B = B_*/(x -> x^2)//ideal
		-- need to take a large enough power. 
		-- it turns out that that 2 is large enough for this example 
		G = res image gens B
		F = koszul gens I
		K = Hom(G, filteredComplex(F))
		E = prune spectralSequence K
		E^1
		E^2
		E^2_{3,-1}
		basis({0,0}, E^2_{3, -1} ** R^{{2, 3}})
		E^2 .dd_{3, -1}
		E^2 .dd
		basis({0,0}, image E^2 .dd_{3,-1} ** R^{{2,3}})
		basis({0,0}, E^2_{1,0} ** R^{{2,3}})
		-- this shows that there is a 1 dimensional space of non-Koszul syzygies of bi-degree (2,3)
		-- which is also what is predicted by the paper.
		basis({0,0}, E^2 _{3, -1} ** R^{{6,1}})
		-- this shows that there is a 1 dimensional space of non-Koszul syzygies of bi-degree (6,1)
		-- this is what is predicted by the paper.
		isIsomorphism(E^2 .dd_{3, -1})	       
	       	  
///	  
     doc ///
     Key
       "Spectral sequences and connecting morphisms"
     Headline
          using spectral sequences to compute connecting morphisms
     Description
     	  Text
	       If $0 \rightarrow A \rightarrow B \rightarrow C \rightarrow 0$ is a 
	       short exact sequence of chain complexes, then the connecting morphism
	       $H_i(C) \rightarrow H_{i - 1}(A)$ can relized as a suitable map
	       on the $E^1$ of a spectral sequences determined by a suitably defined
	       two step filtration of $B$.
	       
	       In this example, we illustrate how these constructions can be used to 
	       compute the connecting morphism $H^i(X, F) \rightarrow H^{i + 1}(X, G)$
	       arising from a short exact sequence 
	       $0 \rightarrow G \rightarrow H \rightarrow F \rightarrow 0$ of sheaves
	       on a smooth toric variety $X$.
	       
	       In more detail, we use multigraded commutative algebra and 
	       spectral sequences
	      to compute the connecting
	       morphism 
	      $H^1(C, OO_C(1,0)) \rightarrow H^2(X, OO_X(-2,-3))$ where 
	      $X := \mathbb{P}^1 \times \mathbb{P}^1$ and $C$ is a general divisor
	      of type $(3,3)$ on $X$.  This connecting morphism is an
	      isomorphism.
	  Example   
	        needsPackage "SpectralSequences";
                needsPackage "ChainComplexExtras";
                R = ZZ/101[a_0..b_1, Degrees=>{2:{1,0},2:{0,1}}]; -- PP^1 x PP^1
		B = intersect(ideal(a_0,a_1),ideal(b_0,b_1)) ; -- irrelevant ideal
		B = B_*/(x -> x^5)//ideal ; -- Suitably high Frobenius power of B
		G = res image gens B
		I = ideal random(R^1, R^{{-3,-3}}) -- ideal of C
	        b = chainComplex gradedModule R^{{1,0}} -- make line bundle a chain complex
		a = chainComplex gradedModule R^{{-2,-3}}
		-- make the map OO(-2, -3) --> OO(1,0)     
		f = chainComplexMap(b, a,{random(R^1, R^{{-3,-3}})}) ; 
		k = filteredComplex ({Hom(G,f)}) ; -- the two step filtered complex we want
		e = prune spectralSequence k ;
		e^1 .dd_{1,-2} -- the connecting map HH^1(C, OO_C(1,0)) --> HH^2(X, OO_X(-2,-3)) 
		basis({0,0}, image e^1 .dd_{1,-2})  -- image 2-dimensional
		basis({0,0}, ker e^1 .dd_{1,-2}) -- map is injective
		basis({0,0}, target e^1 .dd_{1,-2}) -- target 2-dimensional 
		basis({0,0}, source e^1 .dd_{1,-2}) -- source 2 dimensional 
	  Text
	       An alternative way to compute the connecting morphism is 
	  Example
	      	prune connectingMorphism(Hom(G, f), - 2) ;
		prune connectingMorphism(Hom(G, f), - 2) == e^1 .dd_{1, -2}    
///     
     doc ///
     Key
       "Spectral sequences and hypercohomology calculations"
     Headline
     	  illustrating how to use spectral sequences to compute hypercohomology
     Description
     	  Text
	       If $\mathcal{F}$ is a coherent sheaf on a smooth toric variety $X$,
	       then multigraded commutative algebra can be used to compute
	       the cohomology groups $H^i(X, \mathcal{F})$.  
	       
	       More specifically, if $B$ is the irrelevant ideal of $X$ then
	       $H^i(X, \mathcal{F})$ is relized as the degree zero piece of the multigraded
	       module
	       $Ext^i(B^{[l]}, F)$ for sufficiently large $l$; here $B^{[l]}$ denotes
	       the $l$th Forbenius power of $B$ and $F$ is any multigraded module whose
	       corresponding sheaf on $X$ is $\mathcal{F}$.  
	       
	       Given the fan of
	       $X$ and $F$, a sufficiently large power of $l$ can be determined effectively.
	       We refer to sections 2 and 3 of the paper 
	       "Cohomology on Toric Varieties and Local Cohomology with Monomial Supports"
	       for more details.
	       
	       In this example, we consider
	       the case that $X = \mathbb{P}^1 \times \mathbb{P}^1$ and 
	       $F = \mathcal{O}_C(1,0)$ where 
	       $C$ is a general divisor of type $(3,3)$ on $X$. 
	       In this setting, $H^0(C,F)$ and $H^1(C, F)$ are both $2$-dimensional 
	       vector spaces.
    	  Example
	         needsPackage "SpectralSequences";
		 needsPackage "ChainComplexExtras";
	         -- C \subseteq PP^1 x PP^1 type (3,3)
		 -- Use hypercohomology to compute HH OO_C(1,0) 
		 R = ZZ/101[a_0..b_1, Degrees=>{2:{1,0},2:{0,1}}]; -- PP^1 x PP^1
		 B = intersect(ideal(a_0,a_1),ideal(b_0,b_1)) ; -- irrelevant ideal
		 B = B_*/(x -> x^5)//ideal ; -- Sufficentily high Frobenius power 
		 G = res image gens B
		 I = ideal random(R^1, R^{{-3,-3}}) -- ideal of C
		 F = res comodule I 
		 -- Twist F by a line of ruling and make filtered complex whose ss abuts to HH OO_C(1,0) 
		 K = Hom(G , filteredComplex (F ** R^{{1,0}})) ;
		 E = prune spectralSequence K ; --the spectral sequence degenerates on the second page 
		 E^1 
		 E^2 ; -- output is a mess
		 basis({0,0}, E^2_{0,0}) --  == HH^0 OO_C(1,0)
		 basis({0,0}, E^2_{1,-2}) --  == HH^1 OO_C(1,0)	 
///	  


doc ///
          Key
       	    "Computing the Serre Spectral Sequence associated to a Hopf Fibration"
         
	  Description
	       Text
	       	    The purpose of this example is to compute 
		    the Serre Spectral Sequence
		    associated to the Hopf Fibration 
		    $S^1 \rightarrow S^3 \rightarrow S^2$.
		    This example is made possible by the minimal
		    triangualtion of this fibration given in the paper
		    "A minimal triangulation of the Hopf map and its application"
		    by K.V. Madahar and K.S Sarkaria. Geom Dedicata, 2000.
	       Example
	       	    needsPackage "SpectralSequences"
		    needsPackage "SimplicialComplexes"
     	       Text
	       	    We first need to make the relavant simplicial complexes
		    as described on page 110 of the paper.  The
		    simplical complex $D$ below is supposed to be a triangualtion of 
		    $S^3$.  
	       Example		    
		    B=QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2]
		    l1={a_0*b_0*b_1*c_1,a_0*b_0*c_0*c_1,a_0*a_1*b_1*c_1,b_0*b_1*c_1*d_1,b_0*c_0*c_1*d_2,a_0*a_1*c_1*d_2,a_0*c_0*c_1*d_2,b_0*c_1*d_1*d_2};
		    l2={b_1*c_1*c_2*a_2,b_1*c_1*a_1*a_2,b_1*b_2*c_2*a_2,c_1*c_2*a_2*d_1,c_1*a_1*a_2*d_2,b_1*b_2*a_2*d_2,b_1*a_1*a_2*d_2,c_1*a_2*d_1*d_2};
		    l3={c_2*a_2*a_0*b_0,c_2*a_2*b_2*b_0,c_2*c_0*a_0*b_0,a_2*a_0*b_0*d_1,a_2*b_2*b_0*d_2,c_2*c_0*b_0*d_2,c_2*b_2*b_0*d_2,a_2*b_0*d_1*d_2};
		    l4={a_0*b_0*b_1*d_1,a_0*b_1*d_0*d_1,b_1*c_1*c_2*d_1,b_1*c_2*d_0*d_1,a_0*a_2*c_2*d_1,a_0*c_2*d_0*d_1};
		    l5={a_0*b_1*d_0*d_2,a_0*a_1*b_1*d_2,b_1*c_2*d_0*d_2,b_1*b_2*c_2*d_2,a_0*c_2*d_0*d_2,a_0*c_0*c_2*d_2};
		    D=simplicialComplex(join(l1,l2,l3,l4,l5));
	       Text 
	            We now construct filtrations of $D$ corresponding to $p$-
		    sketeltons of the fibration.
		    Again we describe these in pieces.
		    For example, if $p:S^3 \rightarrow S^2$  denotes the map defined
		    by $a_i\mapsto a$, $b_i\mapsto b$, and $c_i \mapsto c$, 
		    then to compute
		    $f1l1$ below, we observe that 
		    the inverse image of $ab$ under $p$ is
		    $a_0b_0b_1, a_0a_1b_1$ etc.
		    I have computed these all by hand previously. 
	       Example
	            f1l1 = {a_0*b_0*b_1,a_0*a_1*b_1,a_0*c_0*c_1,a_0*a_1*c_1,a_0*a_1*d_2,d_1*d_2,b_0*b_1*c_1,b_0*c_0*c_1,b_0*b_1*d_1,b_0*d_1*d_2,c_1*d_1*d_2,c_0*c_1*d_2};
		    f1l2 = {b_1*a_1*a_2,b_1*b_2*a_2,c_1*c_2*a_2,c_1*a_1*a_2,a_1*a_2*d_2,a_2*d_1*d_2,b_1*c_1*c_2,b_1*b_2*c_2,b_1*b_2*d_2,d_1*d_2,c_1*d_1*d_2,c_1*c_2*d_1};
		    f1l3 = {a_2*a_0*b_0,a_2*b_2*b_0, c_2*a_2*a_0,c_2*c_0*a_0,a_2*a_0*d_1,a_2*d_1*d_2,b_2*b_0*c_2,c_2*c_0*b_0,b_2*b_0*d_2,b_0*d_1*d_2,c_2*c_0*d_2,d_1*d_2};
		    f1l4 = {a_0*b_0*b_1,a_0*a_2,a_0*a_2*c_2,c_1*c_2,a_0*d_0*d_1,a_0*a_2*d_1,b_1*c_1*c_2,b_0*b_1,b_0*b_1*d_1,b_1*d_0*d_1,c_1*c_2*d_1,c_2*d_0*d_1}
		    f1l5 = {a_0*a_1*b_1,b_1*b_2,a_0*c_0*c_2,a_0*a_1,a_0*d_0*d_2,a_0*a_1*d_2,b_1*b_2*c_2,c_0*c_2,b_1*d_0*d_2,b_1*b_2*d_2,c_2*d_0*d_2,c_0*c_2*d_2};
		    F1D = simplicialComplex(join(f1l1,f1l2,f1l3,f1l4,f1l5));
	       Text
	            So $F1D$ corresponds to filtration of $D$ by considering the 
		    inverse images of the
		    $1$-dimensional faces of the triangulation of $S^2$. 
		    $D$ corresponds to the filtration of $D$ by considering 
		    inverse images
		    of the two dimensional faces of the triangulation of $S^2$.
	       Example
		    f0l1={a_0*a_1,b_0*b_1,c_0*c_1,d_1*d_2};
		    f0l2={a_1*a_2,b_1*b_2,c_1*c_2,d_1*d_2};
		    f0l3={a_0*a_2,b_0*b_2,c_0*c_2,d_1*d_2};
		    f0l4={a_0*a_2,b_0*b_1,c_1*c_2,d_0*d_1};
		    f0l5={a_0*a_1,b_1*b_2,c_0*c_2,d_0*d_2};
		    F0D=simplicialComplex(join(f0l1,f0l2,f0l3,f0l4,f0l5)); 
	       Text
	            So $F0D$ corresponds to the filtration of $D$ by considering 
		    the inverse images of the 
		    $0$-dimensional faces of the triangulation of $S^2$.
		    To compute the Serre spectral sequence of the Hopf fibration 
		    $S^1 \rightarrow S^3 \rightarrow S^2$ 
		    correctly meaning that we get the $E_2$ page as 
		    asserted in the usual theorem we need to
		    use non-reduced homology.		     
     	       Example		     
     	       	    K=filteredComplex({D,F1D,F0D},ReducedHomology => false)
     	       Text		    
		    Now try to compute the various pages of the spectral sequence.
		    I have not made any serious attempt to compute the $E^0$ 
		    and $E^1$ pages by hand. 
     	       Example		     
     	       	    E = spectralSequence K
     	       Text 
	       	    When we compute the $E^0$ page the output will be unintelliagable. 
		    We will want to prune the page afterwards.
     	       Example		    		    
		    E0page = E^0
		    --new HashTable from apply(keys E0page.dd, i-> i=> E0page.dd #i)
     	       Text
	       	    Here are the maps.
     	       Example		    		    
     	       	    E0page.dd
     	       Text 
	       	    Compare with the pruned version.
     	       Example		    		    
		    minimalE0page = minimalPresentation(E0page)  
		    minimalE0page.dd
		 --   apply(spots E0page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
     	       Text
	       	    Now try the $E^1$ page.  
     	       Example		       	       	    
		    E1page = E^1
		    --new HashTable from apply(keys E1page.dd, i-> i=>  E1page.dd #i)
     	       Text 
	       	    Here are the maps.
     	       Example		    		    
		    E1page.dd 
     	       Text
	       	    Compare with the pruned version.
     	       Example		    		    
		    minimalE1page = minimalPresentation(E1page)  
		    minimalE1page.dd
		  --  apply(spots E1page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
     	       Text
	       	    Now try the $E^2$ page.
     	       Example		    		    
		    E2page = E^2
		    --new HashTable from apply(keys E2page.dd, i-> i=> E2page.dd #i)
     	       Text
	       	    Here are the maps.
     	       Example		    		    
		    E2page.dd
     	       Text
	       	    Here is the pruned version.
     	       Example		    		    
		    minimalE2page = minimalPresentation(E2page)  
		    minimalE2page.dd
		    apply(spots E1page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
     	       Text		    
		    Note that the modules on the E_2 page appear to have been computed correctly.  
		    The statement of the Serre spectral sequence, see for example Theorem 1.3 p. 8 of 
		    Hatcher's Spectral Sequence book, asserts that 
	            $E^2_{p,q}= H_p(S^2,H_q(S^1,QQ))$.
		    This is exactly what we are suppose to get.
		    the maps on the $E_2$ page also seem to be computed correctly as the spectral sequence
		    will abut to the homology of $S^3$.
     	       Example		    
		    E3page = E^3
		    E3page.dd
		    minimalE3page = minimalPresentation(E3page)  
		    minimalE3page.dd
		    --new HashTable from apply(keys E3page.dd, i-> i=> E3page.dd #i)
		 --   apply(spots E1page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,3))
     	       Text		    
		   The E_3 page appears to have been computed correctly.		
///	       
 
 doc ///
      Key
      	   "Balancing Tor"
     Description
     	  Text
	       To balance Tor we first need to make some modules over a ring.
     	  Example
	       A = QQ[x,y,z,w];
	       M = monomialCurveIdeal(A,{1,2,3});
	       N = monomialCurveIdeal(A,{1,3,4});
     	  Text
	       To compute $Tor^A_i(M,N)$ we resolve the modules, tensor appropriately, 
	       and then take homology. 
     	  Example	       	       	       
	       K = res M
	       J = res N
     	  Text
	       The spectral sequence that computes $Tor^A_i(M,N)$ by tensoring
	       $K$ with $N$ and taking homology is given by
     	  Example
	       E = spectralSequence( (filteredComplex K) ** J)
     	  Text
	       The spectral sequence that computes $Tor^A_i(M,N)$ by tensoring
	       $J$ with $M$ and taking homology is given by 	        
     	  Example
	       F = spectralSequence( (K ** (filteredComplex J)))	       
	  Text
	       Let's compute some pages and maps of these spectral sequences.
	  Example
	       E^0
	       e0 = minimalPresentation(E^0)
	       E^0 .dd 
	       e0.dd
	       E^1
	       e1 = minimalPresentation(E^1)
	       E^1 .dd
	       e1.dd
	       E^2
	       e2 = minimalPresentation(E^2)
	       E^2 .dd
	       e2.dd
	       F^0
	       f0 = minimalPresentation(F^0)
	       F^0 .dd
	       f0.dd
	       F^1
	       f1 = minimalPresentation(F^1)
	       F^1 .dd
	       f1.dd
	       F^2  
	       f2 = minimalPresentation(F^2)  
	       F^2 .dd      	       
	       f2.dd
	        	       
	    
///	       	 





--
-- Types
--

    doc ///
     Key
     	  FilteredComplex
     Headline
     	  the type of all FilteredComplexes
     Description
     	  Text	 
	     The type FilteredComplex is a data type for storing information associated to separated and exhaustive filtrations of bounded chain complexes.
	     For an overview of how to create and manipulate filtered complexes 
	     see @TO"filtered complexes"@.	  
	     For an overview of how to create and manipulate spectral sequences see
	     @TO"spectral sequences"@.	    
	     For an overview of how to create and manipulate spectral sequence pages see
	     @TO"spectral sequence page"@.
	     
	  --     The type FilteredComplex is a data type for storing information associated
	  --     to separated and exhaustive filtrations of a chain complex.
     	     -- A filtered complex is a nested family of chain complexes 
	     -- $K : \dots \supseteq K_n \supseteq K_{n-1} \supseteq  
	     -- \dots$ such that the following holds:	      
	     -- 1.  There exists an integer $m$ such that $K_n = K_m$ for all $n \geq m$.	    
	     -- 2.  There exists an integer $l$ such that $K_n = 0$ for all $n \leq l$.
///

doc ///
     Key
          "filtered complexes"
     Headline
     	  how to create and manipulate filtered complexes
     Description
     	  Text	            	     
	    @TO"filtered complexes and spectral sequences from simplicial complexes"@
	  Text    
	    @TO"filtered complexes from chain complexes"@
	  Text    
	    @TO"filtered complexes and spectral sequences from chain complex maps"@
	  Text    
	      @TO"filtered complexes from tensor products of chain complexes"@
	  Text   
	      @TO"filtered complexes from Hom"@	     	  
///	  	 
doc ///
     Key
          "filtered complexes and spectral sequences from simplicial complexes"
     Headline
     	  making filtered complexes and spectral sequences from simplicial complexes
     Description
     	  Text	 	    
	    To make a filtered complex from a list of simplicial 
     	    complexes we first need to make some simplical complexes.
     	  Example
	      needsPackage "SpectralSequences"	     
	      needsPackage "SimplicialComplexes";
	      R = QQ[x,y,z,w]; 	     
	      a = simplicialComplex {x*y*z, x*y, y*z, w*z}
	      b = simplicialComplex {x*y, w}
	      c = simplicialComplex {x,w}
	  Text 
	     Note that $b$ is a simplicial subcomplex of $a$ and that
	     $c$ is a simplical subcomplex of $b$.
	     Let's now create a filtered complex.
	  Example
	      K = filteredComplex{a,b,c}	
	  Text
	      Having made a filtered complex, we can make a  
	      spectral sequence.
     	  Example
	       E = spectralSequence K
     	  Text
	       Let's view some pages and maps of these pages. 
     	  Example
	       E^0
	       F0 = minimalPresentation(E^0) 
	       E^0 .dd
	       F0.dd 	      
	       E^1
	       F1 = minimalPresentation(E^1)
	       E^1 .dd
	       F1.dd
	       E^2
	       F2 = minimalPresentation(E^2) 
	       E^2 .dd
	       F2.dd
	       E^infinity
    	       (prune E) ^infinity
	  Text
     	     If we want the resulting complexes to correspond to the non-reduced homology
     	     of the simpicial complexes we set the ReducedHomology option
	     to false.
     	  Example 
	     J = filteredComplex({a,b,c}, ReducedHomology => false)           	     
	  Text
	       The resulting spectral sequence looks like
     	  Example
	       D = spectralSequence J
	       D^0
	       G0 = minimalPresentation(D^0)
	       G0.dd
	       D^1
	       G1 = minimalPresentation(D^1)
	       G1.dd
	       D^2
	       G2 = minimalPresentation(D^2)
	       G2.dd
	       D^infinity 	             	          
  ///	  	 
doc ///
     Key
     	  "filtered complexes from chain complexes"
     Headline
     	  making filtered complexes and spectral sequences from chain complexes.
     Description
     	  Text
///	  	  
doc ///
     Key
        "filtered complexes and spectral sequences from chain complex maps"
     Headline
     	  making filtered complexes and spectral sequences from chain complex maps	
     Description
     	  Text  
       	    We can make a filtered complex from a list of chain complex maps as follows.
	    We first need to load the relavent packages.
          Example
	       needsPackage "SpectralSequences"	    
	       needsPackage "ChainComplexExtras"
     	  Text
	       We then make a chain complex.
     	  Example	       	 
	       R=QQ[x,y,z,w]
	       d2=matrix(R,{{1},{0}})
	       d1=matrix(R,{{0,1}})
	       C=chainComplex({d1,d2}) 
	  Text
	      We now make the modules of the another chain complex which we will label D.
	  Example      
	       D_2 = image matrix(R,{{1}})
	       D_1 = image matrix(R,{{1,0},{0,0}})
	       D_0 = image matrix(R,{{1}})
	       D = chainComplex({inducedMap(D_0,D_1,C.dd_1),inducedMap(D_1,D_2,C.dd_2)})
     	  Text
	       Now make a chain complex map.
     	  Example	       	     
	       d = chainComplexMap(C,D,apply(spots C, i-> inducedMap(C_i,D_i,id_C _i)))
	       isChainComplexMap d
	       d == chainComplexMap(C,D,{inducedMap(C_0,D_0,id_(C_0)),inducedMap(C_1,D_1,id_(C_1)),inducedMap(C_2,D_2,id_(C_2))})
     	  Text
	       We now make the modules of another chain complex which we will label E.	     
     	  Example	      
               E_2=image matrix(R,{{0}})
	       E_1= image matrix(R,{{1,0},{0,0}})
	       E_0 = image matrix(R,{{1}})
	       E = chainComplex({inducedMap(E_0,E_1,C.dd_1),inducedMap(E_1,E_2,C.dd_2)})
     	  Text
	       Now make a chain complex map.
     	  Example	      	       
	       e=chainComplexMap(C,E,apply(spots C, i->inducedMap(C_i,D_i, id_C _i)))
     	  Text 
	       Now make a filtered complex from a list of chain complex maps.
     	  Example	       	       
	       K=filteredComplex({d,e})
	  Text
	     We can make a filtered complex, with a specified minimum filtration degree
             from a list of ChainComplexMaps by using the Shift option.
      	  Example	       	     
	       L=filteredComplex({d,e},Shift =>1)
	       M=filteredComplex({d,e},Shift =>-1)	      	    
	  
///	  
doc ///
     Key
        "filtered complexes from tensor products of chain complexes"
     Headline
     	 making filtered complexes and spectral sequences from tensor products 	
     Description
     	  Text
///	  

doc ///
     Key
        "filtered complexes from Hom"
     Headline
     	 making filtered complexes and spectral sequences from Hom
     Description
     	  Text
///	  

doc ///
     Key
     	  SpectralSequence
     Headline
     	  the type of all spectral sequences
     Description
     	  Text
	       The SpectralSequences package provides effective computation of spectral sequences
	       associated to separated and exhaustive filtrations of a chain complex.	    
	       For an overview of how to create and manipulate filtered complexes 
	       see @TO"filtered complexes"@.	  
	       For an overview of how to create and manipulate spectral sequences see
	       @TO"spectral sequences"@.	    
	       For an overview of how to create and manipulate spectral sequence pages see
	       @TO"spectral sequence page"@.
	    
	    --   A spectral sequence consists of the following:	      
	    --   1. A sequence of modules \{E^r_{p,q}\}_{p,q \in \ZZ, r \geq 0},
       	    --   2. A collection of homomorphisms \{d^r_{p,q}: E^r_{p,q} $\rightarrow$ E^r_{p-r,q+r-1}}_{p,q \in ZZ, r \geq 0} such that
	    --   d^r_{p,q} d^r_{p+r,q-r+1} =0, 	       
	    --   3. A collection of isomorphisms E^{r+1}_{p,q}  $\rightarrow$ ker d^r_{p,q} / image d^r_{p+r,q-r+1}.	       
	    --   In this package, a spectral sequence is represented by a sequence of spectral sequence pages.	       
///

doc ///
     Key
     	  "spectral sequences"
     Headline
     	  how to create and manipluate spectral sequences
///	  	  
	       
doc ///
     Key
     	  SpectralSequencePage
     Headline
     	  the type of all spectral sequence pages
     Description
     	  Text
	       The SpectralSequences package provides effective computation of spectral sequences
	       associated to separated and exhaustive filtrations of a chain complex.	    
	       For an overview of how to create and manipulate filtered complexes 
	       see @TO"filtered complexes"@.	  
	       For an overview of how to create and manipulate spectral sequences see
	       @TO"spectral sequences"@.	    
	       For an overview of how to create and manipulate spectral sequence pages see
	       @TO"spectral sequence page"@.
	    
	       
	    --   A spectral sequence page (or sheet) with page number r (for a 
	--	    fixed integer r $\geq$ 0) is 
	  --     collection $E^r:=\{E^r_{p,q}, d^r_{p,q}\}_{p,q\in \ZZ}$ such that:	       
	    --   1. $E^r_{p,q}$ are
	     --  modules,	       
	      -- 2. $d^r_{p,q}:E^r_{p,q}\rightarrow E^r_{p-r,q+r-1}$ are homomorphisms,	       
	     --  3. and $d^r_{p,q} d^r_{p+r,q-r+1}=0$.
	       
///	       

doc ///
     Key
     	  "spectral sequence page"
     Headline
     	  how to create and manipluate spectral sequence pages
///	  	  

--- functions and methods ---

-- truncate a filtered complex documentation --
doc ///
     Key
     	  (truncate, ChainComplex,ZZ)
     Headline
     	  truncate a filitered complex.
     Usage
     	  K = truncate(C,p)
     Inputs
     	  C:ChainComplex
	  p:ZZ
     Outputs
     	  K:ChainComplex  
     Description
     	  Text 
	    
	 Example
	  A=QQ[x,y]  
	  I=ideal vars A 
	  C=res I
	  truncate(C,0)
	  truncate(C,-1)
	  truncate(C,-2)
	  truncate(C,-3)
	  truncate(C,1)
	  truncate(C,2)
	  truncate(C,3)
	  truncate(C,10)
	  truncate(C,-10)
	  	  
  ///
  
--doc ///
--     Key
--     	  (spectralSequencePageMap, FilteredChainComplex, ZZ)
--     Headline
--     	  The maps on a spectral sequence page
--     Usage
--     	  d = spectralSequencePageMap(K,r)
--     Inputs
--     	  K:FilteredChainComplex
--	  r:ZZ
--     Outputs
--     	  d:SpectralSequencePageMap
--     Description
--     	  Text 
--	      Returns the maps on the rth page of the spectral sequence determined by K.	  
--  ///


 
  doc ///
          Key
       	    filteredComplex
          Headline
	       make a filtered complex
     	  Usage
	       K=filteredComplex L
	  Inputs
	       L:List       	  
		    	 or 
	       L:ChainComplex 
	       	    	 or
     	       L:SpectralSequence			 
	       ReducedHomology =>Boolean	       	  	    
	       Shift => ZZ
	  Outputs 
	       K: FilteredComplex
	  Description
	       Text
	       	    This is the primative filteredComplex constructor.
	       
///	       

  doc ///
     Key 
      (filteredComplex,List)
     Headline 
      obtain a filtered complex from a list of chain complex maps or a nested list of simplicial complexes
     Usage 
       K = filteredComplex L 
     Inputs 
	  L: List
	  ReducedHomology =>Boolean
	  Shift => ZZ
     Outputs 
       K: FilteredComplex
     Description
      	  Text  
       	    We can make a filtered complex from a list of chain complex maps as follows.
	    We first need to load the relavent packages.
          Example
	       needsPackage "SpectralSequences"	    
	       needsPackage "ChainComplexExtras"
     	  Text
	       We then make a chain complex.
     	  Example	       	 
	       R = QQ[x,y,z,w]
	       d2 = matrix(R,{{1},{0}})
	       d1 = matrix(R,{{0,1}})
	       C = chainComplex({d1,d2}) 
	  Text
	      We now make the modules of the another chain complex which we will label D.
	  Example      
	       D_2 = image matrix(R,{{1}})
	       D_1 = image matrix(R,{{1,0},{0,0}})
	       D_0 = image matrix(R,{{1}})
	       D = chainComplex({inducedMap(D_0,D_1,C.dd_1),inducedMap(D_1,D_2,C.dd_2)})
     	  Text
	       Now make a chain complex map.
     	  Example	       	     
	       d = chainComplexMap(C,D,apply(spots C, i-> inducedMap(C_i,D_i,id_C _i)))
	       isChainComplexMap d
	       d == chainComplexMap(C,D,{inducedMap(C_0,D_0,id_(C_0)),inducedMap(C_1,D_1,id_(C_1)),inducedMap(C_2,D_2,id_(C_2))})
     	  Text
	       We now make the modules of another chain complex which we will label E.	     
     	  Example	      
               E_2 = image matrix(R,{{0}})
	       E_1 = image matrix(R,{{1,0},{0,0}})
	       E_0 = image matrix(R,{{1}})
	       E = chainComplex({inducedMap(E_0,E_1,C.dd_1),inducedMap(E_1,E_2,C.dd_2)})
     	  Text
	       Now make a chain complex map.
     	  Example	      	       
	       e = chainComplexMap(C,E,apply(spots C, i->inducedMap(C_i,D_i, id_C _i)))
     	  Text 
	       Now make a filtered complex from a list of chain complex maps.
     	  Example	       	       
	       K = filteredComplex({d,e})
	  Text
	     We can make a filtered complex, with a specified minimum filtration degree
             from a list of ChainComplexMaps by using the Shift option.
      	  Example	       	     
	       L = filteredComplex({d,e},Shift =>1)
	       M = filteredComplex({d,e},Shift =>-1)	      	    
	  Text
	    We can make a filtered complex from a nested list of simplicial 
     	    complexes as follows
     	  Example
	      needsPackage "SimplicialComplexes"; 	     
	      D = simplicialComplex {x*y*z, x*y, y*z, w*z}
	      E = simplicialComplex {x*y, w}
	      F = simplicialComplex {x,w}
	      K = filteredComplex{D,E,F}
	  Text
     	     If we want the resulting complexes to correspond to the non-reduced homology
     	     of the simpicial complexes we can do the following.
     	  Example 
	     filteredComplex({D,E,F}, ReducedHomology => false)
     SeeAlso
     	  "maps between chain complexes"
///

doc ///
     Key 
          (filteredComplex,ChainComplex)
     Headline 
         obtain a filtered complex from a chain complex
     Usage 
         K = filteredComplex C 
     Inputs 
	  C: ChainComplex
-- these options don't do anything for this constructor.
	  ReducedHomology =>Boolean	       	  	    
	  Shift => ZZ
     Outputs
          K: FilteredComplex
     Description	  
     	  Text
	     Produces the filtered complex obtained by succesively truncating the complex.
	  Example 
	    needsPackage "SpectralSequences"
	    A = QQ[x,y]
	    C = koszul vars A
	    K = filteredComplex C
     SeeAlso 
	  (truncate, ChainComplex,ZZ)
	  
    /// 

doc ///
     Key 
          (filteredComplex,SpectralSequence)
     Headline 
         obtain the filtered complex associated to the spectral sequence
     Usage 
         K = filteredComplex E 
     Inputs 
	  E: SpectralSequence
-- these options don't do anything for this constructor.
	  ReducedHomology => Boolean	       	  	    
	  Shift => ZZ
     Outputs
          K: FilteredComplex
     Description	  
     	  Text
	     Produces the filtered complex which determined the spectral sequence.
	  Example 
	    needsPackage "SpectralSequences";
	    A = QQ[a,b,c,d];
	    D = simplicialComplex {a*d*c, a*b, a*c, b*c};
	    F2D = D
	    F1D = simplicialComplex {a*c, d}
	    F0D = simplicialComplex {a,d}
	    K = filteredComplex {F2D, F1D, F0D}
	    E = spectralSequence(K) ;
    	    C = filteredComplex E ;
    /// 


doc ///
     Key
  	  (chainComplex, FilteredComplex)
     Headline
     	  The ambient chain complex of a filtered complex
     Usage
     	  C = chainComplex K
     Inputs
     	  K:FilteredComplex
     Outputs
     	  C:ChainComplex
     Description
     	  Text 
	       Returns the ambient chain complex of the filtered complex.
	       
    ///
  
doc ///
     Key
     	  (spectralSequence, FilteredComplex)
	  spectralSequence
     Headline
     	  construct a spectralSequence from a filtered complex
     Usage
     	  E = spectralSequence K
     Inputs
     	  K:FilteredComplex
	       A filtered complex
     Outputs
     	  E:SpectralSequence
     Description
     	  Text 
	       Returns the spectral sequence associated to the filtered complex.
    ///
    doc ///
     Key
     	   (Hom, FilteredComplex, ChainComplex)
	   (Hom, ChainComplex, FilteredComplex)
     Headline
     	  the filtered complex Hom complex
     Usage
     	  f = Hom(K,C)
     Inputs
     	  K:FilteredComplex
	  C:ChainComplex
     Outputs
     	  f:FilteredComplex
     Description
     	  Text 
	      Returns the filtrations of the Hom complex determined by the double complex  
    ///
    doc ///
     Key
     	   (chainComplex, SpectralSequence)
     Headline
     	  the underlying chain complex of a Spectral Sequence
     Usage
     	  K = chainComplex E
     Inputs
     	  E:SpectralSequence
     Outputs
     	  K:ChainComplex
     Description
     	  Text 
	       Returns the underlying chain complex of a spectral sequence.
    ///

 doc ///
     Key
     	  (spectralSequencePage, FilteredComplex, ZZ)
	  spectralSequencePage
     Headline
     	  construct a SpectralSequencePage from a filtered complex
     Usage
     	  E = spectralSequencePage(K,r)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
	  r:ZZ
     Outputs
     	  E:SpectralSequencePage
     Description
     	  Text 
	       Returns the rth page of the spectral sequence determined by K.
     ///
 
doc ///
     Key 
          (support,ChainComplex)
     Headline 
         compute the support of a chain complex
     Usage 
         L = support C 
     Inputs 
	  C: ChainComplex
     Outputs
          L: List
     Description	  
     	  Text
	     Produces a list consisting of those the homological degrees for which 
	     the corresponding module is non-zero.
	  Example 
	    needsPackage "SpectralSequences"
	    A = QQ[x,y]
	    C = res ideal vars A
	    L = support C
	    D = koszul vars A
	    M = support D
     SeeAlso
      	  (spots, ChainComplex) 
    /// 
    
     doc ///
     Key
     	  (symbol _, SpectralSequence, ZZ)
	  (symbol _, SpectralSequence, InfiniteNumber)
     Headline
     	  the kth page of a spectral sequence
     Usage
     	  P = E_k
     Inputs
     	  E:SpectralSequence
	  k:ZZ
     Outputs
     	  P: SpectralSequencePage
     Description
     	  Text 
	      Returns the kth page of the spectral sequence.
     ///
     
     doc ///
     Key
     	  (symbol _, SpectralSequencePageMap, List)
     Headline
     	  The {p,q}th map on of a spectral sequence page 
     Usage
     	  d = D _L
     Inputs
     	  D:SpectralSequencePageMap
	  L:List
	      A list L = \{p,q\} of integers.
     Outputs
     	  d: Matrix
     Description
     	  Text 
	      Returns the \{p,q\}th map on a spectral sequence page.
     ///

doc ///
     Key
     	  (symbol ^, SpectralSequencePageMap, List)
     Headline
     	  the {p,q}th map on of a spectral sequence page 
     Usage
     	  d = D ^L
     Inputs
     	  D:SpectralSequencePageMap
	  L:List
	      A list L = \{p,q\} of integers.
     Outputs
     	  d: Matrix
     Description
     	  Text 
	      Returns the \{p,q\}th map on a spectral sequence page.
     ///
         
     
doc ///
     Key
     	  (symbol ^, SpectralSequence, ZZ)
	  (symbol ^, SpectralSequence, InfiniteNumber)
     Headline
     	  the kth page of a spectral sequence
     Usage
     	  P = E^k
     Inputs
     	  E:SpectralSequence
	  k:ZZ
     Outputs
     	  P: SpectralSequencePage
     Description
     	  Text 
	      Returns the kth page of the spectral sequence.
     ///


  doc ///
     Key
     	  (symbol ^, SpectralSequencePage, List)
     Headline
     	  the module in the i,j position on the page
     Usage
     	  M = P^L
     Inputs
     	  P:SpectralSequencePage
	  L:List
	       A list L = \{i,j\} of integers
     Outputs
     	  M:Module
     Description
     	  Text 
	       Returns the module in the \{i,j\}   position in the spectral sequence page. 
	       (Using cohomological indexing conventions.)  
    ///

doc ///
     Key
     	  (symbol _, SpectralSequencePage, List)
	  
     Headline
     	  the module in the i,j position on the page
     Usage
     	  M = P_L
     Inputs
     	  P:SpectralSequencePage
	  L:List
	       A list L = \{i,j\} of integers
     Outputs
     	  M:Module
     Description
     	  Text 
	       Returns the module in the \{i,j\} \ position in the spectral sequence page. 
	       (Using homological indexing conventions.)  
    ///


doc ///
     Key
     	   (symbol **, ChainComplex, FilteredComplex)
	   (symbol **, FilteredComplex, ChainComplex)
     Headline
     	  filtered Tensor product of complexes
     Usage
     	  KK = C ** K
	  KK = K ** C
     Inputs
     	  C:ChainComplex
	  K:FilteredComplex
     Outputs
     	  KK:FilteredComplex
     Description
     	  Text 
	       Returns the two filtrations of K_infty ** C determined by the double complex
    ///
 doc ///
     Key
     	  (inducedMap, FilteredComplex, ZZ)
     Headline
     	  the ith inclusion map in a filtered complex
     Usage
     	  f = inducedMap(K,i)
     Inputs
     	  K:FilteredComplex
	  i:ZZ
     Outputs
     	  f:ChainComplexMap
     Description
     	  Text 
	       Returns the chain complex map specifying the inclusion of the i piece 
	       of the filtered
	       complex to the ambeint chain complex.
    ///
doc ///
     Key
          (symbol _, FilteredComplex, ZZ)
	  (symbol _, FilteredComplex, InfiniteNumber)
     Headline
     	  the filtered pieces
     Usage
     	  C = K _ j
     Inputs
     	  K:FilteredComplex
	  j:ZZ 
	       an integer, infinity, or -infinity
     Outputs
     	  C:ChainComplex
     Description
     	  Text 
	       Returns the chain complex in (homological) filtration degree j.  
	       The relationship	$K _ j = K ^{(-j)}$ holds.
	       
     SeeAlso    
     	  (symbol ^, FilteredComplex, ZZ)           
    ///

doc ///
     Key
          (symbol ^, FilteredComplex, ZZ)
	  (symbol ^, FilteredComplex, InfiniteNumber)
     Headline
     	  the filtered pieces
     Usage
     	  C = K ^  j
     Inputs
     	  K:FilteredComplex
	  j:ZZ 
	       an integer, infinity, or -infinity
     Outputs
     	  C:ChainComplex
     Description
     	  Text 
	       Returns the chain complex in (cohomological) filtration degree j.
	       The relationship $K ^ j = K _{(-j)}$ holds.
     SeeAlso
     	  (symbol _, FilteredComplex, ZZ)	       
    ///


    doc ///
     Key
  	  (spots, FilteredComplex)
     Headline
     	  the sorted filtration degrees of a filtered complex 
     Usage
     	  L = spots H
     Inputs
     	  H: FilteredComplex 
	       
     Outputs
     	  L:List
     Description
     	  Text 
	       Returns the sorted filtration degrees of a filtered complex
	       which the computer explicitly remembers. 	    	      
///
  
  doc ///
     Key
  	  (spots, ChainComplex)
     Headline
     	  the sorted filtration degrees of a chain complex 
     Usage
     	  L = spots H
     Inputs
     	  H: ChainComplex 
	       
     Outputs
     	  L:List
     Description
     	  Text 
	       Returns the sorted homological degrees of a chain complex 
	       which the computer explicitly remembers. 	    	      
///
  doc ///
     Key
  	  spots
     Headline
     	  the sorted integer keys of a hash table.
     Usage
     	  L = spots H
     Inputs
     	  H: HashTable
	       
     Outputs
     	  L:List
     Description
     	  Text 
	       Returns the sorted integer keys of a hash table.	      
///

  doc ///
     Key
     	  connectingMorphism
     Headline
          use spectral sequences to compute connecting morphisms
     Usage 
         g = connectingMorphism(f, n)
     Inputs
         f:ChainComplexMap
	 n:ZZ	 
     Outputs
         g:Matrix 
     Description
          Text
	       Given a morphism $f: A \rightarrow B$ of chain complexes
	       returns the connecting map $H_{n+1}( coker f) \rightarrow H_n (im f)$.
///

doc ///
     Key
     	  (connectingMorphism, ChainComplexMap,ZZ)
     Headline
          use spectral sequences to compute connecting morphisms
     Usage 
         g = connectingMorphism(f, n)
     Inputs
         f:ChainComplexMap
	 n:ZZ	 
     Outputs
         g:Matrix 
     Description
          Text
	       Given a morphism $f: A \rightarrow B$ of chain complexes
	       returns the connecting map $H_{n+1}( coker f) \rightarrow H_n (im f)$.
///

TEST ///
restart;
needsPackage "SpectralSequences";
A = QQ[a,b,c];
C = new ChainComplex;
C.ring = A;
filtererdComplex C
///    

TEST ///
restart;
needsPackage "SpectralSequences";
A = QQ[a,b,c];
D = simplicialComplex {a*b*c};
F2D = D;
F1D = simplicialComplex {a*b,a*c,b*c};
F0D = simplicialComplex {a,b,c};
K = filteredComplex({F2D,F1D,F0D}, ReducedHomology => false);
E = prune spectralSequence K;
e = spectralSequence K;
assert(
all(for i from 0 to 5 list all(keys support E^i, j -> isIsomorphism rpqIsomorphism(E,j#0,j#1,i)
), i -> i == true)
)
assert(
all(for i from 0 to 5 list all(keys support E^i, j -> isIsomorphism rpqIsomorphism(e,j#0,j#1,i)
), i -> i == true)
)
///

end


--------------------------------------------------------------------------------
restart
uninstallPackage"SpectralSequences"
installPackage"SpectralSequences"
installPackage("SpectralSequences", RemakeAllDocumentation => true)
check "SpectralSequences";
viewHelp SpectralSequences
------------------------------------------
-- New scratch examples trying to illustrate the new experimental types --

--- I wonder how hard it would be to make double chain complexes?
-- the following shows that maybe it is not so hard now that we have
-- the data types page and pageMap.
---
restart
needsPackage"SpectralSequences"
C = new DoubleChainComplex
keys C.dd
C.dd.xx
C.dd.yy

A = QQ[x]
C
C.ring = A
keys C.dd


C#{0,0} = A^1

C#{1,0} = A^1

C#{0,1} = A^1 

C#{1,1} = A^1

C.dd.degree

C

C.dd.yy #{0,1} = map(C_{0,0}, C_{0,1}, id_(A^1))

C.dd.yy #{1,1} = map(C_{1,0}, C_{1,1}, id_(A^1))

C.dd.xx #{1,1} = map(C_{0,1}, C_{1,1}, id_(A^1))

C.dd.xx #{1,0} = map(C_{1,0}, C_{0,0}, - id_(A^1))

C.dd.xx
C.dd.yy

C.dd.yy _{0,1}
C.dd.yy _{0,0}
C.dd.yy_{10,10}
C.dd.xx_{1,1}
C.dd.xx
C.dd.xx_{0,1}

C

(C.dd.xx #{1,0}) * (C.dd.yy #{1,1}) == - (C.dd.yy #{0,1}) * (C.dd.xx #{1,1})

C.dd.yy.degree = {0,-1}
C.dd.yy

C.dd.xx.degree = {-1,0}

C.dd.xx

spots(C.dd.yy)

keys C.dd.yy

(C.dd).yy


restart
needsPackage"SpectralSequences"
A = QQ[x,y,z]
I = monomialCurveIdeal(A, {1,3})
M = coker vars A
hilbertPolynomial M
peek hilbertPolynomial I
hilbertPolynomial 3
hilbertPolynomial 0
P = hilbertPolynomial I
P + 3
3 + P
P - 3
- P + 3

----
----
---

restart
needsPackage "SpectralSequences";
-- C \subseteq PP^1 x PP^1 type (3,3)
-- Use hypercohomology to compute HH OO_C(1,0) 
R = ZZ/101[a_0..b_1, Degrees=>{2:{1,0},2:{0,1}}]; -- PP^1 x PP^1
B = intersect(ideal(a_0,a_1),ideal(b_0,b_1)) ; -- irrelevant ideal
B = B_*/(x -> x^5)//ideal ; -- Frobenius power 
G = res image gens B
I = ideal random(R^1, R^{{-3,-3}}) -- ideal of C
F = res comodule I 
-- Twist F by a line of ruling and make filtered complex whose ss abuts to HH OO_C(1,0) 
K = Hom(G , filteredComplex (F ** R^{{1,0}})) ;
E = prune spectralSequence K ; --the (algebraic version of the) spectral sequence degenerates on the second page 
E^1 
basis({0,0},E^1)
keys E^1
E^1
prunningMaps(E^1)

---
---
restart
needsPackage "SpectralSequences";
A = QQ[x,y,z,w]
I = coker gens monomialCurveIdeal(A,{1,2,3})
hilbertPolynomial(A^0) == 0
hilbertPolynomial(I) != 0
hilbertPolynomial(A^0) != 0
------
--
H = complete res I
J = coker gens monomialCurveIdeal(A,{1,3,4})
F = complete res J
E = prune spectralSequence ((filteredComplex H) ** F)
K = (filteredComplex H) ** F
basis(0,E^0)
basis(0,E^0_{0,0})
basis(0,E^0)
basis(0,E^1)
basis(0,(prune HH K_infinity)_1)
prune HH K_infinity
Hilb = hilbertPolynomial(E^0)
Hilb_{0,0}
Hilb_{1,0}
hilbertPolynomial(E^infinity)
E^infinity
prune HH K_infinity
hilbertPolynomial (HH K_infinity) _0
-----
--
restart
needsPackage "SpectralSequences";
-- Try to compute the cohomology of OO_X(4,0,-4), where
-- X in P^2 x P^2 x P^2 is a c.i. of three (1,1,1) forms
-- should compare with Mike Stillmans p2xp2xp2 example.
R = ZZ/101[a_0..c_2, Degrees=>{3:{1,0,0},3:{0,1,0},3:{0,0,1}}]
B = intersect(ideal(a_0,a_1,a_2),ideal(b_0,b_1,b_2),ideal(c_0,c_1,c_2))
B = B_*/(x -> x^5)//ideal
G = res image gens B
I = ideal random(R^3, R^{{-1,-1,-1}})
D = res comodule I
D = D ** R^{{4,0,-4}}
K = Hom(G, filteredComplex(D)) ;
E = prune spectralSequence K ;
e = spectralSequence K ;
E^0 ;
E^0
basis({0,0},E^0_{1,-4});
-- the E^0 page sees to be two large for the net to finish.
-- try the E^1 page.
E^1 ;
basis({0,0},E^1)
-- using the this picture we deduce that the spectral sequence (corresponding to sheaves)
-- degenerates at the E^1 page.
---

-------------------------------------------
--- end of experimental scratch examples.
-------------------------------------------


-- The following are some examples which illustrate the current state of the code.
-- All examples seem to work correctly.
--

restart
needsPackage "SpectralSequences";
-- needsPackage "ChainComplexExtras";
-- C \subseteq PP^1 x PP^1 type (3,3)
-- Use hypercohomology to compute HH OO_C(1,0) 
R = ZZ/101[a_0..b_1, Degrees=>{2:{1,0},2:{0,1}}]; -- PP^1 x PP^1
B = intersect(ideal(a_0,a_1),ideal(b_0,b_1)) ; -- irrelevant ideal
B = B_*/(x -> x^5)//ideal ; -- Frobenius power 
G = res image gens B
I = ideal random(R^1, R^{{-3,-3}}) -- ideal of C
F = res comodule I 
-- Twist F by a line of ruling and make filtered complex whose ss abuts to HH OO_C(1,0) 
K = Hom(G , filteredComplex (F ** R^{{1,0}})) ;
E = prune spectralSequence K ; --the spectral sequence degenerates on the second page 
E^1 
E^2 ; -- output is a mess
basis({0,0}, E^2_{0,0}) --  == HH^0 OO_C(1,0)
basis({0,0}, E^2_{1,-2}) --  == HH^1 OO_C(1,0)
-- Now use spectral sequences to commute the connecting map 
-- HH^1(C, OO_C(1,0)) --> HH^2(X, OO_X(-2,-3)) which is an isom. 
b = chainComplex gradedModule R^{{1,0}} -- make line bundle a chain complex
a = chainComplex gradedModule R^{{-2,-3}}
-- make the map OO(-2, -3) --> OO(1,0)     
f = chainComplexMap(b, a,{random(R^1, R^{{-3,-3}})}) ; 
k = filteredComplex ({Hom(G,f)}) ; -- the two step filtered complex we want
e = prune spectralSequence k ;
e^1 .dd_{1,-2} -- the connecting map HH^1(C, OO_C(1,0)) --> HH^2(X, OO_X(-2,-3)) 
basis({0,0}, image e^1 .dd_{1,-2})  -- image 2-dimensional
basis({0,0}, ker e^1 .dd_{1,-2}) -- map is injective
basis({0,0}, target e^1 .dd_{1,-2}) -- target 2-dimensional 
basis({0,0}, source e^1 .dd_{1,-2}) -- source 2 dimensional 

restart
needsPackage "SpectralSequences";
-- Try to compute the cohomology of OO_X(4,0,-4), where
-- X in P^2 x P^2 x P^2 is a c.i. of three (1,1,1) forms
-- should compare with Mike Stillmans p2xp2xp2 example.

R = ZZ/101[a_0..c_2, Degrees=>{3:{1,0,0},3:{0,1,0},3:{0,0,1}}]
B = intersect(ideal(a_0,a_1,a_2),ideal(b_0,b_1,b_2),ideal(c_0,c_1,c_2))
B = B_*/(x -> x^5)//ideal
G = res image gens B
I = ideal random(R^3, R^{{-1,-1,-1}})
D = res comodule I
D = D ** R^{{4,0,-4}}

K = Hom(G, filteredComplex(D)) ;
E = prune spectralSequence K ;
e = spectralSequence K ;
E^0 ;
E^1 ;
e^1 ;

e^2 ;
numgens image basis({0,0,0}, e^1 _{0, - 2})
numgens image basis({0,0,0}, e^1 _{2, - 4})

-- can compute the E^0 and E^1 pages
numgens image basis({0,0,0}, E^1 _{0, - 2})
numgens image basis({0,0,0}, E^1 _{2, - 4})
E^1

-- computing the E^2 page takes too long
-- E^2 ;

--e^2 ;


-- Try PP^1 x PP^1 X PP^1
-- computer could compute the E^2 page in this example.  
restart
needsPackage "SpectralSequences";

R = ZZ/101[a_0..c_1, Degrees=>{2:{1,0,0},2:{0,1,0},2:{0,0,1}}]
B = intersect(ideal(a_0,a_1),ideal(b_0,b_1), ideal(c_0,c_1))
B = B_*/(x -> x^5)//ideal
C = res image gens B
C' = prune dual C;
I = ideal random(R^2, R^{{-1,-1,-1}});
D = res comodule I;

K = (C') ** (filteredComplex D);

E = prune spectralSequence K

E^0;
E^1;
E^2;

--Try PP^1 x PP^2 
-- The E^2 page could be computed as well.  
restart
needsPackage "SpectralSequences";

R = ZZ/101[a_0,a_1,b_0..b_2, Degrees=>{2:{1,0},3:{0,1}}]
B = intersect(ideal(a_0,a_1),ideal(b_0,b_1,b_2))
B = B_*/(x -> x^5)//ideal
C = res image gens B
C' = prune dual C;
I = ideal random(R^2, R^{{-1,-1}});
D = res comodule I;
K = (C') ** (filteredComplex D);

E = prune spectralSequence K

E^0
E^1
E^2


-------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;


A = QQ[x_0..x_4]

C = coker gens monomialCurveIdeal(A,{1,3,4})

m = ideal(x_0..x_2)

y = ideal(x_3..x_4)

E = koszul gens m
 
F = (koszul gens y) 

K = (filteredComplex E) ** F

EE = prune spectralSequence K
EE^0
EE^1
EE^2

-- now let's try to tensor E with C and then see what happens.

e = E ** C

k = (filteredComplex e) ** F

ee = prune spectralSequence k
ee^0
ee^1
ee^2


--
-- Now try to replace C with a free resolution.

e = E ** G
k = filteredComplex(e) ** F;
ee = prune spectralSequence k
ee^0
ee^1
ee^1 .dd
ee^2

-------
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

-- The following example is taken from p. 127, Fig 7.2 of 
-- Zomorodian's "Topology for computing"


A = ZZ [s,t,u,v,w] 

d0 = simplicialComplex {s}
d1 = simplicialComplex {s,t}
d2 = simplicialComplex {s,t,u}
d3 = simplicialComplex {s*t, u}
d4 = simplicialComplex {s*t, u, v}
d5 = simplicialComplex {s*t, u, v, w}
d6 = simplicialComplex {s*t, s*w ,u, v}
d7 = simplicialComplex {s*t, s*w ,t * w, u, v}
d8 = simplicialComplex {s*t, s*w ,t * w, u * v}
d9 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v}
d10 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u}
d11 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w}
d12 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u}
d13 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w}
d14 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w}
d15 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u}
d16 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v}
d17 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v, s*t*w}

L = reverse {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17}
K = filteredComplex (L, ReducedHomology => false)

E = prune spectralSequence K
E^0
E^0 .dd
E^1
E^1 .dd
E^2
E^2 .dd
E^3
E^3 .dd
E^4
E^4 .dd
E^5
E^5 .dd
E^6
E^6 .dd
E^7
E^7 .dd
E^8
E^8 .dd
E^9
E^9 .dd
E^infinity
prune HH K_infinity

-- let's try the one on page 138, figure 7.11.

S = ZZ[a,b,c,d]
d0 = simplicialComplex {a,b}
d1 = simplicialComplex {a,b,c,d, a* b, b* c}
d2 = simplicialComplex {a,b,c,d, a* b, b* c,c*d, a* d }
d3 = simplicialComplex {a,b,c,d, a* b, b* c,c*d, a* d , a* c}
d4 = simplicialComplex {a,b,c,d, a* b, b* c,c*d, a* d , a* c, a*b*c}
d5 = simplicialComplex {a,b,c,d, a* b, b* c,c*d, a* d , a* c, a*b*c, a* c* d}

l = {d0,d1,d2,d3,d4,d5}
k = filteredComplex (reverse l, ReducedHomology => false)
e = prune spectralSequence k
e^0
e^0 .dd
e^1
e^1 .dd

e^2
e^2 .dd

e^3
e^3 .dd

e^4

prune HH k_infinity

---
-- The following illustrates examples arising from simplicial complexes
-- associated to matrices.
-- Nathan got this idea by reading the paper "Minimal Resolutions and the Homology 
-- of Matching and Chessboard Complexes" by V.REINER and J. Roberts
--  the simplicial complexes produced here are surely related
-- to the chessboard complexes of that paper.  the precise relationship
-- needs to be clarified.  
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;
-- the following scripts are used in this example.


-- the following produces a simplicial complex 
-- by considering the terms of appropriate
-- minors of a generic matrix.

matrixSimplicialComplex = method()
matrixSimplicialComplex(Matrix,InfiniteNumber) :=
matrixSimplicialComplex (Matrix,ZZ) := SimplicialComplex => (M,n) -> ( 
     simplicialComplex flatten(apply(flatten entries gens minors(n,M), i-> terms i))
     )

-- return the size e.g. {# rows, # columns} of a matrix.
size Matrix := (M) -> ({length flatten entries M_{0}, length flatten entries M^{0}})

-- compute the maximal minors of a matrix.
minors(InfiniteNumber,Matrix) := Ideal => opts ->(j,M) -> ( 
     if j < 0 then ideal(1) else minors(min size M, M)
     )

-- the following produces a list of nested simplicial complexes.
-- the first element of the list is the simplicial
-- complex corresponding to the maximal minmors of a generic
-- m x n matrix.  This is the m x n chessboard complex.
-- the other simplicial complexes in the filtration correspond to the
-- maximal minors of the submatrix obtained by deleting successive columns.
-- there will be another filteration obtained by successive rows.
-- to get this one, interchange m and n in the constructor.
-- strictly speaking, the simplicial complexes created by the
-- constructor are different, but they will be what we want
-- up to relabeling.   

filteredMatrixSimplicialComplex = method( )

filteredMatrixSimplicialComplex(ZZ,ZZ,Ring) := (m,n,R) -> (
     M := genericMatrix(R,m,n);
     numberOfColumns := length flatten entries M^{0};
     myList := reverse apply(numberOfColumns, i -> 
	  matrixSimplicialComplex(M_{0..i},infinity))
)

-- the following method checks if the simplicial complex E is a sub complex of D.
isSubSimplicialComplex = method()
isSubSimplicialComplex(SimplicialComplex,SimplicialComplex):=(E,D)->(
     allFaces := D -> (set flatten apply((dim D)+1,i-> flatten entries faces(i,D)));
     L := allFaces(D);
     K := flatten entries facets E;
     all(apply(#K, i -> member(K#i,L)), i -> i == true)
      )
--
-- now try some examples.
R = QQ[a..z]

L = filteredMatrixSimplicialComplex(3,3,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3
prune HH K_infinity

L = filteredMatrixSimplicialComplex(4,2,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
prune HH K_infinity

L = filteredMatrixSimplicialComplex(2,4,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^3
prune HH K_infinity

L = filteredMatrixSimplicialComplex(3,4,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^3
prune HH K_infinity

L = filteredMatrixSimplicialComplex(4,3,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^3
prune HH K_infinity

L = filteredMatrixSimplicialComplex(3,5,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3
E^3 .dd
E^4
E^4 .dd
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(5,3,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
prune HH K_infinity

L = filteredMatrixSimplicialComplex(4,5,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3 
E^3 .dd
E^4
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(5,4,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3 
E^3 .dd
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(2,5,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^3
E^3 .dd
E^4
E^4 .dd
E^5
E^5 .dd
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(5,2,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(2,6,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2 .dd
E^3 .dd 
E^4
E^4 .dd
E^5
E^5 .dd
E^6
E^6 .dd
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(6,2,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
prune HH K_infinity

L = filteredMatrixSimplicialComplex(3,6,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3
E^3 .dd
E^4 
E^4 .dd
E^5
E^5 .dd
E^infinity
prune HH K_infinity

L = filteredMatrixSimplicialComplex(6,3,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
prune HH K_infinity

L = filteredMatrixSimplicialComplex(4,6,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false);
prune K_infinity
E = prune spectralSequence K
E^0
E^1
E^2
E^2 .dd
E^3
E^3 .dd
E^4
E^4 .dd
E^infinity
prune HH K_infinity


------
---------------------------------------------------------------
--- Easy examples of spectral sequences arising from filtrations 
--   of simplicial complexes.
-- All of these examples are small enough that they can be
-- easily computed by hand.
------------------------------------------------------------
-----------------------------------------------------------

-- Example 1 --
-------------------------------------------------------------
-- this is example 2 in Nathan's notes.
--------------------------------------------------------------


restart
needsPackage "SpectralSequences";

A=QQ[a,b,c,d]
D=simplicialComplex {a*d*c, a*b, a*c, b*c}
F2D=D
F1D= simplicialComplex {a*c, d}
F0D = simplicialComplex {a,d}
K= filteredComplex({F2D, F1D, F0D},ReducedHomology => false)
E = spectralSequence(K)
e = prune E
E^0
E^1
E^2
E^3
E^infinity
e^0
e^1
e^2
e^3
prune HH K_infinity
e^2 .dd
---------------
-- using the above we conclude that the map with source 2,-1 on the E2 page
-- must have a 1-diml image and 1-diml kernel.
-------------
---------------------------------------------------
-- the above aggrees with my calculations by hand.
---------------------------------------------------
rpqIsomorphism(E,0,0,0)
keys support E^0 
all(keys support E^0, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- cool.
all(keys support E^1, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
-- cool.
all(keys support E^2, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
-- cool.
all(keys support E^5, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,5))
-- cool.
----------------------------------------------------------

-- Example 2 --
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
-- New example to try.  Everything in this example can be computed easily by hand. ---
-- This is example 1 in Nathan's notes.-----------------------------------------------------
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
-- in order to get the example I did by hand want to remove the
-- contribution of the empty face from these
-- chain complexes.

K=filteredComplex({F3D,F2D,F1D,F0D}, ReducedHomology => false)
K
prune HH K_3

E = prune spectralSequence K

E^0
E^0 .dd
E^0
E^1
E^0 .dd_{1,0}
E^1 .dd
E^1
E^0
E^2

prune HH K_infinity

----------------------------------------------------------------
-- All of the above agrees with hand calculations --
----------------------------------------------------------------

-- Example 3 --
------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
--  This is example 3 in Nathan's Notes
--
restart
needsPackage "SpectralSequences";
--needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[a,b,c]
D = simplicialComplex {a*b*c}
F2D = D
F1D = simplicialComplex {a*b,a*c,b*c}
F0D = simplicialComplex {a,b,c}
K = filteredComplex({F2D,F1D,F0D}, ReducedHomology => false)
C = K_infinity
prune HH C
E = prune spectralSequence K
E^0
E^1
E^2
prune HH K_infinity
E^0 .dd
E^1 .dd
E^2 .dd

----------------------------------------------------
-- the above agrees with my caclulations by hand. --
----------------------------------------------------

all(keys support E^0, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
all(keys support E^1, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
all(keys support E^2, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,2))
all(keys support E^3, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,3))


e = spectralSequence K
all(keys support e^0, i ->  isIsomorphism rpqIsomorphism(e,i#0,i#1,0))
-- cool.
all(keys support  e^1 , i ->  isIsomorphism rpqIsomorphism(e,i#0,i#1,1))
-- cool.
all(keys support e^2, i ->  isIsomorphism rpqIsomorphism(e,i#0,i#1,2))
-- cool.
all(keys support e^5, i ->  isIsomorphism rpqIsomorphism(e,i#0,i#1,5))
-- cool.

--------------------------------------------------
-- -- Example 4 --
-------------------------------------
--Nathan's first example
-- this is example 0 in Nathan's notes.
--It shows how to make a filtered complex by expicitly making chain complexes and a
-- list of chain complex maps 
-------------------------------------
restart
needsPackage "SpectralSequences";
needsPackage "ChainComplexExtras";
debug SpectralSequences;
-- This is the first example I studied.
-- It has the advantage that we can compute everything explicitly by hand.
k = QQ
d2 = matrix(k,{{1},{0}})
d1 = matrix(k,{{0,1}})
-- make a chain complex with these maps
-- throughout this example I'm thinking homologically (by default this is how M2
-- thinks of an displays chain complexes).  
-- NAMELY THE DIFFERENTIAL HAS DEGREE -1.  
C = chainComplex({d1,d2})
prune HH C
-- the above shows that C is acyclic.  
--Hence whatever spectral sequences associated to filtrations of C 
-- we compute they should abut to zero.
-- first make subcomplexes of C which will allow us to make a filtered complex
-- I want to make a filtration of the form
-- C=F3C > F2C > F1C > F0C =0.
-- first make the modules.

F3C2 = image matrix(k,{{1}})
F3C1 = image matrix(k,{{1,0},{0,1}})
F3C0 = image matrix(k,{{1}})


-- The F3C complex. (Which should be isomorphic to C.  I want to explicitly make
-- computer realize all terms in this complex as appropriate sub-quotients.)

F3C = chainComplex({inducedMap(F3C0,F3C1,C.dd_1),inducedMap(F3C1,F3C2,C.dd_2)})
F3C == C
-- so I seem to have inputed things correctly.
-- The F2C complex. 
-- first make the modules 

F2C2 = image matrix(k,{{1}})
F2C1 = image matrix(k,{{1,0},{0,0}})
F2C0 = image matrix(k,{{1}})
-- The F2C complex.  (Which should be a sub complex of F3C.)
F2C = chainComplex({inducedMap(F2C0,F2C1,C.dd_1),inducedMap(F2C1,F2C2,C.dd_2)})
-- It is clear that the F2C complex is a sub complex of F3C in the most obvious way.
--  Now try to construct an explicit chain complex map yielding this inclusion
-- of chain complexes.
-- Want to construct a chain complex map defining the inclusion F2C --> F3C.
-- we will label such maps by the source. (The number 2 in this case.) 
m2 = chainComplexMap(F3C,F2C,{inducedMap(F3C_0,F2C_0,id_(F3C_0)), inducedMap(F3C_1,F2C_1,id_(F3C_1)),inducedMap(F3C_2,F2C_2,id_(F3C_2))})
-------------------------------------------------------------
-- The F1C complex.  (Which should satisfy the relation F3C>F2C>F1C.)
-- make the modules.

F1C2 = image matrix(k,{{0}})
F1C1 = image matrix(k,{{1,0},{0,0}})
F1C0 = image matrix(k,{{1}})

--  The F2C complex.  (Which should be a sub complex of F2C and F3C.  For now
-- I will make it an explicit subcomplex of F3C which will be the "ambient complex".)

F1C = chainComplex({inducedMap(F1C0,F1C1,C.dd_1),inducedMap(F1C1,F1C2,C.dd_2)})

m1 = chainComplexMap(F3C,F1C,{inducedMap(F3C_0,F1C_0,id_(F3C_0)), inducedMap(F3C_1,F1C_1,id_(F3C_1)),inducedMap(F3C_2,F1C_2,id_(F3C_2))})


-- the terms / modules corresponding to the F0C complex. 
F0C2 = image matrix(k,{{0}})
F0C1 = image matrix(k,{{0,0},{0,0}})
F0C0 = image matrix(k,{{0}})


F0C = chainComplex({inducedMap(F0C0,F0C1,C.dd_1),inducedMap(F0C1,F0C2,C.dd_2)})

-- try to make a chain complex map expressing F0C as a subcomplex of F3C.
m0 = chainComplexMap(F3C,F0C,{inducedMap(F3C_0,F0C_0,id_(F3C_0)), inducedMap(F3C_1,F0C_1,id_(F3C_1)),inducedMap(F3C_2,F0C_2,id_(F3C_2))})

K = filteredComplex{m2,m1,m0}
E = prune spectralSequence K
E^0
E^1
E^2
E^3
E^2 .dd
----
----


--------------------------------------------------------------
-- spectral sequences arising from topological fibrations. ---
--------------------------------------------------------------


-- Example 5 --
-- In this example we compute the spectral sequence arising from
-- the quotient map
-- SS^2 --> RR PP^2, given by indentifying anti-podal points.


restart
installPackage"SpectralSequences"
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"


-- In order to give a combinatorial picture of the quotient map
-- SS^2 --> RR PP^2, given by indentifying anti-podal points, we
-- first make an appropriate simplicial realization of SS^2.

A = ZZ[v1,v2,v3,v4,v5,v6,v15,v12,v36,v34,v46,v25]

topHalf = {v3*v4*v5, v5*v4*v15, v15*v34*v4, 
     v15*v34*v1, v34*v1*v6, v34*v46*v6, 
     v36*v46*v6, v3*v4*v46, v4*v46*v34, v3*v46*v36
      }
botHalf = {v1*v6*v2, v6*v2*v36, v2*v36*v12,v36*v12*v3,
     v12*v3*v5, v12*v5*v25, v25*v5*v15, 
     v2*v12*v25, v1*v2*v25, v1*v25*v15
     }

-- the following is a simplicial complex whose topological realiztion is SS^2
-- note that we have added a few barycentric coordinates
twoSphere = simplicialComplex join(topHalf, botHalf)

facets twoSphere

C = truncate(chainComplex twoSphere,1)
prune HH C
-- so at least we've entered a simplicial complex whose homology agrees with that of
-- SS^2.

-- now write down our simplicial complex whose topological realization is RRPP^2.
R = ZZ[a,b,c,d,e,f]

realProjectivePlane = simplicialComplex {
     a*b*c, b*c*d, c*d*e, a*e*d, e*b*a, e*f*b, d*f*b, a*f*d, c*f*e,a*f*c}

C = truncate(chainComplex realProjectivePlane,1)
prune HH C
-- again, at least we've entered a simplical complex whose homology aggrees with that
-- of the real projective plane.
faces(twoSphere, 1)
help faces
faces(1,twoSphere)
faces(1,realProjectivePlane)

-- now compute the fibers over the anti-podal quotient map
-- SS^2 --> RRPP^2.
-- the way this works for example is as follows.
-- a = v3 ~ v1, b = v6 ~ v5, d = v36 ~ v15, c = v4 ~ v2, e = v34 ~ v12, f = v46 ~ v25

-- the fibers over the vertices of RRPP^2 are as follows.
F0twoSphere = simplicialComplex {v1,v3,v5,v6, v4,v2, v36,v15, v34,v12, v46,v25}

-- the fibers over the edges of RRPP^2 are as follows (hopefully computed correctly!)
F1twoSphere = simplicialComplex {
     v3*v4, v1*v2,
     v3*v5, v1*v6,
     v4*v5, v2*v6,
     v5*v15, v6*v36,
     v4*v34, v2*v12,
     v15*v34, v36*v12,
     v1*v15, v3*v36,
     v46*v34, v25*v12,
     v6*v34, v5*v12,
     v6*v46, v5*v25,
     v36*v46, v15*v25,
     v3*v46, v1*v25,
     v4*v15, v2*v36,
     v1*v34, v3*v12,
     v4*v46, v25*v2   
     }
-- the fibers over the faces is all of SS^2.
F2twoSphere = twoSphere
-- the resulting filtered complex is as follows.
K = filteredComplex({F2twoSphere, F1twoSphere, F0twoSphere}, ReducedHomology => false) 
-- compute the resulting spectral sequence.

prune image (image inducedMap(K_infinity,K_0)).dd_1

chainComplex F0twoSphere
prune K_0

help inducedMap
E = prune spectralSequence K
E^0
E^1
E^0 .dd
E^1 .dd
E^2
E^2 .dd

-----
------

--
-- Example 6 --
------------------------------------------------
-- In this example we compute the spectral sequence associated to the fibration
-- Klien Bottle --> SS^1 with fiber SS^1.
-- This fibration was trianulated by hand.
------------------------------------------------

restart
installPackage"SpectralSequences"
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"


S = ZZ[a00,a10,a20,a01,a11,a21,a02,a12,a22]

-- there will be 18 facets of Klein Bottle
f1 = a00*a10*a02
f2 = a02*a12*a10
f3 = a01*a02*a12
f4 = a01*a12*a11
f5 = a00*a01*a11
f6 = a00*a11*a10
f7 = a10*a12*a20
f8 = a12*a20*a22
f9 = a11*a12*a22
f10 = a11*a22*a21
f11 = a10*a11*a21
f12 = a10*a21*a20
f13 = a20*a22*a00
f14 = a22*a00*a01
f15 = a21*a22*a01
f16 = a21*a02*a01
f17 = a20*a21*a02
f18 = a20*a02*a00

-- the following simplicial complex is suppose to be
-- a triangulation of the Klien Bottle.

Delta = simplicialComplex {f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18}

C = truncate(chainComplex Delta,1)
prune HH C
C.dd
prune (ker C.dd_1 / image C.dd_2)
--  Note:  this is ZZ + ZZ/2ZZ.  So this is OK. --
--
-- so the homology of C agrees with the homology of the Klein Bottle.
-- the Klein Bottle has homology H_0 = ZZ, H_1 = ZZ+Z/2, H_i = 0 for i>=2.

-- 
-- Let's continue with this example further.

F1Delta = Delta

-- now want to make subsimplicial complex arising from the filtrations of the
-- inverse image of the verticies.

F0Delta = simplicialComplex {a00*a01,a01*a02
     ,a00*a02,a10*a11,a10*a12,a11*a12,a21*a20,a20*a22,a21*a22}

isSubSimplicialComplex(F0Delta,F1Delta)

-- so at least we've produced a sub-simplicial complex of F1Delta.

K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false)

E = prune spectralSequence K
E^0
E^1
E^2
E^3

-- Note that the spectral sequence is abutting to what it should -- the integral
-- homology of the Klien bottle

-- I wonder what happens if we use rational of coefficients?!

restart
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"


S = QQ[a00,a10,a20,a01,a11,a21,a02,a12,a22]

-- there will be 18 facets of Klein Bottle
f1 = a00*a10*a02
f2 = a02*a12*a10
f3 = a01*a02*a12
f4 = a01*a12*a11
f5 = a00*a01*a11
f6 = a00*a11*a10
f7 = a10*a12*a20
f8 = a12*a20*a22
f9 = a11*a12*a22
f10 = a11*a22*a21
f11 = a10*a11*a21
f12 = a10*a21*a20
f13 = a20*a22*a00
f14 = a22*a00*a01
f15 = a21*a22*a01
f16 = a21*a02*a01
f17 = a20*a21*a02
f18 = a20*a02*a00

-- the following simplicial complex is a triangulation of the Klien Bottle.

Delta = simplicialComplex {f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18}

C = truncate(chainComplex Delta,1)
prune HH C
-- so this seems to be OK?!
-- Now let's try to run the spectral sequence.

F1Delta = Delta

-- now want to make subsimplicial complex arising from the filtrations of the
-- inverse image of the verticies

F0Delta = simplicialComplex {a00*a01,a01*a02
     ,a00*a02,a10*a11,a10*a12,a11*a12,a21*a20,a20*a22,a21*a22}

isSubSimplicialComplex(F0Delta,F1Delta)

-- so at least we've produced a sub-simplicial complex of F1Delta.

K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false)

E = prune spectralSequence K
E^0
E^1
E^2
E^3
prune HH K_infinity
-- so things seem to be working OK.

-- I wonder what happens if we use Z/2 coefs??

restart
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"

S = ZZ/2[a00,a10,a20,a01,a11,a21,a02,a12,a22]

-- there will be 18 facets of Klein Bottle
f1 = a00*a10*a02
f2 = a02*a12*a10
f3 = a01*a02*a12
f4 = a01*a12*a11
f5 = a00*a01*a11
f6 = a00*a11*a10
f7 = a10*a12*a20
f8 = a12*a20*a22
f9 = a11*a12*a22
f10 = a11*a22*a21
f11 = a10*a11*a21
f12 = a10*a21*a20
f13 = a20*a22*a00
f14 = a22*a00*a01
f15 = a21*a22*a01
f16 = a21*a02*a01
f17 = a20*a21*a02
f18 = a20*a02*a00

-- the following simplicial complex is a triangulation of the Klien Bottle.

Delta = simplicialComplex {f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18}

C = truncate(chainComplex Delta,1)
prune HH C
-- so this seems to be OK?!

F1Delta = Delta

-- now want to make subsimplicial complex arising from the filtrations of the
-- inverse image of the verticies

F0Delta = simplicialComplex {a00*a01,a01*a02
     ,a00*a02,a10*a11,a10*a12,a11*a12,a21*a20,a20*a22,a21*a22}

isSubSimplicialComplex(F0Delta,F1Delta)

-- so at least we've produced a sub-simplicial complex of F1Delta.

K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false)

E = prune spectralSequence K
E^0
E^1
E^2
E^3
prune HH K_infinity
-- so things seem to be working OK.


-- Example 7 --
--------------------------------------------------------------------
-- In this example we compute the spectral sequence associated to the 
-- trivial fibration SS^1 x SS^1 --> SS^1, where
-- the map is given by one of the projections.
-- This fibration was also trianulated by hand.
--------------------------------------------------------------------

restart
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"

S = ZZ[a00,a10,a20,a01,a11,a21,a02,a12,a22]

-- there will be 18 facets of SS^1 x SS^1
f1 = a00*a02*a10
f2 = a02*a12*a10
f3 = a01*a02*a12
f4 = a01*a11*a12
f5 = a00*a01*a11
f6 = a00*a10*a11
f7 = a12*a10*a20
f8 = a12*a20*a22
f9 = a11*a12*a22
f10 = a11*a22*a21
f11 = a10*a11*a21
f12 = a10*a21*a20
f13 = a20*a22*a00
f14 = a22*a00*a02
f15 = a21*a22*a02
f16 = a21*a02*a01
f17 = a20*a21*a01
f18 = a20*a01*a00

Delta = simplicialComplex {f1,f2,f3,f4,f5,f6,f7,f8,f9,
     f10,f11,f12,f13,f14,f15,f16,f17,f18}
C = truncate(chainComplex Delta,1)
prune HH C
-- so the homology of C aggrees with the homology of the torus SS^1 x SS^1.

F1Delta = Delta

-- now want to make subsimplicial complex arising from the filtrations of the
-- inverse image of the verticies

F0Delta = simplicialComplex {a00*a01, a01*a02, a00*a02,
     a10*a11,a11*a12,a10*a12,
     a21*a20,a21*a22,a20*a22}

K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false) 
K_infinity == C
prune HH K_infinity

E = prune spectralSequence K
E^0
E^1
E^0_{-1,1}
E^0 .dd
E^1
E^1 .dd
E^2
E^2 .dd
E^infinity

-- Example 8 --
--
-- In this example we compute the spectral sequence arising from the Hopf Fibration
-- SS^1 --> SS^3 --> SS^2.
restart
installPackage"SpectralSequences"
needsPackage "SpectralSequences"
needsPackage "SimplicialComplexes"
B = QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2]
l1 = {a_0*b_0*b_1*c_1,a_0*b_0*c_0*c_1,a_0*a_1*b_1*c_1,b_0*b_1*c_1*d_1,b_0*c_0*c_1*d_2,a_0*a_1*c_1*d_2,a_0*c_0*c_1*d_2,b_0*c_1*d_1*d_2};
l2 = {b_1*c_1*c_2*a_2,b_1*c_1*a_1*a_2,b_1*b_2*c_2*a_2,c_1*c_2*a_2*d_1,c_1*a_1*a_2*d_2,b_1*b_2*a_2*d_2,b_1*a_1*a_2*d_2,c_1*a_2*d_1*d_2};
l3 = {c_2*a_2*a_0*b_0,c_2*a_2*b_2*b_0,c_2*c_0*a_0*b_0,a_2*a_0*b_0*d_1,a_2*b_2*b_0*d_2,c_2*c_0*b_0*d_2,c_2*b_2*b_0*d_2,a_2*b_0*d_1*d_2};
l4 = {a_0*b_0*b_1*d_1,a_0*b_1*d_0*d_1,b_1*c_1*c_2*d_1,b_1*c_2*d_0*d_1,a_0*a_2*c_2*d_1,a_0*c_2*d_0*d_1};
l5 = {a_0*b_1*d_0*d_2,a_0*a_1*b_1*d_2,b_1*c_2*d_0*d_2,b_1*b_2*c_2*d_2,a_0*c_2*d_0*d_2,a_0*c_0*c_2*d_2};
D = simplicialComplex(join(l1,l2,l3,l4,l5));
		    
f1l1 = {a_0*b_0*b_1,a_0*a_1*b_1,a_0*c_0*c_1,a_0*a_1*c_1,a_0*a_1*d_2,d_1*d_2,b_0*b_1*c_1,b_0*c_0*c_1,b_0*b_1*d_1,b_0*d_1*d_2,c_1*d_1*d_2,c_0*c_1*d_2};
f1l2 = {b_1*a_1*a_2,b_1*b_2*a_2,c_1*c_2*a_2,c_1*a_1*a_2,a_1*a_2*d_2,a_2*d_1*d_2,b_1*c_1*c_2,b_1*b_2*c_2,b_1*b_2*d_2,d_1*d_2,c_1*d_1*d_2,c_1*c_2*d_1};
f1l3 = {a_2*a_0*b_0,a_2*b_2*b_0, c_2*a_2*a_0,c_2*c_0*a_0,a_2*a_0*d_1,a_2*d_1*d_2,b_2*b_0*c_2,c_2*c_0*b_0,b_2*b_0*d_2,b_0*d_1*d_2,c_2*c_0*d_2,d_1*d_2};
f1l4 = {a_0*b_0*b_1,a_0*a_2,a_0*a_2*c_2,c_1*c_2,a_0*d_0*d_1,a_0*a_2*d_1,b_1*c_1*c_2,b_0*b_1,b_0*b_1*d_1,b_1*d_0*d_1,c_1*c_2*d_1,c_2*d_0*d_1}
f1l5 = {a_0*a_1*b_1,b_1*b_2,a_0*c_0*c_2,a_0*a_1,a_0*d_0*d_2,a_0*a_1*d_2,b_1*b_2*c_2,c_0*c_2,b_1*d_0*d_2,b_1*b_2*d_2,c_2*d_0*d_2,c_0*c_2*d_2};
F1D = simplicialComplex(join(f1l1,f1l2,f1l3,f1l4,f1l5));
		    
f0l1 = {a_0*a_1,b_0*b_1,c_0*c_1,d_1*d_2};
f0l2 = {a_1*a_2,b_1*b_2,c_1*c_2,d_1*d_2};
f0l3 = {a_0*a_2,b_0*b_2,c_0*c_2,d_1*d_2};
f0l4 = {a_0*a_2,b_0*b_1,c_1*c_2,d_0*d_1};
f0l5 = {a_0*a_1,b_1*b_2,c_0*c_2,d_0*d_2};
F0D = simplicialComplex(join(f0l1,f0l2,f0l3,f0l4,f0l5)); 
		    
K = filteredComplex({D,F1D,F0D},ReducedHomology => false)
E = spectralSequence K		    
E^0		    
E^1
E^2

E = prune spectralSequence K		    
E^0
E^1
E^2
E^2 .dd
E^3

---
---

--
-- Spectral sequence arising from double complexes.

-- Example 9 --
-- Balancing Tor. --
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[x,y,z,w]

help monomialCurveIdeal
I = coker gens monomialCurveIdeal(A,{1,2,3})
H = complete res I

J = coker gens monomialCurveIdeal(A,{1,3,4})
F = complete res J

E = prune spectralSequence ((filteredComplex H) ** F)

E^0
E^1
E^2
Tor_0(J,I) == E^2 _{0,0}
prune E^2 _{1,0} == prune Tor_1(J,I)
(Tor_1(J,I)) == (E^2 _{1,0}) -- this resturned false for some reason.  Strange...

EE = prune spectralSequence(H**(filteredComplex F))
EE^0
EE^1
EE^2
Tor_0(I,J) == EE ^2 _{0,0}
prune Tor_1(I,J)
prune E^2 _{1,0} == prune Tor_1(I,J)
Tor_1(I,J) == EE^2 _{1,0} -- this resturned false for some reason.  Strange...

---------------------------------------------------------------------
----------------------------------------------------------------------
-- Example 10 --
-- This example illustrates some aspects of the paper
--"A case study in bigraded commutative algebra" by Cox-Dickenstein-Schenck.
-- In that paper, an appropriate term on the E2 page of a suitable spectral sequence corresponds to non-koszul syzygies.
-- Using our indexing conventions, the E^2_{3,-1} term will be what the
-- E^{0,1}_2 term is in there paper.
-- We illustrate an instance of the non-generic case for non-Koszul syzygies.
-- This is acheived by looking at the three polynomials used in their Example 4.3.
-- The behaviour that we expect to exhibit is predicted by their Proposition 5.2.

restart
needsPackage "SpectralSequences"
R = QQ[x,y,z,w, Degrees => {{1,0},{1,0},{0,1},{0,1}}]
B = ideal(x*z, x*w, y*z, y*w)
p_0 = x^2*z
p_1 = y^2*w
p_2 = y^2*z+x^2*w
I = ideal(p_0,p_1,p_2)
-- make the frobenious power of the irrelevant ideal
B = B_*/(x -> x^2)//ideal
B
-- need to take a large enough power. 
-- it turns out that that 2 is large enough for this example 
G = res image gens B
F = koszul gens I
K = Hom(G, filteredComplex(F))
E = prune spectralSequence K
E^1
E^2
E^2_{3,-1}
basis({0,0}, E^2_{3, -1} ** R^{{2, 3}})
E^2 .dd_{3, -1}
E^2 .dd
basis({0,0}, image E^2 .dd_{3,-1} ** R^{{2,3}})
basis({0,0}, E^2_{1,0} ** R^{{2,3}})
-- this shows that there is a 1 dimensional space of non-Koszul syzygies of bi-degree (2,3)
-- which is also what is predicted by the paper.
basis({0,0}, E^2 _{3, -1} ** R^{{6,1}})
-- this shows that there is a 1 dimensional space of non-Koszul syzygies of bi-degree (6,1)
-- this is what is predicted by the paper.
isIsomorphism(E^2 .dd_{3, -1})
-- See Example 4.3 and Proposition 5.2 of their paper for more details related to this example.

--
--

----------------------------------------------------------------------------
-- Example 11 --
-- This example is just testing some aspects of the x and y filtrations of 
-- the Hom Complex  --
restart
needsPackage "SpectralSequences"

R = QQ[x,y,z,w, Degrees => {{1,0},{1,0},{0,1},{0,1}}]
B = ideal(x*z, x*w, y*z, y*w)

p_0 = x^2*z
p_1 = y^2*w
p_2 = y^2*z+x^2*w

I = ideal(p_0,p_1,p_2)

-- make the frobenious power of an ideal
Ideal ^ Array := (I,n) -> (ideal apply(flatten entries gens I, i -> i ^ (n#0)))
koszul gens B ^ [2]

-- the following complex is the cech like complex that we want to use.
K = truncate(Hom(koszul gens B ^ [6], R^1),-1)
C = koszul gens I

Hom(K,filteredComplex C)
Hom(filteredComplex K, C)


--------------------------------------
---------------------------------------

-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- examples by other people. ------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
--changeofRing = method ();
--changeofRing (Module,Module):= SpectralSequence => (M,N) -> 
--     spectralSequence ((filteredComplex ((res M) ** ring N)) ** (res N))

restart
needsPackage "SpectralSequences";
debug SpectralSequences;
R = QQ[x,y,z]
M = R^1/ideal(vars R)
F = res M
G = res ideal(x*y,y*z,z^3)

-- Example of spectral sequence for Ext
H = Hom(F,filteredComplex G)
E = prune spectralSequence H

 E^0
E^1
E^2
E^infinity

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
K = H ** G
see (K = H ** G)
E = prune spectralSequence K
netList apply(lim, k -> prune Tor_k(M,pushForward(map(S,R),N)))

E^0
E^1
E^2


netList support E_0
netList support E_1
netList support E_infinity


