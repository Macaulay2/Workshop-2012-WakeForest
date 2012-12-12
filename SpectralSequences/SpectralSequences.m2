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
  Version => "0.5",
  Date => "11 October 2012",
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
      Email => "nathangrieve@mast.queensu.ca",
      HomePage => "http://www.mast.queensu.ca/~nathangrieve"},             
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
  "see", 
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
  "pprune",
  "epqrMaps",
  "pruneEpqrMaps",
  "epq"
  }


protect inducedMaps
needsPackage "SimplicialComplexes"
needsPackage "ChainComplexExtras"

--------------------------------------------------------------------------------


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

zpq:= (K,p,q,r)->(
ker inducedMap((K_infinity)_(p+q-1) / K_(p-r) _ (p+q-1), 
     K_p _ (p+q), K_(infinity).dd_(p+q))
     )



bpq:= (K,p,q,r) ->(
    ( image (K_(p+r-1).dd_(p+q+1))) + (K_(p-1) _ (p+q))
      )

-- the following will compute the pq modules on the rth page explicitly.
epq = method()
epq(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r)->(  ((zpq(K,p,q,r)+bpq(K,p,q,r)) / bpq(K,p,q,r)) )


-- the following computes all modules on the r-th page.

computeErModules = method()

computeErModules(FilteredComplex,ZZ):= (K,r) -> (myList:={};
     for p from min K to max K do (
	  for q from -p + min K_(infinity) to max K_(infinity) do (--length K_(max K) do (
	       myList=append(myList, {p,q}=> epq(K,p,q,r)); )
	       	    );
	       new HashTable from myList
      )

-- the following will compute the pq maps on the rth page explicitly.
epqrMaps = method()
epqrMaps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> (
     inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r),(K_infinity).dd_(p+q)))

-- the following will prune the pq maps on the rth page explicitly. --
pruneEpqrMaps = method()
pruneEpqrMaps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> ( 
     d := epqrMaps(K,p,q,r);
     N := minimalPresentation(source d);
     M := minimalPresentation(target d);
    inverse(M.cache.pruningMap)* d * (N.cache.pruningMap) 
     )
---
ErMaps = method(Options =>{Prune => false})


ErMaps(FilteredComplex,ZZ,ZZ,ZZ):= Matrix => opts -> (K,p,q,r) -> (if opts.Prune == false then
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
inducedMap(source (E^(r+1) .dd_{p,q}),rpqHomology(E,p,q,r), id_(E^(r+1) .filteredComplex _infinity _(p+q)))
  ) 


SpectralSequencePageMap = new Type of HashTable
SpectralSequencePageMap.synonym = "spectral sequence page map"

-- spots might need to be improved.  This will work for now.
spots SpectralSequencePageMap := List => (cacheValue symbol spots)(
  K ->  select(keys K, i -> class i === List))


spectralSequencePageMap = method(Options =>{Prune => false})

spectralSequencePageMap(FilteredComplex,ZZ):= SpectralSequencePageMap => opts ->
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
	            epqrMaps(d.filteredComplex,i#0,i#1,- d.degree #1) 
     	       else
	       	    pruneEpqrMaps(d.filteredComplex,i#0,i#1,- d.degree #1) 	       	    		    
		    )

SpectralSequencePageMap ^ List := Module => (d,i)-> (d_(-i))    

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
      symbol zero => (ring K_infinity)^0})

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

-- the following is an experimental net for a spectral sequence page.
-- for now we view the coordinates in the box.  Perhaps this is what 
-- we want to do...  for example if the box is too large to fit on a screen it
-- will be annoying to try to search for a coordinate axis...
net SpectralSequencePage:= E->(L:=select(keys E.dd, i-> class i === List 
	  and E_i !=0);
maxQ:= max(apply(L, i->i#1)); minQ:=min(apply(L, i-> i#1)); 
maxP:=max(apply(L, i->i#0)); minP:= min(apply(L,i->i#0));
K:=  while maxQ>= minQ list testRow(maxP,minP, maxQ, E) do maxQ=maxQ-1;
netList K)

testRow=method()
testRow(ZZ,ZZ,ZZ,SpectralSequencePage):=(maxP,minP,q,E)->(L:={};
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

--method (Options =>{Prune => false})
--SpectralSequencePage => opts ->  (K,r)
spectralSequence = method (Options =>{Prune => false})
spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
     new SpectralSequence from {
	  symbol filteredComplex => K,
	  symbol zero => K.zero,
	  symbol cache => CacheTable,
     	  symbol Prune => opts.Prune}
     )

-- In the following we are using the rule 
-- if r> max K - min K then E^r_{p,q}=E^r'_{p,q} for all r'>=r.
SpectralSequence ^ InfiniteNumber:=
  SpectralSequence ^ ZZ := SpectralSequencePage => (E,r) -> (
       if E#?r then E#r else 
       (if r> (max E.filteredComplex) - (min E.filteredComplex) then
	    E#r= spectralSequencePage(E.filteredComplex,(max E.filteredComplex) 
		 - (min E.filteredComplex), Prune => E.Prune)
	    else
       E#r = spectralSequencePage(E.filteredComplex,r, Prune => E.Prune);); 
       E#r
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
-- or the truncated complex with image d_{p+1} in degree p and zero in degrees <p ??

-- the following method truncates a chain complex 
truncate (ChainComplex,ZZ):= (C,q) ->( 
     if q == 0 then return C 
     else (
	  m:= min support C;
	  n:=max support C;
	  l:=length C;
	  if q < -l or q > l then return image(0*id_C)
	  else  K:=new ChainComplex;
	        K.ring=C.ring;
	  	if q < 0 then for i from min C + 1 to max C do (
	             if i <= n + q then K.dd_i=C.dd_i 
	       	     else if i-1 > n + q then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
	       	     else K.dd_i = inducedMap(C_(i-1), 0*C_i, C.dd_i) ) 
	  	else for i from min C+1  to max C do (
	       	     if i-1 >= q + m then K.dd_i=C.dd_i 
	       	     else if i < q + m then K.dd_i=inducedMap(0*C_(i-1),0*C_i,C.dd_i)
	       	     else K.dd_i=map(0*C_(i-1), C_i, 0*C.dd_i) )); 
     K)



-- make the filtered complex associated to the "naive truncation of a chain complex"
filteredComplex ChainComplex := FilteredComplex => opts-> C->( complete C; 
     	       n := max support C;
     	       m := min support C;
     	       H := for i from 1 to length C list inducedMap(C,truncate(C,-i));
     	      filteredComplex(H,Shift => -m))


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
     H:= Hom(C,K_infinity);
     filteredComplex(reverse for i from P to (N -1) list 
	       inducedMap(H, complex(H,i)), Shift => -P)
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

-- the following method seems to work ok, although need to test more
-- carefully.
Hom(Matrix, Module) := Matrix => (f,N) -> (
     g := (f * id_(source f)) // id_(target f);
     inducedMap(image id_(Hom(source f, N)),image id_(Hom(target f, N)), 
	       cover((transpose cover g) ** (id_(N))))
)


-- the following method seems to work ok, athough need to test
-- more carefully.
Hom(Module, Matrix) := Matrix => (N,f) -> (inducedMap(Hom(N,target f),
	  Hom(N,source f),   dual id_(cover N) ** f))


-- there is/was a bug in cover chain complex -- 
-- need to test more carefully. --     
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



project := (K,p) -> (
     f:= i -> map(K_p_i,K_infinity_i,1);
     map(K_p,K_infinity,f)
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


  
--FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
--  all(min(min C,min D)..max(max C,max D),i-> C_i == D_i))




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


--load "Doc/SpectralSequencesDoc.m2"
--load "Doc/TestSpectralSequencesDoc.m2"

beginDocumentation()

doc ///
     Key 
          SpectralSequences
     Headline 
         a package for working with spectral sequences associated to filtered complexes,
    Description
    	 Text 
              SpectralSequences is a package to work with spectral sequences
	      associated to a filtered complex.  Here are some examples illustrating 
	      this package.
	      
     	      @TO"Computing the Serre Spectral Sequence associated to a Hopf Fibration"@
	      
	      @TO "Balancing Tor"@
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
		    apply(spots E0page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
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
		    apply(spots E1page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,1))
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
		    apply(spots E1page.dd, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,3))
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
	       The SpectralSequences package provides effective computation of spectral sequences
	       associated to separated and exhaustive filtrations of a chain complex.	    
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
     	  Making filtered complexes and spectral sequences from simplicial complexes
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
	       F = minimalPresentation(E^infinity)
	       E^infinity .dd	            
	       F.dd
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
     	  Making filtered complexes and spectral sequences from chain complexes.
     Description
     	  Text
///	  	  
doc ///
     Key
        "filtered complexes and spectral sequences from chain complex maps"
     Headline
     	  Making filtered complexes and spectral sequences from chain complex maps	
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
     	 Making filtered complexes and spectral sequences from tesor products 	
     Description
     	  Text
///	  

doc ///
     Key
        "filtered complexes from Hom"
     Headline
     	 Making filtered complexes and spectral sequences from Hom
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
     	  Construct a spectralSequence from a filtered complex
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
     	  The ith inclusion map in a filtered complex
     Usage
     	  f = Hom(K,C)
     Inputs
     	  K:FilteredComplex
	  C:ChainComplex
     Outputs
     	  f:FilteredComplex
     Description
     	  Text 
	       Blah
    ///
    doc ///
     Key
     	   (chainComplex, SpectralSequence)
     Headline
     	  The underlying chain complex of a Spectral Sequence
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
     	  Construct a SpectralPage from a filtered complex
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
	       Blah
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
     	  The kth page of a spectral sequence
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
     	  (symbol ^, SpectralSequence, ZZ)
	  (symbol ^, SpectralSequence, InfiniteNumber)
     Headline
     	  The kth page of a spectral sequence
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
     	  The module in the i,j position on the page
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
	       Returns the module in the \{i,j\}  \ position in the spectral sequence page. 
	       (Using cohomological indexing conventions.)  
    ///

doc ///
     Key
     	  (symbol _, SpectralSequencePage, List)
	  
     Headline
     	  The module in the i,j position on the page
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
	       Blah
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
     	  The filtered pieces
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
     	  The filtered pieces
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
    
      
end

--- here is another topological example.
restart
installPackage"SpectralSequences"
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"


-- trying to give a combinatorial picture of the quotient map
-- SS^2 --> RR PP^2, given by indentifying anti-podal points.

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
F0twoSphere = simplicialComplex {v1*v3,v5*v6, v4*v2, v36*v15, v34*v12, v46*v25}

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
E = prune spectralSequence K
E^0
E^0 .dd
ker E^0 .dd_{0,0}
E^0
E^1
E^0 .dd
prune ker E^0 .dd_{0,0}
image E^0 .dd_{0,1}
help epq
prune epq(K,0,0,1)

-- note that there seems to be an error.  There is no way that E^1_{0,0} should be
-- ZZ^6.
E^1 .dd
E^2
E^2 .dd

-- try to investigate the bug.
-- this is the source code.

zpq:= (K,p,q,r)->(
ker inducedMap((K_infinity)_(p+q-1) / K_(p-r) _ (p+q-1), 
     K_p _ (p+q), K_(infinity).dd_(p+q))
     )

bpq:= (K,p,q,r) ->(
    ( image (K_(p+r-1).dd_(p+q+1))) + (K_(p-1) _ (p+q))
      )


-- the following will compute the pq modules on the rth page explicitly.
Myepq = method()
Myepq(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r)->(  ((zpq(K,p,q,r)+bpq(K,p,q,r)) / bpq(K,p,q,r)) )

prune zpq(K,0,0,1)

prune bpq(K,0,0,1)
-- the problem seems to be bpq.
-- investigate more.
prune image(K_0 .dd_(1))

K_0
K

(K_0).dd

source (K_0).dd_1
target (K_0).dd_1
prune image (K_0).dd_1
-- so here's a question:  How can a map with zero source have a non-zero image?!
-- so there seems to be a bug somewhere.
ker (K_0).dd_1

needsPackage "ChainComplexExtras"
isChainComplex K_0

-----
------

--
--
-- The following two examples are filtrations arising from topological fibrations.
restart
installPackage"SpectralSequences"
needsPackage"SpectralSequences"
needsPackage"SimplicialComplexes"


-- trying to compute spectral sequences associated to the fibration
-- Klien Bottle --> SS^1 with fiber SS^1.
-- This fibration was trianulated by hand.

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

Delta = simplicialComplex {f1,f2,f3,f4,f5,f6,f7,f8,f9,
     f10,f11,f12,f13,f14,f15,f16,f17,f18}
C = truncate(chainComplex Delta,1)
prune HH C
-- so the homology of C aggrees with the homology of the Klien Bottle.

F1Delta = Delta

-- now want to make subsimplicial complex arising from the filtrations of the
-- inverse image of the verticies

F0Delta = simplicialComplex {a00*a01,a01*a02
     ,a00*a02,a10*a11,a10*a12,a11*a12,a21*a20,a20*a22,a21*a22}

K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false)

E = prune spectralSequence K
E^0
E^0 .dd
E^1
E^1 .dd
E^2
prune HH C
E^2 .dd

-- A key feature of this example (as illustrated by the E^2 page of the spectral
-- sequence) is that the fundamental group of the base (in this case SS^1) does
-- not act trivially on the fiber.  If it did, then the E^2 page
-- would have E^2_{p,q} = HH_p(F,HH_q(B;ZZ).

-- Now let's try the trivial fibration SS^1 x SS^1 --> SS^1, where
-- the map is given by one of the projections.
-- This fibration was also trianulated by hand.
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
-- note it is important to use the reduced homology option!! 
K = filteredComplex({F1Delta, F0Delta}, ReducedHomology => false) 
K_infinity == C
needsPackage "ChainComplexExtras"
isChainComplexMap(inducedMap(K_infinity, K_0))

E = prune spectralSequence K
E^0
prune coker E^0 .dd_{0,0}
prune coker E^0 .dd_{0,0}
prune image E^0 .dd_{0,1}
prune ker E^0 .dd_{0,0}

prune ker E^0 .dd_{1,0}
prune coker E^0 .dd_{1,1}
E^1

E^0_{-1,1}
E^0 .dd
E^1
E^1 .dd

prune coker E^1 .dd_{1,0} 
pruneEpqrMaps(K,1,0,1)
prune ker epqrMaps(K,1,0,1)

E^2
E^2 _{-1,1}
E^2 _{1,-1}
prune E^2 _{0,0}
E^2 .dd


--------------------------------------------------------------------------------
restart
installPackage"SpectralSequences"
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
viewHelp SpectralSequences
------------------------------------------
--------------

-- trying to do an example from the paper "A case study in 
-- bigraded commutative algebra" by C-D-S.
-- an appropriate term on the E2 page will correspond to non-koszul syzygies.

---
--
restart
needsPackage "SpectralSequences"
R = QQ[x,y,z,w, Degrees => {{1,0},{1,0},{1,1},{1,1}}]
S =QQ[a,b,c,d, Degrees => {{1,0},{1,0},{0,1},{0,1}}]
B = ideal(x*z, x*w, y*z, y*w)

help basis
basis({1,1},R)

p_0 = x^2*z
p_1 = y^2*w
p_2 = y^2*z+x^2*w


I = ideal(p_0,p_1,p_2)

m := n -> matrix(R,{{(x*z)^n,(x* w)^n,(y*z)^n,(y*w)^n}})
-- in the following we will need to take n large enough.  An
-- actual value seems to be contained in theorem 0.2 p. 585 of E-M-S.

-- the following complex is the cech like complex that we want to use.
K = truncate(Hom(koszul m 6, R^1),-1)
Hom(koszul m 6, R^1)

K

K.dd
-- so things seem to be multigraded correctly.
C = koszul matrix(R,{{p_0,p_1,p_2}})
C^(-3)
Hom(C,R^1)
Hom(K,C)
Hom(C,K)
C.dd
-- so things seems to be mutigraded correctly.

prune HH K
prune ker K.dd_(-1)
prune ker K.dd_(-1)

T = K ** (C);

F = K ** filteredComplex C
e = prune spectralSequence F
e^0
e^1
e^2
K
C

F = filteredComplex K

e = prune spectralSequence(F ** C)
e^0
e^1
e^2
f = filteredComplex C
K

ee = prune spectralSequence(K ** f)
ee^0
ee^1
ee^2

image id_C


E = prune spectralSequence (filteredComplex K ** C)
E^0
E^1
E^2

E = prune spectralSequence (K ** filteredComplex(C))
E^0
E^1
E^2

prune HH T
-- to get the term on the E2 page which has the non-koszul syzygies
-- need to use the "right filtration" -- that is the filtration with respect to 
-- y coordinate.

filteredComplex complete C
complete C
K


myFilt = K ** (filteredComplex (image id_C))

eee = prune spectralSequence myFilt
eee^0
eee^1
eee^2

Filt = filteredComplex K ** ((image id_C))
eeee = prune spectralSequence Filt
eeee^0
eeee^1
eeee^2
K

K.dd

E = prune spectralSequence myFilt

E^0
E^1
K

-- check out the top row of the E^1 page.  this looks like it is suppose too.

-- E^1_{p,q} module is supposed to equal HH_q(K ** C_p).
-- we can check this explicitly as 
--follows.

all(keys (support E^1), i -> E^1 _{i#0,i#1} == (prune HH_(i#1)(K ** C_(i#0))))
-- so this looks promising.

E^2

time E^3
-- The E^2_{3,-2} term is what we want to find the non-koszul syzygies.

E^2_{3,-2}

D = res I
D_2
-- so the non-koszul szygies are generated in degrees {5,3} and {7,1} --
E^2 .dd_{3,-2}
-- note that this map is an isomorphism.
prune ker E^2 .dd_{3,-2}
prune image E^2 .dd_{3,-2}

image E^2 .dd_{3,-2} == E^2_{1,-1}
E^3

-- in the above, we might want to twist the complex and take the degree zero pieces.

-- so I think that the above is working as it should.

-- note that we used m 6 in the above.

-- let's see what happens if we try to use smaller values.


(prune spectralSequence(filteredComplex(truncate(Hom(koszul m 6, R^1),-1) ** C,
	   Right => true)))^2 _{3,-2}

for i from 1 to 6 list (prune spectralSequence(filteredComplex(truncate(Hom(koszul m i, R^1),-1) ** C,
	   Right => true)))^2 _{3,-2}
-- so it appears that l >= 2 works in this example.

for i from 1 to 6 list (prune spectralSequence(filteredComplex(truncate(Hom(koszul m i, R^1),-1) ** C,
	   Right => true)))^3 _{3,-2}
-- it also appears that l = 1 works to compute the corresponding term on the E_3 page
-- correctly.

myFilt = filteredComplex(truncate(Hom(koszul m 2, R^1),-1) ** C, Right => true);

prune epq(myFilt,3,-2,2)

-- lets compare the various ways we have to filtered the tensor product complex.

mygens = m 2

benchmark "filteredComplex(truncate(Hom(koszul mygens, R^1),-1) ** C, Right => true)"
-- returned .454884454545454
benchmark "truncate(Hom(koszul mygens, R^1),-1) ** (filteredComplex C)"
-- returned .658425714285715
benchmark "filteredComplex(truncate(Hom(koszul mygens, R^1),-1) ** C, Left => true)"
-- returned .446655599999997
benchmark "filteredComplex truncate(Hom(koszul mygens, R^1),-1) **  C"
-- returned .880638000000005


---
--trying to see which way of filtering the total complex
-- associated to tensor product of two complexes is faster.
---

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[x,y,z,w]

C = koszul vars A
D = complete res monomialCurveIdeal(A,{1,3,4})

K = C ** D;

benchmark "filteredComplex(K,Left => true)"
-- returned .262378818181818

benchmark "filteredComplex(K,Right => true)"
-- returned .197785133333333

benchmark "(filteredComplex(C) ** D)"
-- returned .790209333333335

benchmark "(C ** filteredComplex(D))"
-- returned .641419750000001

-- so I think that the above examples show that we might want to filter
-- using the components directly...

---------
---------
-- try to test the tensor product code.
-- perhaps the bugs are now out.  need to try the hom filtrations again later.
--
------------

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[x,y,z]
B = A^1 / ideal(x^3+y^3+z^3)
-- B is the homogeneous coordinate ring of an elliptic curve

m := n -> image matrix(A,{{x^n,y^n,z^n}})

I := n -> res (m n)


F = complete res B
G = complete I 1
prune Hom(G,A^1)
C = Hom(G,A^1) ** F

K = filteredComplex(C,Left => true)
KK = filteredComplex(Hom(G,A^1)) ** F

E = prune spectralSequence K
EE = prune spectralSequence KK

E^0
EE^0
E^1
EE^1
E^2
EE^2

E^3
EE^3

K = filteredComplex(C,Right => true)
KK = Hom(G,A^1) ** filteredComplex F
E = prune spectralSequence K
EE = prune spectralSequence KK
E^0
EE^0
E^1
EE^1
E^2
EE^2
E^infinity
EE^infinity

prune HH C
-- so the above seem to be working OK.

C = Hom(G,F)

--K = filteredComplex(C, symbol Hom => true, Left => true)

K = Hom(filteredComplex G,F)
prune K
E = prune spectralSequence K
E^0
E^1
E^2

--k = filteredComplex(C, symbol Hom => true, Right => true)

k = Hom(G,filteredComplex F)
prune k
E = prune spectralSequence k
E^0
E^1
E^2


C = Hom(G,Hom(G,G))
--K = filteredComplex(C, symbol Hom => true, Left => true);

K = Hom(G,filteredComplex Hom(G,G))
prune K
--kk = filteredComplex(C, symbol Hom => true, Right => true);

kk = Hom(filteredComplex G,Hom(G,G));


prune kk
prune K
E = prune spectralSequence K
E^0
E^0 _{3,-2}
E^1
E^2
E^3
E^infinity
ee = prune spectralSequence kk
ee^0
ee^1
ee^2
ee^infinity
-- so this seems to suggest that both filtrations are implemented.


---------------


-- since important code has changed, let's make sure we can still compute
-- the hopf fibration correctly.

restart
installPackage"SpectralSequences"
needsPackage "SpectralSequences"
needsPackage "SimplicialComplexes"
B=QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2]
		    l1={a_0*b_0*b_1*c_1,a_0*b_0*c_0*c_1,a_0*a_1*b_1*c_1,b_0*b_1*c_1*d_1,b_0*c_0*c_1*d_2,a_0*a_1*c_1*d_2,a_0*c_0*c_1*d_2,b_0*c_1*d_1*d_2};
		    l2={b_1*c_1*c_2*a_2,b_1*c_1*a_1*a_2,b_1*b_2*c_2*a_2,c_1*c_2*a_2*d_1,c_1*a_1*a_2*d_2,b_1*b_2*a_2*d_2,b_1*a_1*a_2*d_2,c_1*a_2*d_1*d_2};
		    l3={c_2*a_2*a_0*b_0,c_2*a_2*b_2*b_0,c_2*c_0*a_0*b_0,a_2*a_0*b_0*d_1,a_2*b_2*b_0*d_2,c_2*c_0*b_0*d_2,c_2*b_2*b_0*d_2,a_2*b_0*d_1*d_2};
		    l4={a_0*b_0*b_1*d_1,a_0*b_1*d_0*d_1,b_1*c_1*c_2*d_1,b_1*c_2*d_0*d_1,a_0*a_2*c_2*d_1,a_0*c_2*d_0*d_1};
		    l5={a_0*b_1*d_0*d_2,a_0*a_1*b_1*d_2,b_1*c_2*d_0*d_2,b_1*b_2*c_2*d_2,a_0*c_2*d_0*d_2,a_0*c_0*c_2*d_2};
		    D=simplicialComplex(join(l1,l2,l3,l4,l5));
		    
		    f1l1 = {a_0*b_0*b_1,a_0*a_1*b_1,a_0*c_0*c_1,a_0*a_1*c_1,a_0*a_1*d_2,d_1*d_2,b_0*b_1*c_1,b_0*c_0*c_1,b_0*b_1*d_1,b_0*d_1*d_2,c_1*d_1*d_2,c_0*c_1*d_2};
		    f1l2 = {b_1*a_1*a_2,b_1*b_2*a_2,c_1*c_2*a_2,c_1*a_1*a_2,a_1*a_2*d_2,a_2*d_1*d_2,b_1*c_1*c_2,b_1*b_2*c_2,b_1*b_2*d_2,d_1*d_2,c_1*d_1*d_2,c_1*c_2*d_1};
		    f1l3 = {a_2*a_0*b_0,a_2*b_2*b_0, c_2*a_2*a_0,c_2*c_0*a_0,a_2*a_0*d_1,a_2*d_1*d_2,b_2*b_0*c_2,c_2*c_0*b_0,b_2*b_0*d_2,b_0*d_1*d_2,c_2*c_0*d_2,d_1*d_2};
		    f1l4 = {a_0*b_0*b_1,a_0*a_2,a_0*a_2*c_2,c_1*c_2,a_0*d_0*d_1,a_0*a_2*d_1,b_1*c_1*c_2,b_0*b_1,b_0*b_1*d_1,b_1*d_0*d_1,c_1*c_2*d_1,c_2*d_0*d_1}
		    f1l5 = {a_0*a_1*b_1,b_1*b_2,a_0*c_0*c_2,a_0*a_1,a_0*d_0*d_2,a_0*a_1*d_2,b_1*b_2*c_2,c_0*c_2,b_1*d_0*d_2,b_1*b_2*d_2,c_2*d_0*d_2,c_0*c_2*d_2};
		    F1D = simplicialComplex(join(f1l1,f1l2,f1l3,f1l4,f1l5));
		    
		     f0l1={a_0*a_1,b_0*b_1,c_0*c_1,d_1*d_2};
		    f0l2={a_1*a_2,b_1*b_2,c_1*c_2,d_1*d_2};
		    f0l3={a_0*a_2,b_0*b_2,c_0*c_2,d_1*d_2};
		    f0l4={a_0*a_2,b_0*b_1,c_1*c_2,d_0*d_1};
		    f0l5={a_0*a_1,b_1*b_2,c_0*c_2,d_0*d_2};
		    F0D=simplicialComplex(join(f0l1,f0l2,f0l3,f0l4,f0l5)); 
		    
		    K=filteredComplex({D,F1D,F0D},ReducedHomology => false)
E = spectralSequence K		    
E^0		    
E^1
E^2

E = prune spectralSequence K		    
E^0
E^1
E^2
E^3

-- so at least the Hopf Fibration example shows that the present code is working



-------------------------------------------------------------------
-- The bugs in computing the following example seem
-- to be fixed.  
-- the apparent fix for this example caused errors elsewhere.
-- need to check that other previously computed examples still work.
-- (At least the example runs OK.)
-- (Still needs to check the hom filtrations more carefully.  
-- at the very least they are producing examples of filtered
-- complexes which seem to have exposed some bugs.)

-----
-- this next example shows that there is a bug in the code.
-- I think it has to do with zero...
--

installPackage"SpectralSequences"
installPackage("SpectralSequences",RemakeAllDocumentation=>true)

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[x,y,z]
B = A^1 / ideal(x^3+y^3+z^3)
-- B is the homogeneous coordinate ring of an elliptic curve

m := n -> image matrix(A,{{x^n,y^n,z^n}})

I := n -> res (m n)


F = complete res B
G = complete I 1

C = Hom(G,F)

Hom(I 1, res B)
-- OK, so we need to complete the complexes first...


D = filteredComplex(C,symbol Hom => true, Left => true);

E = prune spectralSequence D
E^0
E^1
E^2

prune filteredComplex(C,symbol Hom => true, Right => true)
prune D
-- now I have doubts about the Hom filtrations...
-- need to check this more carefully
-- there appears to be a bug in the spectral sequence code.  It's also
-- possible that it is in the Hom filtration code...
E^0
E^1
E^2
E^3
E^infinity

pruneEpqrMaps(D,0,-2,1)
pruneEpqrMaps(D,1,-2,1)
pruneEpqrMaps(D,1,-1,1)
pruneEpqrMaps(D,0,-1,1)
pruneEpqrMaps(D,1,0,1)
pruneEpqrMaps(D,0,0,1)
maps = method()

maps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> (
inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r), cover id_(K_(p-r) _(p+q-1)) * cover (K_infinity).dd_(p+q))
)

cover id_(D_(0) _(-2))
D
prune D
id_(D_(0) _(-2)) * D_infinity .dd_(-1)

maps(D,1,-2,1)

E^0
pruneEpqrMaps(D,0,-2,2)
pruneEpqrMaps(D,1,-2,2)
pruneEpqrMaps(D,1,-1,2)
pruneEpqrMaps(D,0,-1,2)
pruneEpqrMaps(D,1,0,2)
pruneEpqrMaps(D,0,0,2)

 epqrMaps(D,i#0,i#1,2)

#(keys computeErModules(D,2))
L = (keys computeErModules(D,2))
epqrMaps(D,(L#0)#0,(L#0)#1,2)
epqrMaps(D,3,-3,2)
epq(D,3,-3,2)
epq(D,1,-2,2)

inducedMap(epq(D,1,-2,2),epq(D,3,-3,2), D_1 .dd_0)
-- note that this worked.

apply(keys computeErModules(D,2), i -> epqrMaps(D,i#0,i#1,2))



max D_infinity
help epqrMaps
epqrMaps(D,0,0,0)
pruneEpqrMaps(D,0,0,0)
pruneEpqrMaps(D,1,0,0)
pruneEpqrMaps(D,0,-1,0)
pruneEpqrMaps(D,1,-1,0)
prune source epqrMaps(D,1,-1,0)
prune target epqrMaps(D,1,-1,0)
prune epq(D,1,0,0)
prune epq(D,0,-2,0)
E^0_{1,0}
E^0_{0,-2}

prune source epqrMaps(D,1,0,0)
C_0
C_(-1)


f = inducedMap(epq(D,1,-2,0), epq(D,1,-1,0),(D_infinity).dd_0)
prune source f
prune target f
D_infinity

computeErModules(D,0)
apply(keys computeErModules(D,0), i-> (prune (computeErModules(D,0))#i))
apply(keys computeErModules(D,0), i -> prune source epqrMaps(D,i#0,i#1,0))

apply(keys computeErModules(D,0), i -> prune target epqrMaps(D,i#0,i#1,0))

apply(keys computeErModules(D,0), i-> (prune (computeErModules(D,1))#i))
keys computeErModules(D,1)
(prune E)^0

apply(keys computeErModules(D,0), i-> (prune (computeErModules(D,2))#i))
apply(keys computeErModules(D,2), i -> prune source epqrMaps(D,i#0,i#1,2))

-- The following shows that there 
-- is a problem somewhere... 
-- note there seems to be a bug somewhere...  the bug seems to
-- be in eprMaps.

epqrMaps(D,1,-2,1)

epq(D,1,-2,1)

epq(D,0,-2,1)

cover C.dd_(-1)
inducedMap(epq(D,0,-2,2),epq(D,1,-2,2),cover K_(1).dd_(-1))
-- note that this seemed to work ok. --
-- need to investigate this further.
epqrMaps(D,0,-2,1)
epqrMaps(D,1,-1,1)
epqrMaps(D,0,-1,1)
epqrMaps(D,1,0,1)
epqrMaps(D,0,0,1)

EE = spectralSequence D
EE^0
EE^1

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
--needsPackage "ChainComplexExtras";
debug SpectralSequences;



A = QQ[x,y,z]
B = A^1 / ideal(x^3+y^3+z^3)
-- B is the homogeneous coordinate ring of an elliptic curve

m := n -> image matrix(A,{{x^n,y^n,z^n}})

I := n -> res (m n)

K =  Hom(I 1, B)

prune HH K

H1B = HH_(-1) K
H0B = HH_0 K
H2B = HH_(-2) K

basis(0,H0B)
basis(0,H1B)
basis(0,H2B)

basis(0, Ext^0(m 1, B))
basis(0, Ext^1(m 1, B))
basis(0, Ext^2(m 1, B))

-- observe that the above agrees with the cohomology of the structure sheaf
-- of an elliptic curve as it should.  Also observe that we needed k = 1 here.
-- the resolution of the structure sheaf has the shape 
--  0 --> OO(-3) --> OO --> OO_X -->0 which gives at least one explanation.

F = complete res B
G = complete I 1

C = Hom(G,F)

Hom(I 1, res B)
-- OK, so we need to complete the complexes first...

prune HH C
-- note this aggrees with earlier stuff.

E = prune spectralSequence(filteredComplex(C,symbol Hom => true, Left => true))

D = filteredComplex(C,symbol Hom => true, Left => true);
E = prune spectralSequence D
max D
min D
prune filteredComplex(C,symbol Hom => true, Right => true)
prune D
-- now I have doubts about the Hom filtrations...

E^0
E^1
help epqrMaps
epqrMaps(D,0,0,0)
pruneEpqrMaps(D,0,0,0)
pruneEpqrMaps(D,1,0,0)
pruneEpqrMaps(D,0,-1,0)
pruneEpqrMaps(D,1,-1,0)
prune source epqrMaps(D,1,-1,0)
prune target epqrMaps(D,1,-1,0)
epqr(D,1,0,0)
-- note there seems to be a bug somewhere...  perhaps in the net??
computeErModules(D,0)
apply(keys computeErModules(D,0), i-> (prune (computeErModules(D,0))#i))
apply(keys computeErModules(D,0), i -> prune source epqrMaps(D,i#0,i#1,0))
apply(keys computeErModules(D,0), i -> prune target epqrMaps(D,i#0,i#1,0))
-- so this shows that one of the induced maps is not working correctly!! --

EE = spectralSequence D
EE^0
EE^1



E^1
-- note that the above shows that there is a bug in the above.
epqrMaps(D,0,0,1)
epqrMaps(D,1,0,1)
epqrMaps(D,0,-1,1)
epqrMaps(D,1,-1,1)
-- note that the target of this map 


computeErModules(filteredComplex(C,symbol Hom => true, Left => true),1)

-- note there is a bug ...
-- need to investigate this more.
computeErModules(filteredComplex(C,symbol Hom => true, Left => true),1)

-- observe that there are lots of zero modules which are not explicitly sub-quotients
-- of anything...  Presumably this is what's causing the problem.
--------------
---
-- some examples to try and test the filtratins of tensor product and hom implementation

A = QQ[a,b,c,d]

C = koszul vars A

D = res monomialCurveIdeal(A,{1,3,4})

T = C ** D;

-- filter with respect to x coord
filteredComplex(T, Left => true)
-- filter with respect to y coord
filteredComplex(T, Right => true)

K = Hom(C,D)
-- filter with respect to x coord
filteredComplex(K, symbol Hom => true, Left => true)
-- filter with respect to y coord
filteredComplex(K, symbol Hom => true, Right => true)

-- need to test the above further

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[a,b,c,d]
D = simplicialComplex {a*d*c, a*b, a*c, b*c}
F2D = D
F1D = simplicialComplex {a*c, d}
F0D = simplicialComplex {a,d}
K = filteredComplex({F2D, F1D, F0D}, ReducedHomology => false)

prune Hom(K_infinity,K_1)
prune Hom(K_1,K_infinity)
prune Hom(K_infinity, K_(-2))
prune Hom(K_1,K_infinity)


Hom(K,K_1)

C = K_1
Hom(filteredComplex C, C)
K ** K_1
K_1 ** K
Hom(K,K_1)
Hom(K_1,K)
min K
max K





-- so there still seems to be a bug.
myHom = method()
myHom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
--filteredComplex for p from min K to max K list Hom(project(K,p),C)
 new FilteredComplex from (for p from min K to max K list p => (Hom(K_p,C)  )) | {symbol zero => image (0*id_(Hom(K_infinity,C))), symbol cache =>  new CacheTable}
--filteredComplex ( (for p from min K to (max K)-1 list 
--	  inducedMap (Hom(K_(-infinity),C), Hom(K_p,C))
--	  	       )),Shift =>(- min K) 
)

myHom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
     F := (f,D) -> inducedMap(Hom(target f,D), Hom(image f, D));
filteredComplex (reverse (for p from min K to (max K)-1 list 
	  F(inducedMap(K,p),C)),Shift =>(- min K) )
)

KK = myHom(K,K_1)
apply(spots KK, i-> inducedMap(KK,i))
inducedMap(KK,2)
inducedMap(KK,1)

image inducedMap(K,1)
c = Hom(image inducedMap(K,1),C)
d = Hom(image inducedMap(K,2),C)
inducedMap(d,c)
apply (spots d, i-> inducedMap(d_i,c_i, id_(d_i)))
spots d
inducedMap(d_(-3),c_(-3), id_(d_(-3)))
d_(-3)
c_(-3)
cover c_(-3)
prune d_(-3)
-- so there is at least one source of trouble.
-- is this a problem with inducedMap(Module,Module)??  or with
-- chain complexes??  is c_(-3) supposed to be a subquotient of QQ^1??
inducedMap(d_(-2),c_(-2), id_(d_(-2)))
d_(-2)
c_(-2)
prune K
prune C
-- need to think about this example more carefully.


spots Hom(image inducedMap(K,2),C)
image myHom(inducedMap(K,2),C)
K_1
K_2
C


KK_1
KK_2
help inducedMap
KK = myHom(filteredComplex C, C)
inducedMap(KK,0)
inducedMap(KK,2)
inducedMap(KK,1)
inducedMap(KK,-1)
KK
prune KK
project(K,1)
inducedMap(Hom(K_(-infinity),C),Hom(K_2,C))
C
prune image Hom(inducedMap(K,2),C)
prune image Hom(inducedMap(K,1),C)


inducedMap(Hom(K_2,C),Hom(K_2,C))
Hom(K_(-1),C)
C = K_1

 for p from min K to (max K) list 
	   (prune image Hom(inducedMap(K,p),C))
target inducedMap(K,1)
Hom(K_1,C) == target Hom(inducedMap(K,1),C)

prune Hom(K_(-infinity),C)
inducedMap(Hom(K_(-infinity), C), Hom(K_1,C))


Hom (ChainComplexMap, ChainComplex) := ChainComplexMap => (f,C) -> (
  (F,G) := (Hom(target f, C),Hom(source f, C));
  map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
        (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
	  F#i.cache.components#(F#i.cache.indexComponents#k),
	  if j === k then Hom(f_(j#0), C_(j#1)) 
	  else 0)))))


Hom(K_1,K)

Hom(K_(-3),K)
-- this one needs to be rewritten.  There is a bug in it.

-- there is a bug in this one.
Hom (ChainComplex, FilteredComplex):= FilteredComplex => (C,K) ->(
--  filteredComplex for p from min K to max K list Hom(C,inducedMap(K,p))
-- new FilteredComplex from (for p from min K to max K list p=> (Hom(C,K_p))  ) | {symbol zero => image (0*id_(Hom(C,K_infinity))), symbol cache =>  new CacheTable}
filteredComplex (reverse (for p from min K to (max K)-1 list 
	  Hom(C,inducedMap(K,p))),Shift =>(- min K) )

)

---------------------------------
-- some examples to show Greg.

restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[a,b,c,d]
D = simplicialComplex {a*d*c, a*b, a*c, b*c}
F2D = D
F1D = simplicialComplex {a*c, d}
F0D = simplicialComplex {a,d}
K = filteredComplex({F2D, F1D, F0D}, ReducedHomology => false)
E = spectralSequence K
F = minimalPresentation E
F^0
E^0
G = minimalPresentation spectralSequence K
E^0_{100,100}
E^0
F = spectralSequence(K,Prune => true)
F^0
F^1
E^0_{-100,100}
prune E^0_{100,-100}
F^0_{100,-100}

E^0_{-1000,100}
F^0_{-1000,100}
F^1
F^2
F^infinity
E^infinity
prune F^infinity
prune E^infinity
F^3

F^2 .dd_{2,-1}
prune ker F^2 .dd_{2,-1}

prune Hom(K_infinity,K_1)
prune Hom(K_1,K_infinity)
prune Hom(K_infinity, K_(-2))
prune Hom(K_1,K_infinity)


Hom(K,K_1)
-- so there still seems to be a bug.
Hom(K_1,K)

Hom (ChainComplexMap, ChainComplex) := ChainComplexMap => (f,C) -> (
  (F,G) := (Hom(target f, C),Hom(source f, C));
  map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
        (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
	  F#i.cache.components#(F#i.cache.indexComponents#k),
	  if j === k then Hom(f_(j#0), C_(j#1)) 
	  else 0)))))


for p from min K to (max K)-1 list 
	 prune target Hom(inducedMap(K,p),K_1)


filteredComplex reverse for p from min K to (max K)-1 list 
	  Hom(inducedMap(K,p),K_1)
	  
-- so there is still a bug somewhere.
-- should try myHom and see what happens...
for p from min K to (max K)-1 list Hom(K_1, inducedMap(K,p))

filteredComplex reverse for p from min K to (max K)-1 list Hom(K_1, inducedMap(K,p))

----
----





-- some scratch code trying to get Hom(FilteredComplex,ChainComplex) working.
-- Hom(ChainComplex, FilteredComplex). )
A = QQ[x,y,z]
C = koszul matrix(A,{{x^2, x*y,z}})

D = koszul vars A

myHom = method()
myHom(ChainComplexMap, ChainComplex) := ChainComplexMap => (f,C) -> (
     inducedMap(Hom(target f, C), Hom(image f, C)) 
     )

myHom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
     F := (f,D) -> inducedMap(Hom(target f,D), Hom(image f, D));
filteredComplex (reverse (for p from min K to (max K)-1 list 
	  F(inducedMap(K,p),C)),Shift =>(- min K) )
)

Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
     F := (f,D) -> inducedMap(Hom(target f,D), Hom(image f, D));
     filteredComplex (reverse (for p from min K to (max K)-1 list 
     F(inducedMap(K,p),C)),Shift =>(- min K) )
)

Hom (ChainComplex, FilteredComplex):= FilteredComplex => (C, K) -> (
     F := (D,f) -> inducedMap(Hom(D, target f), Hom(D, image f));
filteredComplex (reverse (for p from min K to (max K)-1 list 
	  F(C,inducedMap(K,p))),Shift =>(- min K) )
)



K = filteredComplex C
Hom(K,C)
Hom(K,K_1)
K

-- I think that something like this will work.

myHom(ChainComplex, ChainComplexMap) := ChainComplexMap =>(C,f) -> (
      inducedMap(Hom(C, target f), Hom(C, image f))
     )

myHom (ChainComplex, FilteredComplex):= FilteredComplex => (C, K) -> (
     F := (D,f) -> inducedMap(Hom(D, target f), Hom(D, image f));
filteredComplex (reverse (for p from min K to (max K)-1 list 
	  F(C,inducedMap(K,p))),Shift =>(- min K) )
)

myHom(C,K)



-- so perhaps the above work ok.

-----
-- some scratch code trying to test Hom(ChainComplex,ChainComplex)
----
restart
installPackage"SpectralSequences"
installPackage("SpectralSequences",RemakeAllDocumentation=>true)

A = QQ[x,y,z]
C = koszul matrix(A,{{x^2, x*y,z}})

D = koszul vars A

Hom(C,D)
Hom(D,C)
Hom(truncate(C,-1),C)
Hom(C,truncate(C,-1))
prune Hom(C,truncate(C,-10))
prune Hom(truncate(C,-10),C)
prune Hom(truncate(C,10),C)
prune Hom(C,truncate(C,10))

-- so maybe things are OK now... 
-------------------------------------------------------------------------------
-- some scratch code trying to test some functions
---------------------------------------------------------------------------



restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A = QQ[a,b,c,d]
D = simplicialComplex {a*d*c, a*b, a*c, b*c}
F2D = D
F1D = simplicialComplex {a*c, d}
F0D = simplicialComplex {a,d}
K = filteredComplex({F2D, F1D, F0D}, ReducedHomology => false)
E = spectralSequence K
F = minimalPresentation E
F^0
E^0
G = minimalPresentation spectralSequence K
E^0_{100,100}
E^0
F = spectralSequence(K,Prune => true)
F^0
F^1
E^0_{-100,100}
prune E^0_{100,-100}

Hom(K_infinity,K_1)
Hom(K_1,K_infinity)

--------------------------------------------------------------------------------
-- some scratch code related to  spectralSequencePageMap --

A=QQ[x,y,z]
C = koszul vars A
K = filteredComplex C
E = spectralSequence K

E^0
E^0 _{0,0}
E^0 _{10,25}

E^0 .dd
myMaps = E^1 .dd
myMaps_{-2,3}
myMaps_{1,0}
spots myMaps
myMaps_{3,-2}
myMaps_{3,0}
myMaps_{10,10}
myMaps^{-1,1}
myMaps_{1,-1}
E^0 .number
E^0 .filteredComplex
E^2
E^2_{-25,1}
E^2 .dd
spots myMaps

lineOnTop := (s) -> concatenate(width s : "-") || s
testNet = method( )
testNet SpectralSequencePageMap := f -> (
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


--------------------------------
-- the following is an example for filteredComplex constructor.  
-- for this example to work need to load package ChainComplexExtras
 -- need to load package ChainComplexExtras and later SimplicialComplexes
	  -- for this to work.
needsPackage"ChainComplexExtras"
R=QQ[a,b,c,d]
d2=matrix(R,{{1},{0}})
d1=matrix(R,{{0,1}})
C=chainComplex({d1,d2})
D_2= image matrix(R,{{1}})
D_1=image matrix(R,{{1,0},{0,0}})
D_0=image matrix(R,{{1}})

D=chainComplex({inducedMap(D_0,D_1,C.dd_1),inducedMap(D_1,D_2,C.dd_2)})

d=chainComplexMap(C,D,apply(spots C, i-> inducedMap(C_i,D_i,id_C _i)))
isChainComplexMap d
d==chainComplexMap(C,D,{inducedMap(C_0,D_0,id_(C_0)),
	   inducedMap(C_1,D_1,id_(C_1)),
	   inducedMap(C_2,D_2,id_(C_2))})
E_2=image matrix(R,{{0}})
E_1= image matrix(R,{{1,0},{0,0}})
E_0 = image matrix(R,{{1}})
E = chainComplex({inducedMap(E_0,E_1,C.dd_1),inducedMap(E_1,E_2,C.dd_2)})
e=chainComplexMap(C,E,apply(spots C, i->inducedMap(C_i,D_i, id_C _i)))
K=filteredComplex({d,e})
L=filteredComplex({d,e},Shift =>1)
M=filteredComplex({d,e},Shift =>-1) 
--------------------------
--------------------------
---
-- trying to test truncate and filteredComplex ChainComplex Code. --
---
restart
needsPackage "SpectralSequences";
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

A=QQ[x,y,z,w]

C=koszul vars A
truncate(C,-5)
truncate(C,5)
truncate(C,20)
truncate(C,-20)
filteredComplex C
filteredComplex (C[-1])
filteredComplex (C[1])




D= res ideal vars A
filteredComplex D
filteredComplex(D[1])

truncate(D[1],-2)
D[1]

filteredComplex(D[-1])

filteredComplex(truncate(C,1))

filteredComplex(truncate(D,2))


E = filteredComplex ({simplicialComplex ({x*y*z})},ReducedHomology => false)
  
-- All of the above seem to work properly. --

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



H ** (filteredComplex H) 

prune ((filteredComplex H)** F)


prune(F** (filteredComplex H))



max H
max F

E= spectralSequence ((filteredComplex H) ** F)

E^0
E^1
E^2

--new HashTable from apply(keys support E_0, i-> i=> prune E_0 _i)

--new HashTable from apply(keys support E_1, i-> i=> prune E_1 _i)

--new HashTable from apply(keys support E_2, i-> i=> prune E_2 _i)

Tor_0(J,I) == E^2 _{0,0}

prune Tor_1(J,I)

prune E^2 _{1,0} == prune Tor_1(J,I)

(Tor_1(J,I)) == (E^2 _{1,0}) -- this resturned false for some reason.  Strange...
peek Tor_1(J,I)
peek E^2 _{1,0}

EE=spectralSequence(H**(filteredComplex F))

EE^0
EE^1
EE^2

--new HashTable from apply(keys support EE_0, i-> i=> prune EE_0 _i)

--new HashTable from apply(keys support EE_1, i-> i=> prune EE_1 _i)

--new HashTable from apply(keys support EE_2, i-> i=> prune EE_2 _i)

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
truncate(C,-1)
truncate(C,1)

K= filteredComplex {id_C}
filteredComplex ({id_C}, Shift=>-1)

filteredComplex{D}
filteredComplex{D,D}




-----------


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
------------------------------------------------------
---------------------------------------------------------------
-- there seems to be a bug in Hom(ChainComplex,ChainComplex) --
Hom(K_infinity, K_1)
--------------------------------------------------------------
---------------------------------------------------------------
Hom(K_1, K_infinity)
---------------------------------------------------------------

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

max KK


spots KK

KK

K=filteredComplex({F2D,F1D,F0D},ReducedHomology => false)

C=chainComplex F2D
prune (KK**C)

prune (C**KK)
max KK
max C
max K

Hom(C,K)
-- so there is a bug in Hom(C,K)
prune Hom(K,C)

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


