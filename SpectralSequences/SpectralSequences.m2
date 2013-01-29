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

--------------------------------------------------------------------------------
restart
installPackage"SpectralSequences"
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
viewHelp SpectralSequences
------------------------------------------

-- The following are some examples which illustrate the current state of the code.
-- All examples seem to work correctly.
--
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

L = filteredMatrixSimplicialComplex(3,3,R)
all((#L - 1), i -> isSubSimplicialComplex(L#(i+1), L#i))
K = filteredComplex(L, ReducedHomology => false)
E = prune spectralSequence K
E^0
E^1
E^2
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
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
debug SpectralSequences;

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
needsPackage "SimplicialComplexes"; 
needsPackage "ChainComplexExtras";
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
-- note: rpqIsomorphism is not implemented to handle the pruned version.
all(keys support E^0, i->  isIsomorphism rpqIsomorphism(E,i#0,i#1,0))
-- the error is in the rpqIsomorphism code. --
e = spectralSequence K
all(keys support e^0, i->  isIsomorphism rpqIsomorphism(e,i#0,i#1,0))
-- cool.
all(keys support  e^1 , i->  isIsomorphism rpqIsomorphism(e,i#0,i#1,1))
-- cool.
all(keys support e^2, i->  isIsomorphism rpqIsomorphism(e,i#0,i#1,2))
-- cool.
all(keys support e^5, i->  isIsomorphism rpqIsomorphism(e,i#0,i#1,5))
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
-- SS^1 --> SS^3 --> SS^1.
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
-- This example is still very much in progress. --
-- trying to do an example from the paper "A case study in 
-- bigraded commutative algebra" by C-D-S.
-- an appropriate term on the E2 page will correspond to non-koszul syzygies.


restart
needsPackage "SpectralSequences"

R = QQ[x,y,z,w, Degrees => {{1,0},{1,0},{0,1},{0,1}}]
B = ideal(x*z, x*w, y*z, y*w)
help basis
basis({1,1},R)
p_0 = x^2*z
p_1 = y^2*w
p_2 = y^2*z+x^2*w

I = ideal(p_0,p_1,p_2)

ideal gens I


ideal apply(flatten entries gens I, i -> i^2)

-- make the frobenious power of an ideal
Ideal ^ Array := (I,n) -> (ideal apply(flatten entries gens I, i -> i ^ (n#0)))


koszul gens B ^ [2]

-- the following complex is the cech like complex that we want to use.
K = truncate(Hom(koszul gens B ^ [6], R^1),-1)

myChainComplex = method()
-- something like this will let us
-- make chain complexes wit a specified minimum homological degree
myChainComplex(List, ZZ) := (L,n) -> (
     C := new ChainComplex ;
     for i from 0 to #L -1 do (
     C.dd_(n+i) = L#i);
     C.ring = ring C.dd_n;
     C
      )
prune K

prune myChainComplex(drop(apply(support K, i -> K.dd_i),1),0)
-- something like this will let us obtain a new chain complex
-- (with the same differentials) but with the homological
-- indices shifted.  (This is not the usual shift of a chain complex.)  
myChainComplex(ChainComplex, ZZ) := (C,n) -> (
     D := new ChainComplex ;
     D.ring = C.ring;
     for i from min support C + 1 to max support C do(
     D.dd_(i+n) = C.dd_i);
     D
     )

prune K
C = prune myChainComplex(K,1)
C.dd
C_(-3)

K = myChainComplex(truncate(Hom(koszul gens B ^ [6], R^1),-1),1)

C = myChainComplex(koszul matrix(R,{{p_0,p_1,p_2}}), -3)

prune HH K

myFilt = K ** filteredComplex C

E = prune spectralSequence myFilt
E^0
E^1
E^2
(res ideal(p_0,p_1,p_2)) .dd_3
-- so there are non-koszul syzygies
-- of degrees {2,3} and {6,1}

E^2 _{0,-1} ** R^{{2,3}}
-- then look at the degree 0 piece.
-- similarly 
E^2 _{0,-1} ** R^{{6,1}}
-- the key point is ensuring that in the calculation of K above that we have taken 
-- a high enough frobenious power of B to compute the E2 page in the appropriate
-- multidegree correctly.
-- In this example, we are really computing the hypercohomology of the complex C.
-- So we should study or at least write down a condition
-- for what high enough means in terms of C.  (One way of getting high enough is 
-- to make the E1 page computed correctly in an approprate multi-degree.
-- this will be determined by the corresponding twisted modules of C.)
-- One condititon for example will be if l is large enough for HH^q C_p ** R(b) to be 
-- computed correctly (this will be the p,q module on the E1 page) then all
-- modules on the E1 page are computed correctly in this multidegree and so 
-- we get all other pages.
-- if we just want to focus on a particular p,q then need to check p-r,q+r-1 for all
-- possible values of r etc.
-- Note Er computed correctly in a multidegree => E^{r+1} computed correctly,
-- but the converse presumably need not hold in general.


-- check out the top row of the E^1 page.  this looks like it is suppose too.

-- E^1_{p,q} module is supposed to equal HH_q(K ** C_p).
-- we can check this explicitly as 
--follows.

E^1
all(keys (support E^1), i -> E^1 _{i#0,i#1} == (prune HH_(i#1)(K ** C_(i#0))))
-- so this looks promising.

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


