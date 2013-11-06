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
  Date => "6 November 2013",
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
--  "computeErModules",
--  "computeErMaps", 
"ErMaps",
  "spots",
  "SpectralSequencePage", 
  "spectralSequencePage",
--  "rpqHomology",
  "homologyIsomorphism",
  "Shift",
  "ReducedHomology",
  --"project",
  "SpectralSequencePageMap",
 "spectralSequencePageMap",
 -- "pprune",
 -- "epqrMaps",
 -- "pruneEpqrMaps",
 -- "epq",
  "connectingMorphism",
  "sourcePruningMap",
  "targetPruningMap",
   "Page", 
   "PageMap", 
   "pageMap", 
   "page" ,
  -- "InfiniteSequence",
  "prunningMaps" --, "xHom", "yHom" --, "xTensor", "yTensor"
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
------------------------------------------------------------------------------------
-- ChainComplexExtraExtras 
--------------------------------------------------------------------------------------

-- since things are mutable we don't want to cache spots
spots = method()

spots ChainComplex := List => (
  C -> sort select(keys C,i -> class i === ZZ))

max ChainComplex := K -> max spots K
min ChainComplex := K -> min spots K

support ChainComplex := List => (
     C -> sort select (spots C, i -> C_i != 0))



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

-- truncate a chain complex at a given homological degree 
truncate(ChainComplex,ZZ):= (C,q) ->( 
     if q == 0 then return C 
     else (
	  m := min support C;
	  n := max support C;
	  l := length C;
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

----------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- filtered complexes
-------------------------------------------------------------------------------------
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"

spots FilteredComplex := List => (
  K -> sort select(keys K, i -> class i === ZZ))

max FilteredComplex := K -> max spots K
min FilteredComplex := K -> min spots K

support FilteredComplex := List => (
     K -> sort select (spots K, i -> K#i != 0))



FilteredComplex _ InfiniteNumber :=
FilteredComplex _ ZZ := ChainComplex => (K,p) -> (
  if K#?p then K#p 
  else if p < min K then K#(min K) 
  else if p > max K then K#(max K)
  )

FilteredComplex ^ InfiniteNumber :=
FilteredComplex ^ ZZ := ChainComplex => (K,p) -> K_(-p)

chainComplex FilteredComplex := ChainComplex => K -> K_infinity

-- Returns the inclusion map from the pth subcomplex to the top
inducedMap (FilteredComplex, ZZ) := ChainComplexMap => opts -> (K,p) -> (
  if not K.cache#?inducedMaps then K.cache.inducedMaps = new MutableHashTable;
  if not K.cache.inducedMaps#?p then K.cache.inducedMaps#p = inducedMap(K_infinity, K_p);
  K.cache.inducedMaps#p)


net FilteredComplex := K -> (
  v := between("", apply(spots K, p -> p | " : " | net K_p));
  if #v === 0 then "0" else stack v)


-- Primitive constructor, takes a list eg {m_n,m_(n-1), ...,m_0} 
-- defining inclusion maps C=F_(n+1)C > F_(n)C > ... > F_0 C 
-- of subcomplexes of a chain complex (or simplicial complexes) 
-- and produces a filtered complex with integer keys the
-- corresponing chain complex.
-- If F_0C is not zero then by default F_(-1)C is added and is 0.
-- THIS IS THE CONVENTION WE WANT BY DEFAULT.  SEE 
-- THE HOPF FIBRATION EXAMPLE.  TO GET THE CORRECT INDICIES ON THE E2 PAGE
-- WE WANT THE ZERO COMPLEX TO HAVE "FILTRATION DEGREE -1".

filteredComplex = method(Options => {
    Shift => 0,
    ReducedHomology => true})

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
    if any(#maps, p -> class maps#p =!= ChainComplexMap) then (
      error "expected sequence of chain complexes");
    C = target maps#0;-- By default the ambient chain complex is target of first map.
    if any(#maps, p -> target maps#p != C) then (
      error "expected all map to have the same target"));     
  Z := image map(C, C, i -> 0*id_(C#i)); -- make zero subcomplex as a subcomplex of ambient complex 
   --   P :=  {(#maps-opts.Shift) => C} ; 
   P := {};
-- apply (#maps,  p -> #maps - (p+1) -opts.Shift => image maps#p); 
 myList := {};
 for p from 0 to #maps - 1 do (
	 if(image maps#p != C) then 
	 myList = myList |
	  {#maps - (p+1) -opts.Shift => image maps#p};
	  );
  if myList != {} then (P = {(#maps-opts.Shift) => C} | myList)
  else P = { - opts.Shift => C} ;
  if (last P)#1 != Z then (P = P | {(-1-opts.Shift) => Z});
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})


--------------------------------------------------------------------------------
-- constructing filtered complexes ---------------------------------------------
--------------------------------------------------------------------------------



-- make the filtered complex associated to the "naive truncation of a chain complex"
filteredComplex ChainComplex := FilteredComplex => opts-> C->( complete C; 
    n := max support C;
    m := min support C;
    p := length C;
    if p > 0  then (
    H := for i from 1 to p list inducedMap(C,truncate(C,-i));
    filteredComplex( H, Shift => - m) )
    else filteredComplex {map(C, image(0 * id_C), id_C)}--{map(C, id_C} -- now the constructor supports the zero chain complex
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
		     supp := support K_infinity;
     -- try to handle the boundary cases --
     if supp != {} and #supp > 1 then (		
     	  N := max support K_infinity;
	  P := min support K_infinity;
	  T := K_infinity ** C;
filteredComplex(reverse for i from P to (N-1) list 
     inducedMap(T, xTensorComplex(T,i)), Shift => -P) 
 )
    else ( if #supp == 1 then
	(
	p := min supp;
	t := K_infinity ** C;
	filteredComplex( {inducedMap(t, xTensorComplex(t, p))}, Shift => - p + 1)
	)
	else( tt:= K_infinity ** C;
	    filteredComplex({id_tt})
	    )
	)
     )
--
--     	  N := max support K_infinity;
--	  P := min support K_infinity;
--	  T := K_infinity ** C;
--filteredComplex(reverse for i from P to (N-1) list 
--     inducedMap(T, xTensorComplex(T,i)), Shift => -P)
--	  )

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
	   supp := support K_infinity;
	        -- try to handle the boundary cases --
     if supp != {} and #supp > 1 then (		
     	  N := max support K_infinity;
	  P := min support K_infinity;
	  T := C ** K_infinity;
filteredComplex(reverse for i from P to (N-1) list 
     inducedMap(T, yTensorComplex(T,i)), Shift => -P) 
 )
    else ( if #supp == 1 then
	(
	p := min supp;
	t := C ** K_infinity;
	filteredComplex( {inducedMap(t, yTensorComplex(t, p))}, Shift => - p + 1)
	)
	else( tt:= C ** K_infinity ;
	    filteredComplex({id_tt})
	    )
	)
     )	   
--    	  N := max support K_infinity;
--	  P := min support K_infinity;
--	  T := C ** K_infinity;
--	   filteredComplex(reverse for i from P to (N -1) list 
--	       inducedMap(T, yTensorComplex(T,i)), Shift => -P)
--     )


--
-- this is the "old" Hom code. -- I think there is a bug / error in the x filtration --
-- xHom below might be a possible fix... everything needs to be thought about and 
-- checked carefully --

-- produce the "x-filtration" of the Hom complex.
--Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
--modules := (p,q,T)->(apply( (T#q).cache.indices,
--     i-> if (i#0) <= p - q then  
--     image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
--     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );
--     complex := (T,p) -> 
--     	       (K := new ChainComplex;
--		    K.ring = T.ring;
--		    for i from min T to max T do (
--		    if T#?(i-1) then
--		    K.dd_i = inducedMap(directSum(modules(p,i-1,T)),directSum(modules(p,i,T)),T.dd_i));
--	       K
--	       );
--     N := max support K_infinity;
--     P := min support K_infinity;
--     H := Hom(K_infinity,C);
--     filteredComplex(reverse for i from P to (N-1) list inducedMap(H, complex(H,i)), Shift => -P)	 
--      )

-- produce the "y-filtration" of the Hom complex.
--Hom (ChainComplex, FilteredComplex) := FilteredComplex => (C,K) -> (    
--modules := (p,q,T)->(apply( (T#q).cache.indices,
--     i-> if (i#1) <= p then  image (id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))
--     else image(0* id_(((T#q).cache.components)#(((T#q).cache.indexComponents)#i)))) );
--complex := (T,p) ->
--     (K := new ChainComplex;
--		    K.ring = T.ring;
--		    for i from min T to max T do (
--		    if T#?(i-1) then
--	     	    K.dd_i = inducedMap(directSum(modules(p,i-1,T)),directSum(modules(p,i,T)),T.dd_i));
--	       K
--	       );
--     N := max support K_infinity;
--     P := min support K_infinity;
--     H:= Hom(C,K_infinity);
--     filteredComplex(reverse for i from P to (N -1) list 
--	       inducedMap(H, complex(H,i)), Shift => -P)
--     )

---
---
-- here are possible / rewrites of filtered Hom complex...  perhaps this is clearer than
-- above, but also the x-filtration might be what we want ... need to think about it 
-- more carefully ...

-- below seems to be clearer now ... -- and seems to work correctly ?!--

-- produce the "x-filtration" of the Hom complex.
xmodules := (n, d, H)->(
    -- want components {p,q} = Hom(-p, q) with p + q = d and p <= n
     apply( (H#d).cache.indices,
     i -> if  - (i#0) <= n then  
     image (id_(((H#d).cache.components)#(((H#d).cache.indexComponents)#i)))
     else image(0* id_(((H#d).cache.components)#(((H#d).cache.indexComponents)#i)))) );


xComplex := (T,n) -> 
     	       (K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
		    K.dd_i = inducedMap(directSum(xmodules(n,i-1,T)),directSum(xmodules(n,i,T)),T.dd_i));
	       K
	       )

-- produce the "x-filtration" of the Hom complex.
Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
xHom(K,C)
)

xHom = method()
xHom(FilteredComplex, ChainComplex) := FilteredComplex => (K,C) -> (    
    	   supp := support K_infinity;
	        -- try to handle the boundary cases --
     if supp != {} and #supp > 1 then (		
     N := - max support K_infinity;
     P := - min support K_infinity;
     H := Hom(K_infinity,C);
     filteredComplex(reverse for i from N to P - 1 list inducedMap(H, xComplex(H,i)), 
	 Shift => - N)
     )
 else ( if #supp == 1 then
	(
	p := min supp;
	h := Hom(K_infinity , C);
	filteredComplex( {inducedMap(h, xComplex(h, p))}, Shift =>  p + 1 )
	)
    	else( hhh:= Hom(K_infinity , C) ;
	    filteredComplex({id_hhh})
	    )
	)
    )

ymodules := (n, d, H) -> (
    -- want components {p,q} = Hom(-p, q) with p + q = d and q <= n
     apply( (H#d).cache.indices,
     i -> if   (i#1) <= n then  
     image (id_(((H#d).cache.components)#(((H#d).cache.indexComponents)#i)))
     else image(0* id_(((H#d).cache.components)#(((H#d).cache.indexComponents)#i)))) 
 )


yComplex := (T,n) -> 
     	       (K := new ChainComplex;
		    K.ring = T.ring;
		    for i from min T to max T do (
		    if T#?(i-1) then
		    K.dd_i = inducedMap(directSum(ymodules(n,i-1,T)),directSum(ymodules(n,i,T)),T.dd_i));
	       K
	       )
Hom (ChainComplex, FilteredComplex) := FilteredComplex => (C,K) -> ( 
    yHom(C, K)
    )

yHom = method()
yHom(ChainComplex, FilteredComplex) := FilteredComplex => (C,K) -> (
     supp := support K_infinity;
	        -- try to handle the boundary cases --
     if supp != {} and #supp > 1 then (		
     N :=  max support K_infinity;
     P :=  min support K_infinity;
     H := Hom(C, K_infinity);
     filteredComplex(reverse for i from P to N - 1 list inducedMap(H, yComplex(H,i)), 
	 Shift => - P)
     )
  else ( if #supp == 1 then
	(
	p := min supp;
	h := Hom(C , K_infinity );
	filteredComplex( {inducedMap(h, yComplex(h, p))}, Shift =>  - p  + 1 )
	)
    	else( hhh:= Hom(C, K_infinity) ;
	    filteredComplex({id_hhh})
	    )
	) 
    )

------------------------------------
-- Pages and Sequences --
------------------------------------


--------------------------------------------------------------------------------
-- Pages
--------------------------------------------------------------------------------
Page = new Type of MutableHashTable
Page.synonym = "Page"
Page.GlobalAssignHook = globalAssignFunction
Page.GlobalReleaseHook = globalReleaseFunction
describe Page := E -> net expression E

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
    maxQ := max(apply(L, i -> i#1)); 
    minQ := min(apply(L, i -> i#1)); 
    maxP := max(apply(L, i -> i#0));
    minP := min(apply(L,i -> i#0));
    K := while maxQ >= minQ list makeRow(maxP, minP, maxQ, E) do maxQ = maxQ - 1;
   -- netList(K, Boxes => false)
   netList K
    )

makeRow = method()
makeRow(ZZ,ZZ,ZZ,Page) := (maxP,minP,q,E)->(L := {};
      apply(minP .. maxP, i-> 
	   if E#?{i,q} then L = append(L, stack(net E#{i,q}, "  ", net {i,q}))
	   else L = append(L, stack(net 0, " ", net {i,q})));
       L)

Page _ List := (E,L) -> ( if E#?L then E#L else (ring E)^0 )


spots Page := List => ( 
    P -> select(keys P, i -> class i === List and all(i, j -> class j === ZZ))
    )


page = method (Options => {Prune => false})

support Page := List => (
     P -> sort select (spots P, i -> P#i != 0))

-- at present there are no advanced constructors for page.

-- given {minP, maxP, Page} make a page.  the idea here is to make the needed keys
-- we then can make entries nonzero as needed.

-- this present method is mainly for testing code.  It might have other uses later. --
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


--------------------------------------------------------------------------------
-- PageMap
--------------------------------------------------------------------------------

PageMap = new Type of MutableHashTable
PageMap.synonym = "page map"
PageMap.GlobalAssignHook = globalAssignFunction
PageMap.GlobalReleaseHook = globalReleaseFunction
describe PageMap := d -> net expression d


spots PageMap := List => ( 
    d -> select(keys d, i -> class i === List and all(i, j -> class j === ZZ))
    )

support PageMap := List => (
     d -> sort select (spots d, i -> d#i != 0))


PageMap _ List := Matrix => (f,i) ->  if f#?i then f#i else (
      de := f.degree;
      so := (f.source)_i;
      ta := (f.target)_(i + de);
      map(ta,so,0))



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

-- at present there are no constructors for pageMap


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


spectralSequence = method (Options =>{Prune => false})

spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
     new SpectralSequence from {
	  symbol filteredComplex => K,
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
	-- again trying to handle the case of the zero complex --
    if min K_(infinity) < infinity and max K_infinity > - infinity then (
	    for p from min K to max K do (
	  	for q from - p + min K_(infinity) to max K_(infinity) do (
	       	    if E.Prune == false then H#{p,q} = epq(K,p,q,s)
	       	    else H#{p,q} = prune epq(K,p,q,s)
	       );
    	   ); 
       );
   ) ;
   
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

----------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- spectral sequence pages
--------------------------------------------------------------------------------
SpectralSequencePage = new Type of Page
SpectralSequencePage.synonym = "spectral sequence page"
SpectralSequencePage.GlobalAssignHook = globalAssignFunction
SpectralSequencePage.GlobalReleaseHook = globalReleaseFunction
describe SpectralSequencePage := E -> net expression E

spectralSequencePage = method (Options =>{Prune => false})

spectralSequencePage(FilteredComplex, ZZ) := SpectralSequencePage => opts ->  (K,r) -> ( 
new SpectralSequencePage from 
 {symbol filteredComplex=> K, 
       symbol Prune => opts.Prune,
       symbol number => r,
       symbol dd => spectralSequencePageMap(K,r, Prune => opts.Prune), 
       symbol cache => CacheTable}
  )

minimalPresentation SpectralSequencePage := prune SpectralSequencePage := SpectralSequencePage  => opts -> (E) -> (
     spectralSequencePage(E.filteredComplex, E.number, Prune => true)
     )

SpectralSequencePage _ List := Module => (E,i)-> ( source(E.dd _i) )
		    

SpectralSequencePage ^ List := Module => (E,i)-> (E_(-i))    

-- view the modules on a Spectral Sequence Page.  We are refering to these
-- as the support of the page.
-- is this what we want??  Or do we only want to view the nonzero modules?

support SpectralSequencePage := E -> (
     new HashTable from apply(spots E.dd, i -> i=> source E.dd #i) )
 
page SpectralSequencePage := Page => opts -> E -> ( 
    	K := E.filteredComplex;
	s := E.number;
    H := new Page;
    -- again trying to handle the case of the zero complex --
    if min K_(infinity) < infinity and max K_infinity > - infinity then (
	    for p from min K to max K do (
	  	for q from -p + min K_(infinity) to max K_(infinity) do (
	       	    if E.Prune == false then H#{p,q} = epq(K,p,q,s)
	       	    else H#{p,q} = prune epq(K,p,q,s)
	       )
	   );
       );
    H
    )

-- the following two methods are used to view the modules 
-- on the r th page in grid form.  
-- this method is called in net of spectral sequence page.
-- it would be good to delete the zero rows.

net SpectralSequencePage := E -> (page E)

support SpectralSequencePage := E -> (
     new Page from apply(spots E.dd, i-> i=> source E.dd #i) )


------------------------------------------------------------------------
-- below are the methods which compute the
-- individual terms on a page of a spectral sequence
-- WE ARE USING HOMOLOGICAL INDEXING CONVENTIONS.
---------------------------------------------------------------------
-- By default the maximum integer key
-- of the filtered complex corresponds to the ambient complex.
-- This is used in the formulas below.
-- the formulas below are the homological versions of the ones in I.2.4 of Danilov's 
-- treatment of spectral sequences in Shafarevich's Encyclopedia of 
-- Math Algebraic Geometry II.  
-- In any event it is easy enough to prove directly that they satisfy the requirments 
-- for a spectral sequence.

cycles := (K,p,q,r) -> (
ker inducedMap((K_infinity)_(p+q-1) / K_(p-r) _ (p+q-1), 
     K_p _ (p+q), K_(infinity).dd_(p+q), Verify => false))

boundaries := (K,p,q,r) -> (
    ( image (K_(p+r-1).dd_(p+q+1))) + (K_(p-1) _ (p+q)))

-- compute the pq modules on the rth page
epq = method()
epq(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> (
    ((cycles(K,p,q,r) + boundaries(K,p,q,r)) / boundaries(K,p,q,r)))

-- the pq maps on the rth page.
epqrMaps = method()
epqrMaps(FilteredComplex,ZZ,ZZ,ZZ) := (K,p,q,r) -> (
     inducedMap(epq(K,p-r,q+r-1,r), epq(K,p,q,r),(K_infinity).dd_(p+q), Verify => false))


-- prune the pq maps on the rth page. --
--  "sourcePruningMap",
-- "targetPruningMap"
--- the following could be replaced by prune d --- except I want to cache the 
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

ErMaps = method(Options => {Prune => false})
ErMaps(FilteredComplex,ZZ,ZZ,ZZ) := Matrix => opts -> (K,p,q,r) -> (if opts.Prune == false then
     epqrMaps(K,p,q,r)
     else   pruneEpqrMaps(K,p,q,r))

-- the homology at the pq spot on the rth page.
rpqHomology = method()
rpqHomology(SpectralSequence,ZZ,ZZ,ZZ) := (E,p,q,r) -> (
      (ker(E^r .dd_{p,q})) / (image(E^r .dd_{p+r,q-r+1}) )
      )

-- the isomorphism of the homology at the pq spot
-- on the r-th page and the module on at the pq spot on the r+1-th page.
homologyIsomorphism = method()
homologyIsomorphism(SpectralSequence,ZZ,ZZ,ZZ) := (E,p,q,r) -> (
    if E.Prune == false then 
inducedMap(source (E^(r+1) .dd_{p,q}),rpqHomology(E,p,q,r), id_(E^(r+1) .filteredComplex _infinity _(p+q)))
    else
    rpqPruneIsomorphism(E,p,q,r)
  ) 

rpqPruneIsomorphism = method()
rpqPruneIsomorphism(SpectralSequence,ZZ,ZZ,ZZ) := (E,p,q,r) -> (    
    M := rpqHomology(E,p,q,r);
    f := inducedMap(target (E^(r + 1) .dd_{p,q}) .cache.sourcePruningMap,
	    M, (E^r .dd_{p,q}).cache.sourcePruningMap);
	inverse((E^(r + 1) .dd_{p,q}) .cache.sourcePruningMap) * f    
  ) 

---
-- Spectral Sequence Page Maps
---

SpectralSequencePageMap = new Type of PageMap
SpectralSequencePageMap.synonym = "spectral sequence page map"
SpectralSequencePageMap.synonym = "spectral sequence page map"
SpectralSequencePageMap.GlobalAssignHook = globalAssignFunction
SpectralSequencePageMap.GlobalReleaseHook = globalReleaseFunction
describe SpectralSequencePageMap := d -> net expression d



spectralSequencePageMap = method(Options =>{Prune => false})

spectralSequencePageMap(FilteredComplex,ZZ) := SpectralSequencePageMap => opts ->
 (K,r) -> (myList:={};
     -- try to handle case coming from the zero complex --
     Kmin := min K_infinity; Kmax := max K_(infinity);
     if class Kmin < infinity  and Kmax > - infinity then (
           for p from min K to max K do (
		for q from -p + min K_(infinity) to max K_(infinity) -p do (
	       	     myList = 
		     append(myList, {p,q} => ErMaps(K,p,q,r, Prune => opts.Prune)) )); );
	       new SpectralSequencePageMap from 
	       join (myList, {symbol cache =>  new CacheTable,
		    symbol degree => {-r,r-1}, 
		    symbol filteredComplex => K, 
		    symbol Prune => opts.Prune})
      )


SpectralSequencePageMap _ List := Matrix => (d,i)-> (if (d)#?i then d#i 
     	  else  
	       if d.Prune == false then 
	            epqrMaps(d.filteredComplex,i#0,i#1,- d.degree #0) 
     	       else
	       	    pruneEpqrMaps(d.filteredComplex,i#0,i#1,- d.degree #0) 	       	    		    
		    )

SpectralSequencePageMap ^ List := Matrix => (d,i)-> (d_(-i))    


-- auxlillary spectral sequence stuff.  

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
-- here are some needed functions related to hilbert polynomials --
hilbertPolynomial ZZ := ProjectiveHilbertPolynomial => o -> (M) -> ( if M == 0
    then new ProjectiveHilbertPolynomial from {} else
    new ProjectiveHilbertPolynomial from {0 => M}
    )
ProjectiveHilbertPolynomial == ZZ := (M,N) -> (M == hilbertPolynomial N)
ProjectiveHilbertPolynomial + ZZ := (P, N) -> P + hilbertPolynomial N
ZZ + ProjectiveHilbertPolynomial := (P,N) -> hilbertPolynomial P + N
ProjectiveHilbertPolynomial - ZZ := (P, N) -> P - hilbertPolynomial N
ZZ - ProjectiveHilbertPolynomial := (P,N) -> hilbertPolynomial P - N
---

hilbertPolynomial (SpectralSequencePage) := Page => o -> (E) -> (
    P := new Page;
    apply(spots E .dd, i -> P#i = hilbertPolynomial(E_i));
    P
    )

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

-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------



beginDocumentation()

undocumented {page, prunningMaps, --spots, 
    (degree, Page),
    (net, FilteredComplex),
    (net, Page),
    (net, PageMap),
    (net, SpectralSequencePage),
    (net, SpectralSequence),
    (symbol _, Page, List),
  --  (page, List, List, Page),
    (page, SpectralSequencePage),
    (symbol _, PageMap, List),
    (ring, Page),
    (spectralSequencePageMap, FilteredComplex, ZZ),
    (spots, FilteredComplex),
    (spots, PageMap),
 --   (spots, SpectralSequencePageMap),
    (support, SpectralSequencePage),
   spots,  ReducedHomology, sourcePruningMap, targetPruningMap,
   pageMap,
   (describe, SpectralSequence),
   (describe, SpectralSequencePage),
      (describe, SpectralSequencePageMap),
      ErMaps,
      (ErMaps,FilteredComplex, ZZ, ZZ, ZZ),
      (spots, Page),
      (support, Page),
      (support, PageMap),
      (page,List, List, Page),
   (expression, SpectralSequence),
   spectralSequencePageMap,
   (support,ChainComplex),
   (truncate, ChainComplex,ZZ),
   homologyIsomorphism, Shift,
   --prunningMaps, 
   (prunningMaps, SpectralSequencePage) ,
   (describe, Page),
   (describe, PageMap),
   (max, FilteredComplex),
   (min, FilteredComplex),
   (support, FilteredComplex)
    }

document { 
  Key => SpectralSequences,
  Headline => "a package for working with filtered complexes and spectral sequences",
  "Every filtered chain complex determines a spectral sequence;     
  this ", EM "Macaulay2", " package allows users to compute spectral sequences which arise from separated and exhaustive filtrations
  of bounded chain complexes.",
 -- SUBSECTION "Contributors",
 -- "The following people have generously contributed code or worked on our code.",
 -- UL {
   -- {HREF("","")},
   -- {HREF("","")},
   -- {HREF("","")},
   -- {HREF("","")},
   -- {HREF("","")},},
    SUBSECTION "How to use this package",
  UL {
    TO"How to work with filtered complexes", --"Making filtered chain complexes from chain complex maps",
    --TO "Filtrations and tensor product complexes",
    --TO "Filtrations and homomorphism complexes",
    --TO "Filtered complexes and simplicial complexes"
    },
    
 
  SUBSECTION "Some examples which illustrate this package",
  UL {
    TO "Computing the Serre Spectral Sequence associated to a Hopf Fibration",
    TO "Balancing Tor",
    TO "Spectral sequences and connecting morphisms",
    TO "Spectral sequences and non-Koszul syzygies",
    TO "A spectral sequence which fails to degenerate quickly"},
  }

document {
    Key => "How to work with filtered complexes",
    Headline => "creating and manipulating filtered complexes",
    "Here we illustrate some ways for working with filtered complexes",
    UL { 
	TO "How to make filtered complexes from chain complex maps",
	TO "Canonical filtrations on tensor product complexes",
	TO "Canoncial filtrations onhomomorphism complexes",
	TO "Filtered complexes and simplicial complexes"
	},
    }

doc ///
     Key
        "How to make filtered complexes from chain complex maps"
     Headline
     	  the most primitive way to make filtered complexes
     Description
     	  Text  
       	    Here we describe
	    the most basic way to create filtered complexes. 
	    The general framework is as follows.  We start with a 
	    chain complex $C$ and suppose that we are given a list of
	    chain complex maps $\{\phi_n, \phi_{n - 1}, \dots, \phi_0  \}$, 
	    $\phi_i : B_i \rightarrow C$ (here the $B_i$ are chain complexes)
	    with the property that $image \phi_{i - 1}$ is a sub-chain complex of
	    $image \phi_i$.
	    Given this input data we produce a filtered chain complex
	    $F_{n + 1} C \supseteq F_n C \supseteq \dots \supseteq F_{-1} C = 0 $
	    where $F_{n + 1} C = C$ and $F_{i} C = image \phi_i$, for $i = 0, \dots, n$.
	    
	    We now illustrate how this is done in a easy example.
	    We first make three chain complexes $C$, $D$, and $E$.
	    We then make two chain complex maps, $d : D \rightarrow C$ 
	    and $e : E \rightarrow C$, and then
	    compute the resulting filtration of $C$.
	    We first need to load the relavent packages.
          Example
	       needsPackage "SpectralSequences"	    
     	  Text
	       We then make our chain complexes $C$, $D$, and $E$.
     	  Example	       	 
	       R = QQ[x,y,z,w] ;
	       c2 = matrix(R,{{1},{0}}) ;
	       c1 = matrix(R,{{0,1}}) ;
	       C = chainComplex({c1,c2})        
	       D_2 = image matrix(R,{{1}});
	       D_1 = image matrix(R,{{1,0},{0,0}});
	       D_0 = image matrix(R,{{1}});
	       D = chainComplex({inducedMap(D_0,D_1,C.dd_1),inducedMap(D_1,D_2,C.dd_2)})     
               E_2 = image matrix(R,{{0}});
	       E_1 = image matrix(R,{{1,0},{0,0}});
	       E_0 = image matrix(R,{{1}});
	       E = chainComplex({inducedMap(E_0,E_1,C.dd_1),inducedMap(E_1,E_2,C.dd_2)})
     	  Text
	       We now make our chain complex maps.
     	  Example	       	     
	       d = chainComplexMap(C,D,apply(spots C, i-> inducedMap(C_i,D_i,id_C _i)))
	       e = chainComplexMap(C,E,apply(spots C, i->inducedMap(C_i,E_i, id_C _i)))
	  Text
	       We can check that these are indeed are indeed chain complex maps:
	  Example   
	       isChainComplexMap d
	       isChainComplexMap e
     	  Text 
	       Now, given the list of chain complex maps $\{d, e\}$, we obtain
	       a filtration of $C$ by:
     	  Example	       	       
	       K = filteredComplex({d,e})
	  Text
	     If we want to specify a specify minimum filtration degree
             we can use the Shift option.
      	  Example	       	     
	       L = filteredComplex({d,e},Shift =>1)
	       M = filteredComplex({d,e},Shift =>-1)	      	    
///	  

--doc ///
    -- Key
    --      "filtered complexes"
    -- Headline
     --	  how to create and manipulate filtered complexes
    -- Description
  --   	  Text	            	     
--	    @TO"filtered complexes and spectral sequences from simplicial complexes"@
--	  Text    
--	    @TO"filtered complexes from chain complexes"@
--	  Text    
--	    @TO"filtered complexes and spectral sequences from chain complex maps"@
--	  Text    
--	      @TO"filtered complexes from tensor products of chain complexes"@
--	  Text   
--	      @TO"filtered complexes from Hom"@	     	  
--///	  	 

--------------------------------------------
-- Documentation of methods and functions --
--------------------------------------------

--
-- Types
--

    doc ///
     Key
     	  FilteredComplex
     Headline
     	  the type of all filtered complexes
     Description
     	  Text	 
	     This is a data type for storing information associated to separated and exhaustive filtrations of bounded chain complexes.
	     For an overview of how to create and manipulate filtered complexes 
	     see @TO"filtered complexes"@.	  
	     For an overview of how to create and manipulate spectral sequences see
	     @TO"spectral sequences"@.	    
	     For an overview of how to create and manipulate spectral sequence pages see
	     @TO"spectral sequence page"@.
///

doc ///
     Key
     	  SpectralSequencePage
     Headline
     	  the type of all spectral sequence pages
     Description
     	  Text
	       This is a data type for working with spectral sequence pages.	  
	       For an overview of how to create and manipulate filtered complexes 
	       see @TO"filtered complexes"@.	  
	       For an overview of how to create and manipulate spectral sequences see
	       @TO"spectral sequences"@.	    
	       For an overview of how to create and manipulate spectral sequence pages see
	       @TO"spectral sequence page"@.
///	       

--doc ///
--     Key
--     	  InfiniteSequence
--     Headline
--     	  the type of all infinite sequences
--     Description
--     	  Text
--	       This is a data type for working with infinte sequences.
--///	       


doc ///
     Key
     	  Page
     Headline
     	  the type of all pages
     Description
     	  Text
	       This is a data type for working with doubly indexed tables.
///	       

doc ///
     Key
     	  PageMap
     Headline
     	  the type of all page maps
     Description
     	  Text
	       This is a data type for working with doubly indexed maps.
///	       

doc ///
     Key
     	  SpectralSequencePageMap
     Headline
     	  the type of all spectral sequence page maps
     Description
     	  Text
	       This is a data type for working with the maps on a spectral sequence page.
///	       


--- functions and methods --- 
  doc ///
          Key
       	    filteredComplex
          Headline
	       make a filtered complex
     	  Usage
	       K = filteredComplex L
	  Inputs
	       L:List       	  
		    	 or 
	       L:ChainComplex 
	       	    	 or
     	       L:SpectralSequence			 
	       ReducedHomology => Boolean	       	  	    
	       Shift => ZZ
	  Outputs 
	       K: FilteredComplex
	  Description
	       Text
	       	    This is the primative filtered complex constructor.     
///	       

  doc ///
     Key 
      (filteredComplex, List)
     Headline 
      obtain a filtered complex from a list of chain complex maps or a nested list of simplicial complexes
     Usage 
       K = filteredComplex L 
     Inputs 
	  L: List
	  ReducedHomology => Boolean
	  Shift => ZZ
     Outputs 
       K: FilteredComplex
     Description
      	  Text  
       	    We can make a filtered complex from a list of chain complex maps as follows.
	    We first need to load the relavent packages.
          Example
	       needsPackage "SpectralSequences"	    
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
	       L = filteredComplex({d,e},Shift => 1)
	       M = filteredComplex({d,e},Shift => -1)	      	    
	  Text
	    We can make a filtered complex from a nested list of simplicial 
     	    complexes as follows
     	  Example	     
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
          (filteredComplex, ChainComplex)
     Headline 
         obtain a filtered complex from a chain complex
     Usage 
         K = filteredComplex C 
     Inputs 
	  C: ChainComplex
-- these options don't do anything for this constructor.
	  ReducedHomology => Boolean	       	  	    
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
          (filteredComplex, SpectralSequence)
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
  	  (basis, List, SpectralSequencePage)
	  (basis, ZZ, SpectralSequencePage)
     Headline
     	  generators of a particular degree
     Usage
     	  B = basis(L, E)
     Inputs
     	  L:List
	  E:SpectralSequencePage
     Outputs
     	 B:Matrix
     Description
     	  Text 
	       Returns generators for the requested (multi)degree of the spectral sequence page.
    ///
  
doc ///
     Key
  	  (hilbertPolynomial, SpectralSequencePage)
     Headline
     	  the Hilbert polynomial of a spectral sequence page
     Usage
     	  H = hilbertPolynomial(E)
     Inputs
	  E:SpectralSequencePage
     Outputs
     	 H:Page
     Description
     	  Text 
	       Returns the Hilbert polynomials of all modules of the spectral sequence page
    ///

doc ///
     Key
  	  (chainComplex, FilteredComplex)
     Headline
     	  the ambient chain complex of a filtered complex
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
  	  (minimalPresentation, SpectralSequence)
	  (prune, SpectralSequence)
     Headline
     	  a minimal presentation of a spectral sequence
     Usage
     	  E = minimalPresentation e
     Inputs
     	  e:SpectralSequence
     Outputs
     	  E:SpectralSequence
     Description
     	  Text 
	       Returns a minimal presentation of the spectral sequence.
    ///

doc ///
     Key
  	  (minimalPresentation, SpectralSequencePage)
	  (prune, SpectralSequencePage)
     Headline
     	  a minimal presentation of a spectral sequence page
     Usage
     	  E = minimalPresentation e
     Inputs
     	  e:SpectralSequencePage
     Outputs
     	  E:SpectralSequencePage
     Description
     	  Text 
	       Returns a minimal presentation of the spectral sequence page.
    ///


doc ///
     Key
     	  (spectralSequence, FilteredComplex)
	  spectralSequence
     Headline
     	  construct a spectral sequence from a filtered complex
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
     	  the filtered Hom complex
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
     	  construct a spectral sequence page from a filtered complex
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
     	  (symbol _, SpectralSequence, ZZ)
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
     	  The p,q th map on of a spectral sequence page 
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
	      Returns the p,q th map on a spectral sequence page.
     ///

doc ///
     Key
     	  (symbol ^, SpectralSequencePageMap, List)
     Headline
     	  the p,q th map on of a spectral sequence page 
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
	      Returns the p,q th map on a spectral sequence page.
     ///
         
     
doc ///
     Key
     	  (symbol ^, SpectralSequence, ZZ)
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
	  (symbol ^, SpectralSequence, InfiniteNumber)
	  (symbol _, SpectralSequence, InfiniteNumber)
     Headline
     	  the infinity page of a spectral sequence
     Usage
     	  P = E^k
     Inputs
     	  E:SpectralSequence
	  k:InfiniteNumber
     Outputs
     	  P: Page
     Description
     	  Text 
	      Returns the infinity page a spectral sequence.
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
     	  filtered tensor product of complexes
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
	       Returns the two filtrations of the tensor product complex determined by 
	       the double complex
    ///
 doc ///
     Key
     	  (inducedMap, FilteredComplex, ZZ)
     Headline
     	  the i th inclusion map in a filtered complex
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
	       returns the connecting map $H_{n+1}(coker f) \rightarrow H_n (im f)$.
///

doc ///
     Key
     	  (homologyIsomorphism, SpectralSequence, ZZ, ZZ, ZZ)
     Headline
          the homology isomorphism
     Usage 
         g = homologyIsomorphism(SpectralSequence, ZZ, ZZ, ZZ)
     Inputs
         E:SpectralSequence
	 p:ZZ
	 q:ZZ
	 r:ZZ	 
     Outputs
         g:Matrix 
     Description
          Text
	       Computes the isomorphism $ker d^r_{p,q} / image d^r_{p + r, q - r + 1} \rightarrow E^r_{p,q}$
///


---
-- Examples
---

  doc ///
    Key
      "A spectral sequence which fails to degenerate quickly"
   -- Headline
     --	  nonzero maps on higher page numbers
    Description
    	  Text
	       The following example is taken from p. 127, Fig 7.2 of 
	       Zomorodian's "Topology for computing".  In that figure, a filtration of a suitable
	       simplicial complex is pictured.  Here we compute the associated spectral sequence.
	       As we will see below, the spectral sequences has nonzero maps on higher page numbers.
     	  Example
	        needsPackage "SpectralSequences";
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
     Description
     	  Text
	       If $0 \rightarrow A \rightarrow B \rightarrow C \rightarrow 0$ is a 
	       short exact sequence of chain complexes, then the connecting morphism
	       $H_i(C) \rightarrow H_{i - 1}(A)$ can relized as a suitable map
	       on the $E^1$ of a spectral sequence determined by a suitably defined
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
     	  using spectral sequences to compute hypercohomology
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
     	       Text
	       	    We first need to make the relavant simplicial complexes
		    as described on page 110 of the paper.  The
		    simplical complex $D$ below is supposed to be a triangualtion of 
		    $S^3$.  
	       Example		    
		    B = QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2];
		    l1 = {a_0*b_0*b_1*c_1,a_0*b_0*c_0*c_1,a_0*a_1*b_1*c_1,b_0*b_1*c_1*d_1,b_0*c_0*c_1*d_2,a_0*a_1*c_1*d_2,a_0*c_0*c_1*d_2,b_0*c_1*d_1*d_2};
		    l2 = {b_1*c_1*c_2*a_2,b_1*c_1*a_1*a_2,b_1*b_2*c_2*a_2,c_1*c_2*a_2*d_1,c_1*a_1*a_2*d_2,b_1*b_2*a_2*d_2,b_1*a_1*a_2*d_2,c_1*a_2*d_1*d_2};
		    l3 = {c_2*a_2*a_0*b_0,c_2*a_2*b_2*b_0,c_2*c_0*a_0*b_0,a_2*a_0*b_0*d_1,a_2*b_2*b_0*d_2,c_2*c_0*b_0*d_2,c_2*b_2*b_0*d_2,a_2*b_0*d_1*d_2};
		    l4 = {a_0*b_0*b_1*d_1,a_0*b_1*d_0*d_1,b_1*c_1*c_2*d_1,b_1*c_2*d_0*d_1,a_0*a_2*c_2*d_1,a_0*c_2*d_0*d_1};
		    l5 = {a_0*b_1*d_0*d_2,a_0*a_1*b_1*d_2,b_1*c_2*d_0*d_2,b_1*b_2*c_2*d_2,a_0*c_2*d_0*d_2,a_0*c_0*c_2*d_2};
		    D = simplicialComplex(join(l1,l2,l3,l4,l5));
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
		    f0l1 = {a_0*a_1,b_0*b_1,c_0*c_1,d_1*d_2};
		    f0l2 = {a_1*a_2,b_1*b_2,c_1*c_2,d_1*d_2};
		    f0l3 = {a_0*a_2,b_0*b_2,c_0*c_2,d_1*d_2};
		    f0l4 = {a_0*a_2,b_0*b_1,c_1*c_2,d_0*d_1};
		    f0l5 = {a_0*a_1,b_1*b_2,c_0*c_2,d_0*d_2};
		    F0D = simplicialComplex(join(f0l1,f0l2,f0l3,f0l4,f0l5)); 
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
     	       	    K = filteredComplex({D,F1D,F0D},ReducedHomology => false)
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
     	       Text
	       	    Here are the maps.
     	       Example		    		    
     	       	    E0page.dd
     	       Text 
	       	    Compare with the pruned version.
     	       Example		    		    
		    minimalE0page = minimalPresentation(E0page)  
		    minimalE0page.dd
     	       Text
	       	    Now try the $E^1$ page.  
     	       Example		       	       	    
		    E1page = E^1
     	       Text 
	       	    Here are the maps.
     	       Example		    		    
		    E1page.dd 
     	       Text
	       	    Compare with the pruned version.
     	       Example		    		    
		    minimalE1page = minimalPresentation(E1page)  
		    minimalE1page.dd
     	       Text
	       	    Now try the $E^2$ page.
     	       Example		    		    
		    E2page = E^2
     	       Text
	       	    Here are the maps.
     	       Example		    		    
		    E2page.dd
     	       Text
	       	    Here is the pruned version.
     	       Example		    		    
		    minimalE2page = minimalPresentation(E2page)  
		    minimalE2page.dd
		    apply(spots E1page.dd, i->  isIsomorphism homologyIsomorphism(E,i#0,i#1,2))
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






--doc ///
    -- Key
     --     "filtered complexes"
   --  Headline
     --	  how to create and manipulate filtered complexes
    -- Description
  --   	  Text	            	     
--	    @TO"filtered complexes and spectral sequences from simplicial complexes"@
--	  Text    
--	    @TO"filtered complexes from chain complexes"@
--	  Text    
--	    @TO"filtered complexes and spectral sequences from chain complex maps"@
--	  Text    
--	      @TO"filtered complexes from tensor products of chain complexes"@
--	  Text   
--	      @TO"filtered complexes from Hom"@	     	  
--///	  	 
doc ///
     Key
          "filtered complexes and spectral sequences from simplicial complexes"
   --  Headline
    -- 	  making filtered complexes and spectral sequences from simplicial complexes
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
        "filtered complexes from tensor products of chain complexes"
     Headline
     	 making filtered complexes and spectral sequences from tensor products 	
     Description
     	  Text
///	  

--doc ///
--     Key
--       "filtered complexes from Hom"
--     Headline
--     	 making filtered complexes and spectral sequences from Hom
--     Description
--     	  Text
--///	  

doc ///
     Key
     	  SpectralSequence
     Headline
     	  the type of all spectral sequences
     Description
     	  Text
	       This is a data type for working with spectral sequences.
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
     	  "spectral sequence page"
     Headline
     	  how to create and manipluate spectral sequence pages
     Description
     	   Text
	       Here we explain how to create and manipluate spectral sequence pages.
///	  	  


TEST ///
restart;
needsPackage "SpectralSequences";
A = QQ[a,b,c];
C = new ChainComplex;
C.ring = A;
K = filteredComplex C;
assert(K_0 == C);
assert(K_1 == C);
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
assert(all(keys support E^0, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,0)))
assert(all(keys support E^1, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,1)))
assert(all(keys support E^2, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,2)))
assert(all(keys support E^3, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,3)))
assert(all(keys support E^4, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,4)))
assert(all(keys support E^5, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,5)))
assert(all(keys support e^0, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,0)))
assert(all(keys support e^1, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,1)))
assert(all(keys support e^2, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,2)))
assert(all(keys support e^3, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,3)))
assert(all(keys support e^4, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,4)))
assert(all(keys support e^5, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,5)))
///

TEST ///
restart
needsPackage "SpectralSequences";
-- The following example is taken from p. 127, Fig 7.2 of 
-- Zomorodian's "Topology for computing"
A = ZZ [s,t,u,v,w] ;
d0 = simplicialComplex {s};
d1 = simplicialComplex {s,t} ;
d2 = simplicialComplex {s,t,u} ;
d3 = simplicialComplex {s*t, u} ;
d4 = simplicialComplex {s*t, u, v} ;
d5 = simplicialComplex {s*t, u, v, w} ;
d6 = simplicialComplex {s*t, s*w ,u, v} ;
d7 = simplicialComplex {s*t, s*w ,t * w, u, v} ;
d8 = simplicialComplex {s*t, s*w ,t * w, u * v};
d9 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v};
d10 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u};
d11 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w};
d12 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u};
d13 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w};
d14 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w};
d15 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u};
d16 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v};
d17 = simplicialComplex {s*t, s*w ,t * w, u * v, s * v, s*u, u * w, t* u, t*u*w, s*u*w,s*t*u, s*u*v, s*t*w};
L = reverse {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17};
K = filteredComplex (L, ReducedHomology => false);
E = prune spectralSequence K
e = spectralSequence K
assert(all(keys support E^0, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,0)))
assert(all(keys support E^1, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,1)))
assert(all(keys support E^2, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,2)))
assert(all(keys support E^3, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,3)))
assert(all(keys support E^4, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,4)))
assert(all(keys support E^5, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,5)))
assert(all(keys support E^6, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,6)))
assert(all(keys support E^7, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,7)))
assert(all(keys support E^8, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,8)))
assert(all(keys support E^9, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,9)))
assert(all(keys support E^10, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,10)))
assert(all(keys support E^11, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,11)))
assert(all(keys support E^12, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,12)))
assert(all(keys support e^0, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,0)))
assert(all(keys support e^1, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,1)))
assert(all(keys support e^2, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,2)))
assert(all(keys support e^3, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,3)))
assert(all(keys support e^4, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,4)))
assert(all(keys support e^5, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,5)))
assert(all(keys support e^6, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,6)))
assert(all(keys support e^7, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,7)))
assert(all(keys support e^8, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,8)))
assert(all(keys support e^9, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,9)))
assert(all(keys support e^10, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,10)))
assert(all(keys support e^11, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,11)))
assert(all(keys support e^12, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,12)))
///

TEST ///
restart
needsPackage "SpectralSequences";
A = QQ[a,b,c,d];
D = simplicialComplex {a*d*c, a*b, a*c, b*c};
F2D = D;
F1D = simplicialComplex {a*c, d};
F0D = simplicialComplex {a,d};
K = filteredComplex({F2D, F1D, F0D},ReducedHomology => false);
E = spectralSequence(K);
e = prune E;
assert(all(keys support E^0, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,0)))
assert(all(keys support E^1, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,1)))
assert(all(keys support E^2, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,2)))
assert(all(keys support E^3, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,3)))
assert(all(keys support E^4, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,4)))
assert(all(keys support E^5, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,5)))
assert(all(keys support E^6, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,6)))
assert(all(keys support E^7, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,7)))
assert(all(keys support E^8, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,8)))
assert(all(keys support E^9, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,9)))
assert(all(keys support E^10, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,10)))
assert(all(keys support E^11, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,11)))
assert(all(keys support E^12, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,12)))
assert(all(keys support e^0, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,0)))
assert(all(keys support e^1, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,1)))
assert(all(keys support e^2, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,2)))
assert(all(keys support e^3, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,3)))
assert(all(keys support e^4, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,4)))
assert(all(keys support e^5, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,5)))
assert(all(keys support e^6, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,6)))
assert(all(keys support e^7, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,7)))
assert(all(keys support e^8, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,8)))
assert(all(keys support e^9, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,9)))
assert(all(keys support e^10, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,10)))
assert(all(keys support e^11, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,11)))
assert(all(keys support e^12, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,12)))
///

TEST ///
restart
needsPackage"SpectralSequences";
B = QQ[a_0..a_2,b_0..b_2,c_0..c_2,d_0..d_2];
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
K = filteredComplex({D,F1D,F0D},ReducedHomology => false);
E = spectralSequence K;
e = prune spectralSequence K;
assert(all(keys support E^0, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,0)))
assert(all(keys support E^1, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,1)))
assert(all(keys support E^2, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,2)))
assert(all(keys support E^3, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,3)))
assert(all(keys support E^4, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,4)))
assert(all(keys support E^5, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,5)))
assert(all(keys support E^6, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,6)))
assert(all(keys support E^7, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,7)))
assert(all(keys support E^8, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,8)))
assert(all(keys support E^9, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,9)))
assert(all(keys support E^10, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,10)))
assert(all(keys support E^11, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,11)))
assert(all(keys support E^12, j -> isIsomorphism homologyIsomorphism(E,j#0,j#1,12)))
assert(all(keys support e^0, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,0)))
assert(all(keys support e^1, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,1)))
assert(all(keys support e^2, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,2)))
assert(all(keys support e^3, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,3)))
assert(all(keys support e^4, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,4)))
assert(all(keys support e^5, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,5)))
assert(all(keys support e^6, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,6)))
assert(all(keys support e^7, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,7)))
assert(all(keys support e^8, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,8)))
assert(all(keys support e^9, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,9)))
assert(all(keys support e^10, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,10)))
assert(all(keys support e^11, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,11)))
assert(all(keys support e^12, j -> isIsomorphism homologyIsomorphism(e,j#0,j#1,12)))

///


end

---
-- scratch code --
---

-- Now are trying to start debuging --
-- and check all the boundary cases --
 
restart
uninstallPackage"SpectralSequences"
installPackage"SpectralSequences"
installPackage("SpectralSequences", RemakeAllDocumentation => true)
check "SpectralSequences";
-- not sure why one of the checks fails ...

restart
needsPackage"SpectralSequences"

-- these examples show that the few added lines to the 
-- filtered complex constructor handles the case of a one term complex
-- and the zero complex the way that we want it to

A = QQ[x]
M = A^1
D = M[0]
C = new ChainComplex
C.ring = A
E = koszul vars A
filteredComplex D
filteredComplex C
filteredComplex E
d = (filteredComplex D) ** D
filteredComplex{id_C}
filteredComplex{id_D}

e = spectralSequence d
e^0
e^0 .dd
e^infinity
e = prune spectralSequence d
e^0
e^0 . dd
-- maybe we are displaying two many maps ??

d = D ** (filteredComplex D)
e = spectralSequence d
e^0
e^1 
e^1 .dd

c = C ** (filteredComplex C)
e = spectralSequence c
e^0
-- the bug here has been fixed. --
-- so there is a bug here that needs to be fixed ...
-- again need to handle the case that min K_infinity is an infinity number etc --

spots C

min C
min c_infinity

(filteredComplex C) ** C

--the following shows that there might be an error in the filtered Hom code
E
Hom(filteredComplex E, E)
Hom(E, filteredComplex E)
-- the middle piece should be different
-- compare with 
xHom(filteredComplex E, E)
yHom(E, filteredComplex E)
-- so the xHom and yHom might be a fix
-- need to check the shift ...

-- trying to handle the boundary cases for xHom and yHom --

restart
needsPackage"SpectralSequences"

A = QQ[x]
M = A^1
D = M[0]
C = new ChainComplex
C.ring = A
H = koszul vars A

xHom(filteredComplex C, C)
yHom(C, filteredComplex C)

e = spectralSequence xHom(filteredComplex C, C)
e^0
e^10

ee = spectralSequence yHom(C, filteredComplex C)

ee^0
ee^10

xHom(filteredComplex D, D)
yHom(D, filteredComplex D)

e = spectralSequence xHom(filteredComplex D, D)
e^0
e^10

xHom(filteredComplex H, H)
yHom(H, filteredComplex H)

ee = spectralSequence yHom(H, filteredComplex H)

ee^0
ee^10

restart
installPackage"SpectralSequences"
needsPackage"SpectralSequences"
A = QQ[x]
M = A^1
C = M[10]
K = filteredComplex C
E = spectralSequence K
E^0
E^1
E^infinity
c = new ChainComplex 
c.ring = A
k = filteredComplex c
e = spectralSequence k
e^0
e^10
e^infinity
-- so now e^infinity of the zero complex seems to be OK.