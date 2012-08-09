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
needsPackage "SimplicialComplexes"
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
  if ring M =!= ring N
  then error "expected modules over the same ring";
  R := ring M;
  if ambient M != ambient N
  or M.?relations and N.?relations and M.relations != N.relations
  or M.?relations and not N.?relations
  or not M.?relations and N.?relations
  then error "expected submodules of the same module";
  subquotient(
    ambient M,
    if not M.?generators or not N.?generators then null else M.generators | N.generators,
    if M.?relations then M.relations else null
    )
  )

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
  R := C.ring;
  if R =!= D.ring then error "expected graded modules over the same ring";
  c := spots C;
  d := spots D;
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

-- Computes the total complex of the Hom double complex of two chain complexes
Hom (ChainComplex, ChainComplex) := ChainComplex => (C,D) -> (
  R := C.ring;
  if R =!= D.ring then error "expected chain complexes over the same ring";
  complete C;
  complete D;
  E := chainComplex (lookup( Hom, GradedModule, GradedModule))(C,D);
  scan(spots E, i -> if E#?i and E#?(i-1) then E.dd#i = 
       map(E#(i-1), E#i, 
	    matrix table(
		 E#(i-1).cache.indices, E#i.cache.indices, 
		 (j,k) -> map(E#(i-1).cache.components#(E#(i-1).cache.indexComponents#j), 
		      (E#i).cache.components#((E#i).cache.indexComponents#k),
		      if j#0 === k#0 and j#1 === k#1-1 then (-1)^(k#0)*Hom(C_(j#0),D.dd_(k#1))
		      else if j#0 === k#0 - 1 and j#1 === k#1 then Hom(C.dd_(j#0),D_(k#0))
		      else 0))));
  E)	    		    

Hom (ChainComplex, ChainComplexMap) := ChainComplexMap => (C,f) -> (
     F:= Hom(C,source f); 
     G:= Hom(C,target f);
     map(G,F, i -> map(G_i,F_i, matrix table( G_i.cache.indices,F_i.cache.indices, 
		    (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
			 F#i.cache.components#(F#i.cache.indexComponents#k),
			 if j === k then Hom(C_(j#0), f_(j#1)) 
			 else 0)))))

Hom (ChainComplexMap, ChainComplex) := ChainComplexMap => (f,C) -> (
     G:= Hom(source f, C); 
     F:= Hom(target f, C);
     map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
		    (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
			 F#i.cache.components#(F#i.cache.indexComponents#k),
			 if j === k then Hom(f_(j#0), C_(j#1)) 
			 else 0)))))
  
ChainComplexMap ** ChainComplex := ChainComplexMap => (f,C) -> (
     F:= (source f) ** C; 
     G:= (target f) ** C;
     map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
		    (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
			 F#i.cache.components#(F#i.cache.indexComponents#k),
			 if j === k then f_(j#0) ** C_(j#1) 
			 else 0)))))

ChainComplex ** ChainComplexMap := ChainComplexMap => (C,f) -> (
     F:= C ** source f; 
     G:= C ** target f;
     map(G,F, i -> map (G_i,F_i, matrix table(G_i.cache.indices,F_i.cache.indices,
		    (j,k) -> map(G#i.cache.components#(G#i.cache.indexComponents#j), 
			 F#i.cache.components#(F#i.cache.indexComponents#k),
			 if j === k then C_(j#0) ** f_(j#1) 
			 else 0)))))

--------------------------------------------------------------------------------
-- constructing filtered complexes
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"

-- Retrieves the indices  of the (possibly nontrivial) pieces of the filtration 
spots = K -> select(keys K, i -> class i === ZZ)
max FilteredComplex := K -> max spots K
min FilteredComplex := K -> min spots K

-- Returns the pth subcomplex in a filtration of a chain complex 
-- (our filtrations are descending)
FilteredComplex ^ InfiniteNumber :=
FilteredComplex ^ ZZ := ChainComplex => (K,p) -> (
     -- We assume that spots form a consecutive sequence of integers
  maxK := max K;                   -- all filtrations are separated
  minK := min K;      	      	   -- all filtrations are exhaustive
  if K#?p then K#p else if p < minK then K#minK else if p > maxK then K#maxK
  else error "expected no gaps in filtration")

chainComplex FilteredComplex := ChainComplex => K -> K^-infinity

inducedMap (FilteredComplex, ZZ) := ChainComplexMap => opts -> (K,p) -> (
  if not K.cache#?inducedMaps then K.cache.inducedMaps = new MutableHashTable;
  if not K.cache.inducedMaps#?p then K.cache.inducedMaps#p = inducedMap(K^-infinity, K^p);
  K.cache.inducedMaps#p
  )

FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
  all(min(min C,min D)..max (max C,max D),i-> C^i == D^i))

net FilteredComplex := K -> (
     -- Don't want to display all filtered pieces
     -- Should we display the quotients rather than the submodules?
     -- Plan: display sequence of form "K^(min K) \supset .. \supset K^(max K)"
  v := between("", apply(sort spots K, p -> p | " : " | net K^p));
  if #v === 0 then "0" else stack v)

-- Method for looking at all of the chain subcomplexes pleasantly
see = method();
see FilteredComplex := K -> (
     -- Eliminate the duplication of the homological indexes
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
     new FilteredComplex from apply(keys F, p -> if class p =!= Symbol then p => prune F#p else p => F#p)


Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,C) -> (
     filteredComplex for p from min K to max K list Hom(inducedMap(K,p),C))
    
Hom (ChainComplex,FilteredComplex):= FilteredComplex => (C,K) -> (
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

filteredComplex SpectralSequence := FilteredComplex => E -> (E.filteredComplex)

chainComplex SpectralSequence := ChainComplex => E -> (
  chainComplex filteredComplex E)

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

--get the inverse image of C under the map d
invSubmodule := (d,C) -> (
  g := inducedMap ((target d)/C,target d);
  f := g * d;
  ker f)

pageZ := (r, F,p,q) -> (
     C:= chainComplex F;
     M:= (F^p)_(-p-q);
     d:= C.dd_(-p-q);
     N:= invSubmodule (d,(F^(p+r))_(-p-q-1));
     NQ:= intersect(M, N) + (F^(p+1))_(-p-q);
     NQ/(F^(p+1))_(-p-q))

pageB := (r, F,p,q) -> (
     C:= chainComplex F;
     d:= C.dd_(1 -p-q);
     M := image inducedMap(target d, (F^(p-r+1))_(1-p-q),d);
     MQ:= intersect (M,(F^p)_(-p-q)) + (F^(p+1))_(-p-q);
     MQ/(F^(p+1))_(-p-q))

pageE := (r, F,p,q) -> (
     if r < 1 then ((F^p)_(-p-q))/((F^(p+1))_(-p-q)) else 
     if r == 1 then (
	  C:= chainComplex F;
	  M:= (F^p)_(-p-q);
	  d:= C.dd_(-p-q);
	  N:= invSubmodule (d,(F^(p+r))_(-p-q-1));
	  MQ:= intersect(M, N) + (F^(p+1))_(-p-q);
	  d2:= C.dd_(-p-q+1);
	  NQ:= image inducedMap(target d2, (F^p)_(-p-q+1),d2) + (F^(p+1))_(-p-q);
	  MQ/NQ)
     else pageZ(r,F,p,q)/pageB(r,F,p,q))

SpectralSequenceSheet = new Type of MutableHashTable
SpectralSequenceSheet.synonym = "spectral sequence sheet"

SpectralSequence _ ZZ := SpectralSequenceSheet => (E,r) -> (
  F := filteredComplex E;
  L := for p from E.minF to E.maxF list (
       for q from E.minH - E.maxF to E.maxH - E.minF list (
	    M := pageE(r,F,p,q);
	    if M!= 0 then {{p,q}, M} else continue	    )
       );
  new SpectralSequenceSheet from flatten L | {symbol zero => E.zero} )


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
changeofRing (Module,Module,RingMap):= SpectralSequence => (M,N,f) -> (
     S:= source f;
     T:= target f;
     F:= res M;
     G:= filteredComplex (F ** T);
     spectralSequence (G ** res N))
     

load "Doc/SpectralSequencesDoc.m2"
end

--------------------------------------------------------------------------------
restart
installPackage("SpectralSequences",RemakeAllDocumentation=>true)
check "SpectralSequences";
--viewHelp SpectralSequences

restart
needsPackage "SpectralSequences";
debug SpectralSequences;
R = QQ[x,y,z]
M = R^1/ideal(vars R)
S = R/(x^2-y^2)
N = S^1 /ideal(x^3,x*y^2,y^3)
F = res M
lim = 10
G = res (N, LengthLimit => lim)
g = max G
J=ker G.dd_lim
G#(lim+1) = J
G.dd#(lim+1) = inducedMap(G_lim,G_(lim+1))

H = filteredComplex(F ** S)
see (K = H ** G)
spectralSequence K
E = oo

k = 2
netList apply(lim, k -> prune Tor_k(M,pushForward(map(S,R),N)))

netList support E_0
netList support E_1 
Ei = E_infinity
netList support Ei

G



spots K
VerticalList apply(sort spots K, i -> prune K^i)
phi=F**inducedMap(FF,1);
target phi == F**(FF^-infinity)

spectralSequence FF

Hom(F,G)
Hom(G,F)
fHom(F,F)
G^0 == F

T = G ** F
E = spectralSequence T
E0 = E_0
keys E_0
E1 = E_1
keys E1
prune E1^{0,-2}
prune E1^{0,-1}
prune E1^{0,-3}
E2 = E_2
supportSpectralSequenceSheet E2
prune E2^{2,-3}
prune E2^{1,-3}
prune E2^{0,-3}

E3 = E_3
supportSpectralSequenceSheet E3
prune E3^{3,-4}
prune E3^{2,-4}
prune E3^{1,-4}
prune E3^{0,-4}

T = totalTensor(F,F)
T.dd
G = filteredTensor(F,F)

-- Nathan's first example
id_(QQ^1) || 0*id_(QQ
C = chainComplex(matrix(QQ, {{1},{0}}), matrix(QQ,{{0,1}}))
M1 = { matrix(QQ,{{1}}), matrix(QQ, {{1,0},{0,0}}), matrix(QQ,{{1}})

-- filtered simplicial complex
D0 = simplicialComplex {product gens S}
D1 = simplicialComplex {x*y, x*z}
D2 = simplicialComplex {x*y}

K = filteredComplex{D0,D1,D2}


code(net,Variety)


-- filtration by successive skeleta of the real projective plane
S = QQ[a..f];
D = simplicialComplex monomialIdeal(a*b*c, a*b*f, a*c*e, a*d*e, a*d*f, b*c*d,
  b*d*e,b*e*f,c*d*f,c*e*f)

C = chainComplex D
D1 =simplicialComplex first entries faces(1,D)
D0 =simplicialComplex first entries faces(0,D)
Z =simplicialComplex first entries faces(-1,D)
ring Z
chainComplex Z

K = filteredComplex {D,D1,D0,Z}
E = spectralSequence K
E_0

code(chainComplex, SimplicialComplex)
ring faces(2,D)

break


chainComplex SimplicialComplex := (D) -> (
  d := dim D;
  C := if d < -1 then (coefficientRing ring D)^0[-1]
  else if d === -1 then (coefficientRing ring D)^1
  else chainComplex apply(0..d, r -> boundary(r,D));
  if D.cache.?labels then C[0] else C[1]
  )

