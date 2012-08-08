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
  Version => "0.1'",
  Date => "4 August 2012",
  Authors => {{
      Name => "Nathan Grieve", 
      Email => "nathangrieve@mast.queensu.ca"},     
      {
      Name => "David Berlekamp", 
      Email => "daffyd@math.berkeley.edu", 
      HomePage => "http://www.math.berkeley.edu/~daffyd"},
    {
      Name => "Adam Boocher", 
      Email => "aboocher@math.berkeley.edu", 
      HomePage => "http://www.math.berkeley.edu/~aboocher"},
{
      Name => "Thanh Vu", 
      Email => "vqthanh@math.berkeley.edu",
      HomePage => "http://math.berkeley.edu/~thanh"},
    {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}},
  Headline => "spectral sequences",
  DebuggingMode => true
  )

export {
  "FilteredComplex",
  "filteredComplex",
  "SpectralSequence",
  "spectralSequence",
  "SpectralSequenceSheet",
  "totalHom",
  "filteredHom",
  "spots"
  }

-- symbols used as keys
protect minF
protect maxF
protect minH
protect maxH

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
-- constructing filtered complexes
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"

spots = K -> select(keys K, i -> class i === ZZ)
max FilteredComplex := K -> max spots K
min FilteredComplex := K -> min spots K

FilteredComplex ^ ZZ := ChainComplex => (K,p) -> (
     -- We assume that spots form a consecutive sequence of integers
  maxK := max K;                   -- all filtrations are separated
  minK := min K;      	      	   -- all filtrations are exhaustive
  if K#?p then K#p else if p < minK then K#minK else if p > maxK then K#maxK
  else error "expected no gaps in filtration")

FilteredComplex == FilteredComplex := Boolean => (C,D) -> (
     all(min(min C,min D)..max (max C,max D),i-> C^i == D^i)
     )

FilteredComplex _ ZZ := ChainComplexMap => (K,p) -> (
     minK := min K;
     Source := K^p;
     Target := K^minK;
     f:= i -> inducedMap(Target_i,Source_i);
     map(Target,Source,f)
     )

net FilteredComplex := K -> (
     -- Don't want to display all filtered pieces
     -- Should we display the quotients rather than the submodules?
     -- Eliminate the duplication of the homological indexes     
  v := between("", apply(sort spots K, p -> p | " : " | net K^p));
  if #v === 0 then "0" else stack v)

filteredComplex = method(TypicalValue => FilteredComplex)

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
  P := {0 => C} | for p to #maps-1 list (
       F:= image maps#p;
       p => chainComplex for i from min F to max F - 1 list (
	    inducedMap(F_i,F_(i+1), matrix C.dd_(i+1))
	    ));
  if (last P)#1 != Z then P = P | {#maps+1 => Z};
  return new FilteredComplex from P | {symbol zero => (ring C)^0, symbol cache =>  new CacheTable})
    
--truncate C below ith spot, i.e. set everything below homological degree i to 0
truncateQuot = method();
truncateQuot (ChainComplex, ZZ) := ChainComplex => (C,i) -> (
  complete C;
  if i >= max C then chainComplex gradedModule (ring C)^0 
  else chainComplex apply(drop(spots C,1), k -> if k > i then C.dd_k else if k===i then 
       map(0*C_(k-1), C_k, 0) else map(0*C_(k-1),0*C_k,0)))    


--truncate C above ith spot, i.e. set everything above homological degree i to 0
truncate (ChainComplex, ZZ) := ChainComplex => (C,i) -> (
  complete C;
  if i < min C then chainComplex gradedModule (ring C)^0
  else chainComplex apply(drop(spots C,1), k -> if k <= i then C.dd_k else if k===i+1 then 
       map(C_(k-1), 0*C_k, 0) else map(0*C_(k-1),0*C_k,0)))   
    
filteredComplex ChainComplex := C -> (
  complete C;
  c := drop(spots C,-1);
  filteredComplex apply(c, i -> (
	    E := truncate(C,i);
	    map(C,E, j -> if j < i then map(C_j, E_j, 0) 
		 else map(C_j, E_j, 1)))))

  
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

Hom (ChainComplex, ChainComplex) := ChainComplex => (C,D) -> (
  R := C.ring;
  if R =!= D.ring then error "expected chain complexes over the same ring";
  complete C;
  complete D;
  E := chainComplex lookup( Hom, GradedModule, GradedModule)(C,D);
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


filteredHom = method(Options => {Degree => {1,0}})
filteredHom (ChainComplex, ChainComplex):= FilteredComplex => opts -> (C,D) -> (
     E:= Hom(C,D);
     
     --S^1/(ideal (x,y,z))l := if Degree == {1,0} then length c else length d;
     E --provisionally for testing, makes this like totalHom
     )



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
expression SpectralSequence := E -> new FunctionApplication from {
  spectralSequence, filteredComplex E}

filteredComplex SpectralSequence := FilteredComplex => E -> (
  E.filteredComplex)
chainComplex SpectralSequence := ChainComplex => E -> (
  K := filteredComplex E;
  K^0)

spectralSequence = method(Options => {Degree => 1})
spectralSequence FilteredComplex := SpectralSequence => opts -> K -> (
  new SpectralSequence from {
    symbol minF => min K,
    symbol maxF => max K,
    symbol maxH => - min K^0,
    symbol minH => - max K^0,
    symbol filteredComplex => K,
    symbol zero => K.zero,
    symbol cache => CacheTable}
)

invSubmodule := (d,C) -> (
     g := inducedMap ((target d)/C,target d);
     f := g * d;
     ker f
     )


pageA := (r, F,p,q) -> (
     d:=(F^(min F)).dd_(-p-q);
     M:= (F^p)_(-p-q);
     N:= (F^(p+r))_(-p-q-1);
     P:= invSubmodule (d, N);
     A:= intersect (M,P);
     dA:= inducedMap (N, A, d);
     {A, dA}
     )

pageA2 := (r,F,p,q) -> (
     A:= pageA(r-1,F,p-r+1,q+r-2);
     image A_1
     )

pageZ := (r, F,p,q) -> (
     A:= pageA(r,F,p,q);
     d:= (F^(min F)).dd_(-p-q);
     M:= (F^(p+1))_(-p-q);
     (A_0 + M)/M
     )

pageB := (r,F,p,q) -> (
     A:= pageA2(r,F,p,q);
     d:= (F^(min F)).dd_(-p-q);
     M:= (F^(p+1))_(-p-q);
     (A+M)/M
     )

pageE = method ();
pageE :=  (r,F,p,q) -> (
    Z:= pageZ(r,F,p,q);
    B:= pageB(r,F,p,q);
    Z/B
    ) 


SpectralSequenceSheet = new Type of MutableHashTable
SpectralSequenceSheet.synonym = "spectral sequence sheet"

SpectralSequence _ ZZ := SpectralSequenceSheet => (E,r) -> (
  F := filteredComplex E;
  L := for p from E.minF to E.maxF list (
    M:= for q from E.minH - E.maxF to E.maxH - E.minF list (
      S := pageE(r,F,p,q);
      if S != 0 then 
      {{p,q},inducedMap(pageE(r,F,p+r,q-r+1),S,matrix (F^(p+1)).dd_(-p-q))}
      else continue
      );
    if M != {} then M else continue
 );
  new SpectralSequenceSheet from flatten L | {symbol zero => E.zero} 
  )


SpectralSequenceSheet ^ List := Module => (Er,L) -> (
       if Er#?L then source Er#L else Er.zero
       ) 
  


truncate (ZZ, ChainComplex):= ChainComplex => (i,F) -> (
     S:= ring F;
     L:= apply(toList(min F+1..max F), p -> (
	       if p < i then map(S^0, S^0,0) 
	       else if p == i then map(S^0,F_i,0)
	       else F.dd_p));
     truncated:= (chainComplex L)[min F];
     f:= j -> if j < i then map(F_j,truncated_j,0) else id_(F_j);
     g:= j -> if j < i then map(truncated_j,F_j,0) else id_(F_j);
     {truncated,map(F,truncated,f),map(truncated,F,g)}
     )


     
discrete = method ();
discrete ChainComplex := FilteredComplex => C -> (
     minC:= min C;
     maxC:= max C;
     maps:= apply(toList(minC..maxC), p -> (truncate(p,C))_1);
     filteredComplex maps
     )
	  

tmap := (L,M,f) -> matrix apply (M, i-> apply(L,j->f(j,i)))

	  );
     chainComplex reverse L
     )


Hom (ChainComplex, ChainComplexMap) := ChainComplexMap => (K,f) -> (
     F:= source f;
     G:= target f;
     S:= Hom(K,F); 
     T:= Hom(K,G);
     m:= k -> (
	  g:= (i,j) -> (if i == j then Hom(K_i,f_(i-k)) else map(Hom(K_j,G_(j-k)),Hom(K_i,F_(i-k)),0));
	  L:= toList(max (min K,k + min F)..min(max K,k + max F));
	  tmap (L,L,g)
	  );
     maps:= k -> map(T_k,S_k,m (max K - min F - k));
     map(T,S,maps)
     )

Hom (ChainComplexMap, ChainComplex) := ChainComplexMap => (f,K) -> (
     F:= source f;
     G:= target f;
     S:= Hom(G, K); 
     T:= Hom(F, K);
     m:= k -> (
	  g:= (i,j) -> (if i == j then Hom(f_i,K_(i-k)) else map(Hom(F_j,K_(j-k)),Hom(G_i,K_(i-k)),0));
	  L:= toList(max (min F,k + min K)..min(max F,k + max K));
	  tmap (L,L,g)
	  );
     maps:= k -> map(T_k,S_k,m (max F - min K - k));
     map(T,S,maps)
     )





-- fHom makes a filter complex from double complex of hom of chain complexes with horizontal filtration     
fHom = method();
fHom (ChainComplex, ChainComplex):= FilteredComplex => (C,D) -> (
     minC:= min C;
     maxC:= max C;
     maps := for p from minC to maxC list (
	  trun := truncate(p,C);
	  Hom(trun_2,D)       );
     filteredComplex maps
     )
		    
Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,D) -> fHom(K^(min K),D)
    
     {*		    
Hom (FilteredComplex, ChainComplex):= FilteredComplex => (K,D) -> (
     C:= K^(min K);
     minC:= min C;
     maxC:= max C;
     maps := for p from minC to maxC list (
	  trun := truncate(p,C);
	  Hom(trun_2,D)       );
     filteredComplex maps
     )
  *}

Hom (ChainComplex,FilteredComplex):= FilteredComplex => (C,D) -> (
     maps:= apply(toList(min D..max D),p -> Hom(C,D_p));
     filteredComplex maps
     )
  


ChainComplexMap ** ChainComplex := ChainComplexMap => (f,K) -> (
     F:= source f;
     G:= target f;
     S:= F ** K; 
     T:= G ** K; 
     m:= k -> (
	  g:= (i,j) -> (if i == j then f_i ** K_(k-i) else map(G_j ** K_(k-j),F_i ** K_(k-i),0));
	  L:= toList(max (min F,k - max K)..min(max F,k - min K));
	  tmap (L,L,g)
	  );
     maps:= k -> map(T_k,S_k,m k);
     map(T,S,maps)
     )

ChainComplex ** ChainComplexMap := ChainComplexMap => (K,f) -> (
     F:= source f;
     G:= target f;
     S:= K ** F;
     T:= K ** G;
     m:= k -> (
	  g:= (i,j) -> (if i == j then K_i ** f_(k-i) else map(K_j ** G_(k-j),K_i ** F_(k-i),0));
	  L:= toList(max (min F,k - max K)..min(max F,k - min K));
	  tmap (L,L,g)
	  );
     maps:= k -> map(T_k,S_k,m k);
     map(T,S,maps)
     )

     


FilteredComplex ** ChainComplex := FilteredComplex => (C,D) -> (
     maps := apply(toList(min C..max C), p -> C_p ** D);
     filteredComplex maps
     )

ChainComplex ** FilteredComplex := FilteredComplex => (C,D) -> (
     maps := apply(toList(min D..max D), p -> C ** D_p);
     filteredComplex maps
     )

end

--------------------------------------------------------------------------------

restart
needsPackage "SpectralSequences";
debug SpectralSequences;
S = QQ[x,y]
I = ideal (x,y)
F = res I
G = discrete F
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

