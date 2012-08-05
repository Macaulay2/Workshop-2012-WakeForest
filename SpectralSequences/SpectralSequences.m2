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
  Date => "1 August 2012",
  Authors => {{
      Name => "Nathan Grieve", 
      Email => "nathangrieve@mast.queensu.ca"},
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
  "SpectralSequenceSheet"
  }

-- symbols used as keys
protect minF
protect maxF
protect minH
protect maxH

needsPackage "SimplicialComplexes"
debug Core

--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------
-- constructing filtered complexes
FilteredComplex = new Type of HashTable
FilteredComplex.synonym = "filtered chain complex"

spots := K -> select(keys K, i -> class i === ZZ)
max FilteredComplex := K -> max spots K
min FilteredComplex := K -> min spots K

FilteredComplex ^ ZZ := ChainComplex => (K,p) -> (
  maxK := max K;                   -- all filtrations are separated
  minK := min K;      	      	   -- all filtrations are exhaustive
  if K#?p then K#p else if p < minK then K#minK else K#maxK)

net FilteredComplex := K -> (
  v := between("", apply(sort spots K, p -> p | " : " | net K^p));
  if #v === 0 then "0" else stack v)

filteredComplex = method(
  Dispatch => Thing, 
  TypicalValue => FilteredComplex)

filteredComplex Sequence :=
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
    C = target maps#0);	       	       	    -- all filtrations are exhaustive
  Z := image map(C, C, i -> 0*id_(C#i));    -- all filtrations are separated
  P := {{0,C}} | apply(#maps, p -> {p+1, image maps#p});
  if (last P)#1 != Z then P = P | {{#maps+1, Z}};
  return new FilteredComplex from P | {{symbol cache, new CacheTable}})
    
filteredComplex ChainComplex := C -> (
  complete C;
  g := map(C, C, i -> 0*id_(C#i));
  return filteredComplex{g})
    

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
  spectralSequence, chainComplex E}

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
    symbol minH => min K^0,
    symbol maxH => max K^0,
    symbol filteredComplex => K,
    symbol cache => CacheTable})

cycles := (K,r,p,q) -> (
  ker inducedMap(K^0^(p+q+1) / K^(p+r)^(p+q+1), K^p^(p+q), (K^0).dd_(-p-q)))
boundaries := (K,r,p,q) -> (
  image ((K^(p-r+1)).dd_(-p-q+1)) + image id_(K^(p+1)^(p+q)))


SpectralSequenceSheet = new Type of MutableHashTable
SpectralSequenceSheet.synonym = "spectral sequence sheet"

SpectralSequence _ ZZ := SpectralSequenceSheet => (E,r) -> (
  K := filteredComplex E;
  L := {};
  for p from E.minF to E.maxF do (
    for q from E.minH to E.maxH do (
      L = {{p,q},(cycles(K,r,p,q) + boundaries(K,r,p,q)) / boundaries(K,r,p,q)};
      ))
  )

end

--------------------------------------------------------------------------------

restart
needsPackage "SpectralSequences";
debug SpectralSequences
S = QQ[x,y,z];
C = res ideal gens S;   -- Koszul complex
K = filteredComplex C
K^(-2)
K^4

spectralSequence K
E = spectralSequence K
filteredComplex E
chainComplex E
keys E

r = 0
L = {};
for p from E.minF to E.maxF do (
  for q from E.minH to E.maxH do (
    << (p,q) << "  " << cycles(K,r,p,q) << "  " << boundaries(K,r,p,q) << endl;
    L = {{p,q},(cycles(K,r,p,q) + boundaries(K,r,p,q)) / boundaries(K,r,p,q)};
    ))
Er = new SpectralSequenceSheet from {L}
keys Er
cycles(K,r,p,q)
boundaries(K,0,0,1)
(image (K^1).dd_0) 
(K^1) == 0
image id_(K^0^(-1))
K^0^(-1)  

-- Nathan's first example
id_(QQ^1) || 0*id_(QQ
C = chainComplex(matrix(QQ, {{1},{0}}), matrix(QQ,{{0,1}}))
M1 = { matrix(QQ,{{1}}), matrix(QQ, {{1,0},{0,0}}), matrix(QQ,{{1}})

-- filtered simplicial complex
D0 = simplicialComplex {product gens S}
D1 = simplicialComplex {x*y, x*z}
D2 = simplicialComplex {x*y}

K = filteredComplex(D0,D1,D2)


code(net,Variety)

cycles = (K,p,q,r) -> (
  ker inducedMap(K^0^(p+q+1) / K^(p+r)^(p+q+1), K^p^(p+q), (K^0).dd_(-p-q)))

boundaries = (K,p,q,r) -> (
  image ((K^(p-r+1)).dd_(-p-q+1)) + (K^(p+1)^(p+q)))



boundaries(

epq(FilteredCoChainComplex,ZZ,ZZ,ZZ):=
(FK,p,q,r)->(  ((zpq(FK,p,q,r)+bpq(FK,p,q,r)) / bpq(FK,p,q,r)) )

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
p = 2
maps = apply(#L-1, p -> map(C, chainComplex L#(p+1), 
    i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk)))

length C
maps = apply(3, i -> sub(contract(transpose faces(i,L#0), faces(i,L#(p+1))), kk))
chainComplex 
L#(p+1)
C


chainComplex SimplicialComplex := (D) -> (
  d := dim D;
  C := if d < -1 then (coefficientRing ring D)^0[-1]
  else if d === -1 then (coefficientRing ring D)^1
  else chainComplex apply(0..d, r -> boundary(r,D));
  if D.cache.?labels then C[0] else C[1]
  )

