-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- MULTIPLIER IDEALS -----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Copyright 2011 Claudiu Raicu, Bart Snapp, Zach Teitler
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

{*
  multIdeal

   Compute multiplier ideal of an ideal, using various strategies.
   - For general ideals, use Dmodules package.
   - For hyperplane arrangement, use HyperplaneArrangements package.
   - For monomial ideals, use Howald's theorem, implemented in this package.
   - For ideal of monomial curve, use Howard Thompson's theorem, implemented
     in this package.
   - (Future work: generic determinantal ideals, using Amanda Johnson's dissertation)
   - (Future work: plane curve singularities)
   
   Initial version: simply have separate commands for each of the above computations.
   For now, only try to compute multiplier ideals and lcts.
   Eventually, add code for jumping numbers.
   
   
   Future work: a more unified single command with "strategy" optional argument
  
   Optional argument: Strategy
   Possible values: DmodulesMultIdealStrat, MonomialMultIdealStrat,
    MonomialCurveMultIdealStrat, HyperplaneArrangementMultIdealStrat,
    AutomaticMultIdealStrat
   Default value: 'AutomaticMultIdealStrat'
   'Automatic' strategy tries strategies from "cheapest" to most general:
   1. if input ideal is a MonomialIdeal, use Monomial strategy
   2. else if input ideal defines a monomial curve, use MonomialCurve strategy
   3. else if input ideal defines a hyperplane arrangement, use that strategy
      (not yet sure how to test for this)
   4. else use Dmodules strategy.
  
   Input:
   With Dmodules strategy:
    * ideal I
    * rational t
   With Monomial strategy:
    * MonomialIdeal I
    * rational t
   With MonomialCurve strategy:
    * ring S
    * list of integers {a1,...,an} (exponents in parametrization of curve)
    * rational t
    OR
    * ideal I which happens to be the defining ideal of a monomial curve
    * rational t
   With HyperplaneArrangement strategy:
    * CentralArrangement A
    * rational t
    * (optional) list of multiplicities M
    OR (can we do this?)
    * ideal I which happens to be the defining ideal of a central arrangement
      (with multiplicities)
    * rational t
  
   Output:
    * Ideal or MonomialIdeal
*}


newPackage(
  "MultiplierIdeals",
      Version => "0.1", 
      Date => "July 31, 2011",
      Authors => {
       {Name => "Zach Teitler"},
       {Name => "Bart Snapp"},
       {Name => "Claudiu Raicu"}
       },
      Headline => "multiplier ideals, log canonical thresholds, and jumping numbers",
      PackageImports=>{"ReesAlgebra","Dmodules","Normaliz"}
      )

--needsPackage "HyperplaneArrangements"


-- Main functionality:
-- Multiplier ideals.
-- Input: an ideal, a real number
-- Output: the multiplier ideal
-- For arbitrary ideals, use the Dmodules package
-- When possible, use specialized routines for
--  monomial ideals (implemented in this package)
--  ideal of monomial curve (implemented in this package)
--  hyperplane arrangements (implemented in HyperplaneArrangements)


-- Implementation for monomial curves is based on the algorithm given in
-- H.M. Thompson's paper: "Multiplier Ideals of Monomial Space
-- Curves." arXiv:1006.1915v4 [math.AG] 
-- 
-- http://arxiv.org/abs/1006.1915


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORTS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
     multIdealViaDmodules,
     lctViaDmodules,
     multIdealMonomial,
     lctMonomial,
     thresholdMonomial,
     multIdealMonomialCurve,
     lctMonomialCurve,
     multIdealHyperplaneArrangement,
     lctHyperplaneArrangement
     }

--     multIdeal,
--     AutomaticMultIdealStrat,
--     DmodulesMultIdealStrat,
--     MonomialMultIdealStrat

exportMutable {}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- PACKAGES --------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- Set Normaliz version to "normbig", arbitrary-precision arithmetic (vs. "norm64", 64-bit)
-- Format of command in previous versions (Macaulay2 1.3 and pre; Normaliz 2.1 and pre)
-- setNmzVersion("normbig");
-- Format of command as of Macaulay2 1.4, Normaliz 2.5:
-- nmzVersion="normbig";
-- Format of command as of Normaliz 2.7:
setNmzOption("bigint",true);


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- METHODS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- VIA DMODULES ----------------------------------------------------------------
--------------------------------------------------------------------------------

{*
  We should provide access for the various strategies
  and other optional arguments provided in Dmodules
*}

multIdealViaDmodules := (I,t) -> (
  Dmodules$multiplierIdeal(I,t)
  );

lctViaDmodules := (I) -> (
  Dmodules$lct(I)
  );

--------------------------------------------------------------------------------
-- MONOMIAL IDEALS -------------------------------------------------------------
--------------------------------------------------------------------------------

{*
  Code in this section written by Zach Teitler 2010, 2011, 2012
*}

-- NewtonPolyhedron
-- compute a matrix A such that Ax >= 0 defines the cone over
-- the Newton polyhedron of a monomial ideal
-- (ie Newt(I) is placed at height 1)
-- Uses Normaliz
NewtonPolyhedron = method();
NewtonPolyhedron (MonomialIdeal) := (I) -> (
  
  R := ring I;
  use R;
  nmzFilename = temporaryFileName() ;
  setNmzOption("supp",true);
  
  -- Compute equations of supporting hyperplanes of (cone over) Newt(I)
  -- new version of Normaliz/M2 interface no longer exports mons2intmat function
  -- following code 'matrix(I / exponents / flatten)' is paraphrased from Normaliz.m2 source
--  normaliz( mons2intmat(I), 3 ); -- worked with Normaliz.m2, version 0.2.1
  normaliz( matrix(I / exponents / flatten) , 3 ); -- works with Normaliz.m2 version 0.2.1 or 2.0
  M := readNmzData("sup");
  
  -- Clean up tmp files, options
  setNmzOption("normal",true);
  rmNmzFiles();
  
  return M;
  
);

-- multIdealMonomial
-- input: monomialIdeal I, rational number t
-- output: multiplier ideal J(I^t)
----
---- How it works:
----
---- First, compute integer matrix M defining Newton polyhedron Newt(I)
---- in the sense that M = (A|-b) where x^v \in I iff M(v|1) >= 0,
---- ie, Av >= b.
----   Some rows are ``unit rows'' with a single nonzero entry which is a 1,
---- corresponding to requiring the exponents (entries of v) to be >= 0.
---- These define *coordinate* facets of Newt(I) (ie, facets of Newt(I) contained
---- in facets of the positive orthant). All other rows define *non-coordinate*
---- facets.
----
---- Second, get an integer matrix for t*Newt(I) by writing t=p/q
---- and setting M1 = (pA | -qb).
----
---- The inequality
----    (pA) * v >= (qb),
---- or
----    M1 * ( v | 1 ) >= 0,
---- corresponds to t*Newt(I). From Howald's Theorem, we need the interior,
---- Int(t*Newt(I)). It is not quite correct to take M1 * (v | 1) > 0,
---- because this is wrong for the coordinate faces. (It is correct for the
---- non-coordinate faces.) Here "interior" means: relative to the positive orthant.
---- In other words, we are removing the part of the boundary of t*Newt(I)
---- which is in the interior of the positive orthant.
----
---- Let 'bump' be a vector of the same length as b, with entries 0 or 1:
----   the entry is 0 in each row of M1 corresponding to a coordinate face,
----   the entry is 1 in each row of M1 corresponding to a non-coordinate face.
---- Then the lattice points in Int(t*Newt(I)) satisfy
----    (pA | -qb-bump) * (v | 1 ) >= 0,
---- that is
----    (pA)*v >= qb+bump.
---- For integer points with nonnegative entries this is equivalent to
----    (pA)*v > qb.
----
---- Finally, we use Normaliz to compute the monomial ideal containing x^v
---- for v in Int(t*Newt(I)); then use Macaulay2 to quotient by the product
---- of the variables, corresponding to Howald's (1,...,1).

multIdealMonomial = method();
multIdealMonomial (MonomialIdeal, ZZ) := (I,t) -> multIdealMonomial(I,promote(t,QQ));
multIdealMonomial (MonomialIdeal, QQ) := (I,t) -> (
  
  R := ring I;
  use R;
  local multIdeal;
  
  
  if ( t <= 0 ) then (
    
    multIdeal = monomialIdeal(1_R) ;
  
  ) else if ( t >= keynumber I ) then (
    
    s := 1 + floor(t-keynumber(I));
    multIdeal = I^s*multIdealMonomial(I,t-s) ;
  
  ) else (
    
    M := NewtonPolyhedron(I);
    m := numRows M;
    n := numColumns M;
    -- ambient dimension = n-1 !!
    
    nmzFilename = temporaryFileName() ;
    setNmzOption("normal",true);
    
    -- Scale to get t*Newt(I) (clear denominators)
    p := numerator t;
    q := denominator t;
    M1 := M * diagonalMatrix( flatten { toList((n-1):q) , {p} } );
    
    -- Set up "bump" of nontrivial facets, but don't bump coordinate facets
    -- (except we do end up bumping the row (0,..,0,1); but that's okay, no harm)
    bump := apply(toList(0..<m) ,
      i -> (  if ( M_(i,n-1) >= 0 ) then ( return 0; ) else ( return 1; )  ) );
    -- now bump has a 0 in rows corresponding to coordinate facets, 1 in other rows
  
    -- "Bump" t*Newt(I): push nontrivial facets in by "epsilon" (which is 1)
    M2 := M1 - ( matrix(toList(m:toList((n-1):0))) | transpose matrix({bump}) );
    
    -- Semigroup of lattice points inside "bumped" region (i.e., interior of t*Newt(I))
    nmzOut := normaliz(M2,4);
    M3 := nmzOut#"gen";
    
    -- Ideal generated by those lattice points
    -- Normaliz.m2 version 0.2.1: exports an 'intmat2mons' command
    -- the following works in Normaliz.m2 version0.2.1:
--    J := intmat2mons(M3,R,1);
    -- Normaliz.m2 version 2.0 no longer exports that command --- it's internal, we can't use it :(
    -- so I wrote my own... somewhat copied from Normaliz.m2
    J := intmat2monomIdeal(M3,R,1);
    
    -- Howald's translation by (1,1,...,1) is same as colon with product of variables
    multIdeal = monomialIdeal quotient(J, product(flatten entries vars R)) ;
    
    -- Clean up tmp files
    rmNmzFiles();
    
  );
  
  return multIdeal;

);


intmat2monomIdeal = method();
intmat2monomIdeal ( Matrix, Ring ) := (M,R) -> (
  if ( numColumns M > numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  genList := apply( 0..< numRows M ,
                    i -> R_(flatten entries M^{i}) );
  
  return monomialIdeal genList;
);
-- only include rows whose last entry is d; and ignore last column
intmat2monomIdeal ( Matrix, Ring, ZZ ) := (M,R,d) -> intmat2monomIdeal(M,R,d,numColumns(M)-1);
-- only include rows with entry 'd' in column 'c'; and ignore column 'c'
intmat2monomIdeal ( Matrix, Ring, ZZ, ZZ ) := (M,R,d,c) -> (
  if ( numColumns M > 1 + numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  rowList := select( 0 ..< numRows M , i -> (M_(i,c) == d) ) ;
  columnList := delete( c , toList(0 ..< numColumns M) );
  
  M1 := submatrix(M,rowList,columnList);
  
  return intmat2monomIdeal(M1,R);
);




-- lctMonomial: lct of monomial ideal
lctMonomial = method();
lctMonomial (MonomialIdeal) := (I) -> (
  
--  M := NewtonPolyhedron(I);
--  m := numRows M;
--  n := numColumns M;
--  
--  lctList := {};
--  
--  local i;
--  for i from 0 to m-1 do (
--    s := sum( toList(0..(n-2)) , j -> M_(i,j) );
--    if ( M_(i,n-1) != 0 and s != 0 ) then (
--      lctList = append(lctList , -1*s / M_(i,n-1));
--    );
--  );
--  
--  return min(lctList);
--);

  return first thresholdMonomial ( I , 1_(ring(I)) ) ;
);

  

-- thresholdMonomial
-- threshold of inclusion in a multiplier ideal
-- input:
--  1. a monomial ideal I
--  2. a monomial x^v, or exponent vector v
-- output: a pair
--  1. a rational number t, defined by
--        t = sup { c : x^v is in the c'th multiplier ideal of I }
--     the threshold (of inclusion of x^v in the multiplier ideal of I).
--  2. a matrix (A' | -b') consisting of those rows of the defining matrix of Newt(I)
--     which impose the threshold on x^v.
--  In other words, the line joining the origin to the vector (v+(1,..,1)) hits the boundary of Newt(I)
--  at (1/t)*(v+(1,..,1)), and the vector (1/t)*(v+(1,..,1)) lies on the facets defined by the rows of (A' | -b')
--  (via: (A'|-b')(w|1)^transpose >= 0 )
thresholdMonomial = method();
thresholdMonomial (MonomialIdeal , RingElement) := (I , m) -> (
  if ( leadMonomial(m) != m ) then (
    error("Second input must be a monomial (input was ",m,")");
  ) else (
    return thresholdMonomial(I,first exponents m);
  );
  return 0;
);
thresholdMonomial (MonomialIdeal , List) := (I , v) -> (
  
  M := NewtonPolyhedron(I);
  m := numRows M;
  n := numColumns M;
  
  local i;
  threshVal := infinity;
  facetList := {}; -- list of rows
  
  for i from 0 to m-1 do (
    s := sum( toList(0..(n-2)) , j -> M_(i,j)*(1+v_j) );
    if ( M_(i,n-1) != 0 and s != 0 ) then (
      t := -1*s / M_(i,n-1) ;
      if ( t < threshVal ) then (
        threshVal = t;
        facetList = {i};
      ) else if ( t == threshVal ) then (
        facetList = append(facetList , i);
      );
    );
  );
  
  facetMatrix := M^facetList;
  
  return ( threshVal , facetMatrix );
);

-- keynumber: 'key number' of an ideal,
-- a la Hochster-Huneke:
-- should be keynumber=min(ambient dimension, numgens I, analyticSpread I) = analyticSpread I
-- v0.2b: keynumber = ambient dimension = numColumns vars ring I
-- v0.2c: keynumber = analyticSpread
keynumber = (I) -> (
--  return numColumns vars ring I;
--  return numgens trim I;
  return analyticSpread(I); -- defined in package 'ReesAlgebra'
);

--------------------------------------------------------------------------------
-- MONOMIAL CURVES -------------------------------------------------------------
--------------------------------------------------------------------------------

{*
  Code in this section written by Claudiu Raicu, Bart Snapp,
  Zach Teitler 2011, 2012
*}

-- affineMonomialCurveIdeal
--
-- Compute defining ideal of a curve in affine 3-space parametrized by monomials,
-- i.e., parametrized by t -> (t^a,t^b,t^c) for positive integers a,b,c.
--
-- Input:
--  * ring S
--  * list of integers {a,b,c}
-- Output:
--  * ideal (ideal in S defining curve parametrized by t->(t^a,t^b,t^c))
--
-- The ring S should be a polynomial ring over a field. Currently this
-- is not checked.  The integers {a,b,c} should be positive. Currently
-- this is not checked.  The output ideal may need to be trimmed, we
-- do not do this.
--
-- The code for affineMonomialCurveIdeal is based on the code for
-- monomialCurveideal from Macaulay2.

affineMonomialCurveIdeal = (S, a) -> (
     -- check that S is a polynomial ring over a field
     n := # a;
     if not all(a, i -> instance(i,ZZ) and i >= 1)
     then error "expected positive integers";
     t := symbol t;
     k := coefficientRing S;
     M1 := monoid [t];
     M2 := monoid [Variables=>n];
     R1 := k M1;
     R2 := k M2;
     t = R1_0;
     mm := matrix table(1, n, (j,i) -> t^(a#i));
     j := generators kernel map(R1, R2, mm);
     ideal substitute(j, submatrix(vars S, {0..n-1}))
     );


-- ord
--
-- Compute monomial valuation of a given polynomial with respect to a
-- vector that gives the values of the variables.
--
-- Input:
--  * list mm = {a1,a2,a3,...}
--  * polynomial p
-- Output:
--  * integer
--
-- This computes the monomial valuation in which the variable x1 has
-- value a1, x2 has value a2,...  The value of a polynomial is the
-- MINIMUM of the values of its terms (like order of vanishing, NOT
-- like degree).
--
-- The values {a1,a2,...} should be nonnegative and there should be at
-- least as many as the number of variables appearing in the
-- polynomial. Currently we do not check this.

ord = (mm,p) -> (
     R := ring p;
     degs := apply(listForm p, i-> first i);
     min apply(degs, i -> sum apply(i,mm,times))
     );


-- sortedGens
--
-- Compute the minimal generators of the defining ideal of the
-- monomial curve parametrized by t->(t^a1,t^a2,t^a3,...) and return
-- the list of generators in order of increasing values of
-- ord({a1,a2,a3,...}, -).
--
-- Input:
--  * ring R
--  * list nn = {a1,a2,a3,...} of integers
-- Output:
--  * list of polynomials
--
-- The ring R should be a polynomial ring over a field. Currently this
-- is not checked.  The integers {a1,a2,a3,...} should be
-- positive. Currently this is not checked.

sortedGens = (R,nn) -> (
     KK := coefficientRing R;
     genList := flatten entries gens trim affineMonomialCurveIdeal(R,nn);
     L := sort apply(genList, i -> {ord(nn,i), i});
     apply(L, i-> last i)     
     );


-- exceptionalDivisorValuation
--
-- Compute the valuation induced by the (mm,ord(mm,f_2)) exceptional
-- divisor in the resolution of singularities of the monomial curve
-- with exponent vector nn.
--
-- Input:
--  * list of integers nn={a,b,c}
--  * list of integers mm={d,e,f}
--  * polynomial p (in 3 variables)
-- Output:
--  * integer
--
-- The valuation is defined as follows. First we computed the sorted
-- generators (f0,f1,f2,...)  of the defining ideal of the
-- curve. Writing p = f0^d * g where g is not divisible by f0, the
-- valuation of p is d*ord(mm,f1) + ord(mm,g).

exceptionalDivisorValuation = (nn,mm,p) -> (
     R := ring p;
     ff := sortedGens(R,nn);
     n := 0;
     while p % ff_0 == 0 do (p = p//ff_0; n = n+1;);
     n*ord(mm,ff_1) + ord(mm,p)
     );


-- exceptionalDivisorDiscrepancy
--
-- Compute the multiplicity of the relative canonical divisor along
-- the (mm,ord(mm,f_2)-ord(mm,f_1)) exceptional divisor in the
-- resolution of singularities of a monomial curve.
--
-- Input:
--  * list of integers mm={a,b,c}
--  * sorted list of generators of the ideal of the monomial curve
-- Output:
--  * integer

exceptionalDivisorDiscrepancy = (mm,ff) -> (
     sum(mm) - 1 + ord(mm, ff_1) - ord(mm, ff_0)
     );

-- monomialValuationIdeal
--
-- Compute valuation ideal {h : ord(mm,h) >= val}.
--
-- Input:
--  * ring R
--  * list of integers mm={a1,a2,...}
--  * integer val
-- Output:
--  * ideal of R.
-- The ring R should be a polynomial ring over a field.
-- The list mm should have nonnegative integers, with at least as many as the number
-- of variables in R. Currently we do not check these things.

monomialValuationIdeal = (R,mm,val) -> (
     M := (matrix{mm}|matrix{{-val}}) || id_(ZZ^(#mm+1));
     normalizOutput := normaliz(M,4);
     M2 := normalizOutput#"gen";
     intmat2monomIdeal(M2,R,1)
     );


-- exceptionalDivisorValuationIdeal
--
-- Compute valuation ideal {h : v(h) >= val}, where the valuation v is induced by the
-- (mm,ord(mm,f_2)-ord(mm,f_1)) exceptional divisor.
--
-- Input:
--  * ring R
--  * sorted list of generators of curve ideal
--  * list mm={a,b,c}
--  * integer val
-- Output:
--  * ideal

exceptionalDivisorValuationIdeal = (R,ff,mm,val) -> (
     maxpow := ceiling(val / ord(mm,ff_1));
     if maxpow < 0 then ideal(1_R) else
     sum apply(splice{0..maxpow}, i -> ideal(ff_0^i)*monomialValuationIdeal(R,mm,val-i*ord(mm,ff_1)))
     );


-- termIdeal
--
-- Compute smallest monomial ideal containing a given ideal.
--
-- Input:
--  * ideal
-- Output:
--  * monomialIdeal

termIdeal = I -> (
     R := ring I;
     if I == ideal 0_R then return monomialIdeal 0_R else
     return monomialIdeal flatten apply(flatten entries gens I, i -> terms i)
     );

-- symbolicPowerCurveIdeal
--
-- Compute symbolic power of the defining ideal of a monomial space curve.
--
-- Input:
--  * ideal I
--  * integer t
-- Output:
--  * ideal
--
-- For a prime ideal I and p>=0, the symbolic power I^(p) is the ideal of functions vanishing to
-- order at least p at every point of V(I). It is the I-primary component of I^p. The non-I-primary
-- components of I^p have support contained in Sing(V(I)).
--
-- For our ideals (of monomial curves) the singular locus is a single point, the origin.
-- We compute the symbolic power by computing I^p, then saturating with respect to the ideal
-- of the origin (to remove unwanted primary components).
--
-- In the future this may be replaced by a better algorithm, perhaps?
--
-- We assume the input ideal is indeed prime, and that its unique singular point is the origin.

symbolicPowerCurveIdeal = (I,t) -> saturate(I^(max(0,t)));


-- intersectionIndexSet
--
-- Compute indexing set for intersection appearing in the formula for multiplier ideals.
-- This is a finite set of lattice points defined by some equations and inequalities.
-- See H.M. Thompson's paper (cited above).
--
-- Input:
--  * sorted list of generators of monomial space curve ideal
-- Output:
--  * list (of lattice points, each written as a list of integers)
--

intersectionIndexSet = (ff) -> (
     uu := {(exponents(ff_0))_0, (exponents(ff_1))_0};
     vv := {(exponents(ff_0))_1, (exponents(ff_1))_1};
     
     cols := #(uu_0);
     candidateGens1 := (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{uu_1 - vv_1} || id_(ZZ^cols),4))#"gen";
     candidateGens2 := (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{vv_1 - uu_1} || id_(ZZ^cols),4))#"gen";
     candidateGens  := candidateGens1 || candidateGens2;
     rhoEquation    := (transpose matrix {uu_1-uu_0}) | (transpose matrix {vv_1-vv_0});
     
     T := candidateGens * rhoEquation;
     rows := toList select(0..<numRows T, i -> all(0..<numColumns T, j -> T_(i,j) > 0));
     unique apply(rows, i -> flatten entries candidateGens^{i})
     );


-- multIdealMonomialCurve
--
-- Compute multiplier ideal of the defining ideal of a monomial space curve, ie., a curve in
-- affine 3-space parametrized by monomials, t->(t^a,t^b,t^c).
--
-- Input:
--  * ring R
--  * list of integers {a,b,c}, the exponents in the parametrization
--  * an integer or rational number t
-- Output:
--  * an ideal

multIdealMonomialCurve = method()
multIdealMonomialCurve(Ring, List, QQ) :=
multIdealMonomialCurve(Ring, List, ZZ) := (R, nn, t) -> (
     ff := sortedGens(R,nn);
     curveIdeal := affineMonomialCurveIdeal(R,nn);
     
     indexList := intersectionIndexSet(ff);
     
     
     symbpow := symbolicPowerCurveIdeal(curveIdeal , floor(t-1));
     term    := multIdealMonomial(termIdeal(curveIdeal) , t);
     
     validl  := intersect apply(indexList ,
                     mm -> exceptionalDivisorValuationIdeal(R,ff,mm,
                          floor(t*ord(mm,ff_1)-exceptionalDivisorDiscrepancy(mm,ff)) ));
     
     intersect(symbpow,term,validl)
     );




-- lctMonomialCurve
--
-- Compute log canonical threshold of the defining ideal of a monomial
-- space curve, ie., a curve in affine 3-space parametrized by
-- monomials, t->(t^a,t^b,t^c).
--
-- Input:
--  * ring R
--  * list of integers {a,b,c}, the exponents in the parametrization
-- Output:
--  * a rational number

lctMonomialCurve = method()
lctMonomialCurve(Ring,List) := (R, nn) -> lctMonomialCurveFromSortedGens(sortedGens(R,nn));

lctMonomialCurveFromSortedGens = method()
lctMonomialCurveFromSortedGens(List) :=  ff -> (
     indexList  := intersectionIndexSet(ff);
     curveIdeal := ideal ff;
     lctTerm    := lctMonomial(termIdeal(curveIdeal));
     min (2, lctTerm, 
    min(
         apply(indexList, mm -> 
         (
           exceptionalDivisorDiscrepancy(mm,ff)+1)/ord(mm,ff_1)
         )
         )
    )
);
 



--------------------------------------------------------------------------------
-- HYPERPLANE ARRANGEMENTS -----------------------------------------------------
--------------------------------------------------------------------------------

multIdealHyperplaneArrangement = method()
multIdealHyperplaneArrangement(Number,CentralArrangement) := (s,A) -> (
  HyperplaneArrangements$multIdeal(s,A)
  );
multIdealHyperplaneArrangement(Number,CentralArrangement,List) := (s,A,m) -> (
  HyperplaneArrangements$multIdeal(s,A,m)
  );

lctHyperplaneArrangement(CentralArrangement) := (A) -> (
  HyperplaneArrangements$lct(A)
  );



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- THE END ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end



{*
multIdeal = method(TypicalValue=>Ideal,
                         Options=>{Strategy=>AutomaticMultIdealStrat});

-- with integer input:
-- promote to rational number, keep options the same
multIdeal(Ideal,ZZ) := opt -> (I,t) ->
  multIdeal(I,promote(t,QQ),opt);


multIdeal(Ideal,QQ) := opt -> (I,t) -> (
  if (opt.Strategy == DmodulesMultIdealStrat) then (
    return multIdealViaDmodules(I,t);
  ) else if (opt.Strategy == AutomaticMultIdealStrat) then (
    return multIdeal(I,t,Strategy=>DmodulesMultIdealStrat);
  );
  );
*}



