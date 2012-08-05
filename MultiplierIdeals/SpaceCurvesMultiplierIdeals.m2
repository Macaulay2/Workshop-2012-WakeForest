-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--  SPACE CURVES MULTIPLIER IDEALS ---------------------------------------------
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

newPackage(
	"SpaceCurvesMultiplierIdeals",
    	Version => "0.2", 
    	Date => "July 29, 2011",
    	Authors => {
	     {Name => "Zach Teitler"},
	     {Name => "Bart Snapp"},
	     {Name => "Claudiu Raicu"}
	     },
    	Headline => "multiplier ideals of monomial space curves"
    	)

-- End functionality:
-- input: ring, sequence of integers, and a real number
-- output: multiplier ideal

-- Intermediate functionality (we need):
-- Symbolic power of I.
-- term ideal of the monomial ideal. DONE!
-- some intersection of the lattice points. 

-- This implementation is based on the algorithm given in
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
     monomialSpaceCurveMultiplierIdeal,
     monomialSpaceCurveJumpingNumbers,
     monomialSpaceCurveLCT    
     }

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- PACKAGES --------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

needsPackage "Normaliz"
needsPackage "MonomialMultiplierIdeals"
needsPackage "ReesAlgebra"


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- METHODS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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




-- intmat2monomIdeal
--
-- Compute the monomial ideal generated by monomials given by exponent
-- vectors taken from the rows of an integer matrix. Optionally,
-- select a subset of rows of the matrix.
--
-- Input:
--  * a matrix M with integer entries
--  * a ring R
--  * (optional) an integer d
--  * (optional) an integer c
-- Output:
--  * a monomialIdeal I
--
-- Without optional inputs:
--   For each row (a1,a2,...) of M, the monomial x1^a1*x2^a2*... is a generator of I.
-- With a single optional input d:
--   Only read rows whose last entry is equal to d.
-- 
--  Ignore the last column, i.e., (a1,a2,...,an,d) corresponds to the monomial x1^a1*...*xn^an.
-- With two optional inputs d,c:
--   Only read rows whose entry in the c'th column is equal to d. Ignore c'th column.
--
-- This code was copied from Zach Teitler's package
-- MonomialMultiplierIdeals.m2 (v. 0.6.1), which in turn borrows from
-- Normaliz.m2.
-- 

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


-- monomialSpaceCurveMultiplierIdeal
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

monomialSpaceCurveMultiplierIdeal = method()
monomialSpaceCurveMultiplierIdeal(Ring, List, QQ) :=
monomialSpaceCurveMultiplierIdeal(Ring, List, ZZ) := (R, nn, t) -> (
     ff := sortedGens(R,nn);
     curveIdeal := affineMonomialCurveIdeal(R,nn);
     
     indexList := intersectionIndexSet(ff);
     
     
     symbpow := symbolicPowerCurveIdeal(curveIdeal , floor(t-1));
     term    := monomialMultiplierIdeal(termIdeal(curveIdeal) , t);
     
     validl  := intersect apply(indexList ,
                     mm -> exceptionalDivisorValuationIdeal(R,ff,mm,
                          floor(t*ord(mm,ff_1)-exceptionalDivisorDiscrepancy(mm,ff)) ));
     
     intersect(symbpow,term,validl)
     );




-- monomialSpaceCurveLCT
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

monomialSpaceCurveLCT = method()
monomialSpaceCurveLCT(Ring,List) := (R, nn) -> monomialSpaceCurveLCTFromSortedGens(sortedGens(R,nn));

monomialSpaceCurveLCTFromSortedGens = method()
monomialSpaceCurveLCTFromSortedGens(List) :=  ff -> (
     indexList  := intersectionIndexSet(ff);
     curveIdeal := ideal ff;
     lctTerm    := monomialLCT(termIdeal(curveIdeal));
     min (2, lctTerm, 
	  min(
	       apply(indexList, mm -> 
		    (exceptionalDivisorDiscrepancy(mm,ff)+1)/ord(mm,ff_1)
		    )
	       )
	  )
     );
 



-- Qinterval (copied from MonomialMultiplierIdeals v. 0.6.1)
-- give all rational numbers k/denom in the interval [a, b]
Qinterval = method();
Qinterval ( ZZ , Number , Number ) := ( denom, a, b ) -> (
  start := ceiling(denom*a);
  end := floor(denom*b);
  
  L := apply(start..end , k -> promote(k/denom,QQ));
  
  return toList L;
);


-- JumpingDenominators gives potential denominators for jumping
-- numbers
-- Input: List of gens for the curve ideal
-- Output: List of distinct integers 
jumpingDenominators = method();
jumpingDenominators (List) := ff -> (
     indexList  := intersectionIndexSet(ff);
     unique({1} | apply(indexList, m -> ord(m,ff_1)))
     );



-- keynumber: 'key number' of an ideal,
-- a la Hochster-Huneke:
-- should be keynumber=min(ambient dimension, numgens I, analyticSpread I) = analyticSpread I
-- (copied from MonomialMultiplierIdeals v. 0.6.1)
keynumber = (I) -> (
--  return numColumns vars ring I;
  return analyticSpread(I); -- defined in package 'ReesAlgebra'
);



-- potentialJumpingNumbers
-- give a sorted list of all potential jumping numbers
-- in the interval [a,b]
-- Default: [a,b] = [monomialSpaceCurveLCT(I),keynumber(I)]
potentialJumpingNumbers = method();
potentialJumpingNumbers (List) := (ff) -> potentialJumpingNumbers(ff,monomialSpaceCurveLCTFromSortedGens(ff),keynumber ideal ff);
potentialJumpingNumbers ( List , Number , Number ) := (ff , Left, Right) -> (
  
  a := max(Left, monomialSpaceCurveLCTFromSortedGens ff);
  b := Right;
  
  -- empty interval?
  if ( a > b ) then (
    return { };
  );
  
  denoms := jumpingDenominators(ff);
  jnList := set {};
  
  local i;
  for i from 0 to (#denoms-1) do (
    jnList = jnList + set Qinterval( denoms#i , a , b );
  );
  
  jnList = sort toList jnList;
  
  return jnList;
);




-- monomialSpaceCurveJumpingNumbers
-- return a list {jumpingNumbers, multiplierIdeals}
-- where for jumpingNumbers#i <= c < jumpingNumbers#(i+1), J(I^c) = multiplierIdeals#i
-- Finds jumping numbers in interval [a,b]
-- Default: [a,b] = [monomialSpaceCurveLCT(R,nn),keynumber(affineMonomialCurveIdeal(R,nn))]
monomialSpaceCurveJumpingNumbers = method();
monomialSpaceCurveJumpingNumbers ( Ring, List ) := (R, nn) -> monomialSpaceCurveJumpingNumbers(R, nn, monomialSpaceCurveLCT(R, nn),keynumber affineMonomialCurveIdeal(R,nn));
monomialSpaceCurveJumpingNumbers ( Ring, List , ZZ , ZZ ) := (R, nn,a,b) -> monomialSpaceCurveJumpingNumbers(R, nn,promote(a,QQ),promote(b,QQ));
monomialSpaceCurveJumpingNumbers ( Ring, List , QQ , ZZ ) := (R, nn,a,b) -> monomialSpaceCurveJumpingNumbers(R, nn,promote(a,QQ),promote(b,QQ));
monomialSpaceCurveJumpingNumbers ( Ring, List , ZZ , QQ ) := (R, nn,a,b) -> monomialSpaceCurveJumpingNumbers(R, nn,promote(a,QQ),promote(b,QQ));

monomialSpaceCurveJumpingNumbers ( Ring, List , QQ , QQ ) := (R, nn , Left , Right) -> (
  ff  := sortedGens(R,nn);
  lct := monomialSpaceCurveLCT(R,nn);
  
  pjn := potentialJumpingNumbers(ff, Left, Right);
  
  -- Empty list?
  if ( #pjn == 0 ) then (
    return { { }, { } }; -- no jumping numbers, no multiplier ideals
  );
  
  local prev;
  local next;
  local jumpingNumbers;
  local multiplierIdeals;
  
  -- Figure out whether pjn#0 is a jumping number:
  -- We know pjn#0 >= lct.
  -- If pjn#0 == lct, then it's definitely a jumping number
  -- Otherwise, need to actually check:
  -- we want to compare J(I^p) and J(I^(p-epsilon)) (where p=pjn#0)
  -- We don't know how small epsilon needs to be,
  -- so find the greatest potential jumping number less than p
  -- and use that for p-epsilon
  if ( (pjn#0) == lct ) then (
    jumpingNumbers = { lct };
    prev = monomialSpaceCurveMultiplierIdeal(R,nn,lct);
    next = prev;
    multiplierIdeals = { prev };
  ) else (
    pjn2 := potentialJumpingNumbers(ff, lct, pjn#0 );
    -- pjn2#-1 = pjn#0
    -- The greatest potential jumping number less than p is pjn2#-2
    prev = monomialSpaceCurveMultiplierIdeal(R,nn,pjn2#-2);
    next = monomialSpaceCurveMultiplierIdeal(R,nn,pjn#0);
    if ( prev != next ) then (
      -- yes it is a jumping number
      jumpingNumbers = { pjn#0 };
      multiplierIdeals = { next };
    ) else (
      -- no it is not a jumping number
      jumpingNumbers = { };
      multiplierIdeals = { };
    );
  );
  
  -- Now check whether rest of pjn's are jumping numbers:
  
  for i from 1 to (#pjn-1) do (
    
    prev = next;
    next = monomialSpaceCurveMultiplierIdeal(R,nn,pjn#i);
    
    if ( prev != next ) then (
      jumpingNumbers = append( jumpingNumbers , pjn#i );
      multiplierIdeals = append( multiplierIdeals , next );
    );
  );
  
  return (jumpingNumbers, multiplierIdeals);
);











--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()


doc /// 
Key 
   SpaceCurvesMultiplierIdeals
Headline
   multiplier ideals of monomial space curves
Description
   Text 
    This implementation is based on the algorithm given in
    H.M. Thompson's paper: {\it Multiplier Ideals of Monomial Space Curves}, 
    @HREF { "http://arxiv.org/abs/1006.1915" , "arXiv:1006.1915v4" } @, [math.AG].
///

doc ///
Key
  monomialSpaceCurveMultiplierIdeal
  (monomialSpaceCurveMultiplierIdeal,Ring,List,QQ)
  (monomialSpaceCurveMultiplierIdeal,Ring,List,ZZ)
Headline
  multiplier ideal of monomial space curve
Usage
  I = monomialSpaceCurveMultiplierIdeal(R,n,t)
Inputs
  R:Ring
  n:List
     three integers
  t:QQ
Outputs
  I:Ideal
Description
  Text
  
    Given a monomial space curve {\tt C} and a parameter {\tt t}, the function 
    {\tt monomialSpaceCurveMultiplierIdeal} computes the multiplier ideal associated to the embedding of {\tt C}
    in {\tt 3}-space and the parameter {\tt t}.
    
    More precisely, we assume that {\tt R} is a polynomial ring in three variables, {\tt n = \{a,b,c\}}
    is a sequence of positive integers of length three, and that {\tt t} is a rational number. The corresponding
    curve {\tt C} is then given by the embedding {\tt u\to(u^a,u^b,u^c)}.
  
  Example
    R = QQ[x,y,z];
    n = {2,3,4};
    t = 5/2;
    I = monomialSpaceCurveMultiplierIdeal(R,n,t)

///


doc ///
Key
  monomialSpaceCurveJumpingNumbers
  (monomialSpaceCurveJumpingNumbers, Ring, List)
  (monomialSpaceCurveJumpingNumbers, Ring, List, ZZ, ZZ)
  (monomialSpaceCurveJumpingNumbers, Ring, List, QQ, ZZ)
  (monomialSpaceCurveJumpingNumbers, Ring, List, ZZ, QQ)
  (monomialSpaceCurveJumpingNumbers, Ring, List, QQ, QQ)
    
Headline
  jumping numbers and corresponding multiplier ideals of monomial space curves
Usage
  (jn,mi) = monomialSpaceCurveJumpingNumbers(R,n)
  (jn,mi) = monomialSpaceCurveJumpingNumbers(R,n,min,max)  
Inputs
  R:Ring
  n:List 
   three integers
Outputs
  jn:List 
   the jumping numbers 
  mi:List
   the corresponding multiplier ideals 
Description
  Text
  
    The function {\tt monomialSpaceCurveJumpingNumbers} computes the
    jumping numbers and corresponding multiplier ideals of the space
    curve. This curve is defined via {\tt n = (a,b,c)} through the
    embedding {\tt u\to(u^a,u^b,u^c)}.
    
  Example
    R = QQ[x,y,z];
    n = {2,3,4};
    (jn,mi) = monomialSpaceCurveJumpingNumbers(R,n)

  Text
     By default, the jumping numbers are searched for in the closed
     interval bounded by the log canonical threshold and the analytic
     spread. However, the user may change these bounds via the
     optional arguments min and max:
  
  Example
    R = QQ[x,y,z];
    n = {2,3,4};
    (jn,mi) = monomialSpaceCurveJumpingNumbers(R,n,2,3)

///


doc ///
Key
  monomialSpaceCurveLCT
  (monomialSpaceCurveLCT, Ring, List)
    
Headline
  log canonical threshold of monomial space curves
Usage
  lct = monomialSpaceCurveLCT(R,n)
Inputs
  R:Ring
  n:List 
   three integers
Outputs
  lct:QQ 

Description
  Text
  
    The function {\tt monomialSpaceCurveLCT} computes the log
    canonical threshold of a space curve. This curve is defined via
    {\tt n = (a,b,c)} through the embedding {\tt u\to(u^a,u^b,u^c)}.
    
  Example
    R = QQ[x,y,z];
    n = {2,3,4};
    lct = monomialSpaceCurveLCT(R,n)
///




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


---Test 0 - affineMonomialCurveIdeal
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
assert( (affineMonomialCurveIdeal(R,{2,3,4})) == ideal(y^2-x*z,x^2-z) )
assert( (affineMonomialCurveIdeal(R,{5,8})) == ideal(x^8-y^5) )
assert( (affineMonomialCurveIdeal(R,{1,1,1})) == ideal(y-z,x-z) )
///

---Test 1 - ord
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
assert( (ord({2,3,4},z-x^2)) === 4 )
assert( (ord({1,1,1},z*y+x-x^2)) === 1 )
assert( (ord({0,0,0},(z*y+x-x^2)^2)) === 0 )
assert( (ord({2,3,4},1+x)) === 0 )
///

---Test 2 - sortedGens
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
assert( {x^2-z,y^2-x*z} === (sortedGens(R,{2,3,4})) )
assert( (sortedGens(R,{1,1,1})) === {y-z,x-z} )
assert( (try sortedGens(R,{0,0,0}) else oops) === oops )
///

---Test 3 - exceptionalDivisorValuation
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
assert( (exceptionalDivisorValuation({2,3,4},{1,1,2},x)) === 1 )
assert( (exceptionalDivisorValuation({2,3,4},{1,1,2},y)) === 1 )
assert( (exceptionalDivisorValuation({2,3,4},{1,1,2},z)) === 2 )
assert( (exceptionalDivisorValuation({2,3,4},{1,1,2},z-x^2)) === 2 )
assert( (exceptionalDivisorValuation({2,3,4},{1,1,2},(z-x^2)^3*(x+y+z))) === 7 )
assert( (exceptionalDivisorValuation({3,5,11},{7,1,2},x)) === 7 )
assert( (exceptionalDivisorValuation({3,5,11},{7,1,2},y)) === 1 )
assert( (exceptionalDivisorValuation({3,5,11},{7,1,2},z)) === 2 )
assert( (exceptionalDivisorValuation({3,5,11},{7,1,2},x^2*y-z)) === 3 )
assert( (exceptionalDivisorValuation({3,5,11},{7,1,2},(x^2*y-z)^2 * x * (y + z))) === 14 )
///

---Test 4 - monomialValuationIdeal
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
needsPackage "Normaliz";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y];
assert( (monomialValuationIdeal(R,{2,3},6)) == monomialIdeal (x^3,x^2*y,y^2) )
assert( (monomialValuationIdeal(R,{2,3},1)) == monomialIdeal (x,y) )
assert( (monomialValuationIdeal(R,{2,3},0)) == monomialIdeal 1_R )
assert( (monomialValuationIdeal(R,{2,3},-1)) == monomialIdeal 1_R )

S = QQ[x,y,z];
assert( (monomialValuationIdeal(S,{2,3,4},6)) == monomialIdeal (x^3,x^2*y,y^2,x*z,y*z,z^2) )
assert( (monomialValuationIdeal(S,{3,4,5},9)) == monomialIdeal (x^3,x^2*y,x*y^2,y^3,x^2*z,y*z,z^2) )
assert( (monomialValuationIdeal(S,{3,5,11},0)) == monomialIdeal 1_S )
assert( (monomialValuationIdeal(S,{3,5,11},2)) == monomialIdeal (x,y,z) )
///

---Test 5 - exceptionalDivisorValuationIdeal
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
needsPackage "Normaliz";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
ff = sortedGens(R,{3,4,5});
assert( (exceptionalDivisorValuationIdeal(R,ff,{1,1,2},6)) == ideal(z^3,y^2*z^2,x*y*z^2,x^2*z^2,y^3*z,x*y^2*z,y^4,x^3*y*z,x^4*z,x^2*y^3,x^3*y^2,x^5*y,x^6) )
assert( (exceptionalDivisorValuationIdeal(R,ff,{2,3,4},3)) == ideal(z,y,x^2) )
S = QQ[x,y,z];
ff = sortedGens(S,{2,3,4});
assert( ( exceptionalDivisorValuationIdeal(S,ff,{1,2,2},4)) == ideal(z^2,y*z,y^2,x^2*z,x^2*y,x^3-x*z) )
assert( ( exceptionalDivisorValuationIdeal(S,ff,{2,3,4},6)) == ideal(z^2,y*z,x*z,y^2,x^2-z) )
assert( ( exceptionalDivisorValuationIdeal(S,ff,{2,3,4},1)) == ideal(z,y,x) )
assert( ( exceptionalDivisorValuationIdeal(S,ff,{1,2,2},6)) == ideal(z^3,y*z^2,y^2*z,y^3,x^2*z^2,x^2*y*z,x^3*z-x*z^2,x^2*y^2,x^3*y-x*y*z,x^4-2*x^2*z+z^2) )
assert( ( exceptionalDivisorValuationIdeal(S,ff,{1,2,2},-1)) == ideal 1_S )
assert( ( exceptionalDivisorValuationIdeal(S,ff,{1,2,2},0)) == ideal 1_S )
///

---Test 6 - termIdeal
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
assert( (termIdeal(ideal{y^2-x^3})) == monomialIdeal (x^3,y^2) )
assert( (termIdeal(ideal{y^2-x^3,(x-y)^3})) == monomialIdeal (x^3,x^2*y,y^2) )
assert( (termIdeal(ideal{y^2-x^3,x*y*z+1})) == monomialIdeal 1_R )
assert( (termIdeal(ideal{0_R})) == monomialIdeal 0_R )
assert( (termIdeal(ideal{1_R})) == monomialIdeal 1_R )
///


---Test 7 - symbolicPowerCurveIdeal
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
R = QQ[x,y,z];
I = affineMonomialCurveIdeal(R,{2,3,4})
J = affineMonomialCurveIdeal(R,{3,4,5})
assert(symbolicPowerCurveIdeal(I,3) == I^3)
assert(symbolicPowerCurveIdeal(J,3) != J^3)
assert(symbolicPowerCurveIdeal(J,1) == J)
assert( (symbolicPowerCurveIdeal(J,2)) == ideal(y^4-2*x*y^2*z+x^2*z^2,x^2*y^3-x^3*y*z-y^2*z^2+x*z^3,x^3*y^2-x^4*z-y^3*z+x*y*z^2,x^5+x*y^3-3*x^2*y*z+z^3) )
assert( (symbolicPowerCurveIdeal(J,4)) == ideal(y^8-4*x*y^6*z+6*x^2*y^4*z^2-4*x^3*y^2*z^3+x^4*z^4,x^2*y^7-3*x^3*y^5*z+3*x^4*y^3*z^2-x^5*y*z^3-y^6*z^2+3*x*y^4*z^3-3*x^2*y^2*z^4+x^3*z^5,x^3*y^6-3*x^4*y^4*z+3*x^5*y^2*z^2-x^6*z^3-y^7*z+3*x*y^5*z^2-3*x^2*y^3*z^3+x^3*y*z^4,x^5*y^4-2*x^6*y^2*z+x^7*z^2+x*y^7-5*x^2*y^5*z+7*x^3*y^3*z^2-3*x^4*y*z^3+y^4*z^3-2*x*y^2*z^4+x^2*z^5,x^7*y^3-x^8*y*z-x^4*y^4*z-x^5*y^2*z^2+2*x^6*z^3+y^7*z-4*x*y^5*z^2+8*x^2*y^3*z^3-5*x^3*y*z^4-y^2*z^5+x*z^6,x^8*y^2-x^9*z+x^4*y^5-5*x^5*y^3*z+4*x^6*y*z^2-x*y^6*z+4*x^2*y^4*z^2-2*x^3*y^2*z^3-x^4*z^4-y^3*z^4+x*y*z^5,x^10+2*x^6*y^3-6*x^7*y*z+x^2*y^6-6*x^3*y^4*z+9*x^4*y^2*z^2+2*x^5*z^3+2*x*y^3*z^3-6*x^2*y*z^4+z^6) )
assert( (symbolicPowerCurveIdeal(I,0)) == ideal 1_R )
assert( (symbolicPowerCurveIdeal(J,-1)) == ideal 1_R )
///


----Test 8 - monomialSpaceCurveMultiplierIdeal 
TEST ///
needsPackage"SpaceCurvesMultiplierIdeals";
needsPackage"Dmodules"
debug SpaceCurvesMultiplierIdeals;

R = QQ[x,y,z];
assert( (monomialSpaceCurveMultiplierIdeal(R,{2,3,4},1)) == ideal 1_R )
assert( (monomialSpaceCurveMultiplierIdeal(R,{2,3,4},7/6)) == ideal 1_R )
assert( (monomialSpaceCurveMultiplierIdeal(R,{2,3,4},20/7)) == ideal(y^2*z-x*z^2,x^2*z-z^2,y^3-x*y*z,x*y^2-z^2,x^2*y-y*z,x^3-x*z) )
assert( (monomialSpaceCurveMultiplierIdeal(R,{3,4,5},11/5)) == ideal(y^2-x*z,x^2*y-z^2,x^3-y*z) )
I = affineMonomialCurveIdeal(R,{2,3,4})
assert(monomialSpaceCurveMultiplierIdeal(R,{2,3,4},3/2) == multiplierIdeal(I,3/2))
///



----Test 9 - Qinterval and potentialJumpingNumbers 
TEST ///
needsPackage "SpaceCurvesMultiplierIdeals";
debug SpaceCurvesMultiplierIdeals;
assert ( Qinterval( 3 , 4 , 5 ) === { 4/1 , 13/3 , 14/3 , 5/1 } );
assert ( Qinterval( 3 , 4.5 , 5 ) === { 14/3 , 5/1 } );
R = QQ[x,y,z];
assert( (jumpingDenominators sortedGens(R,{2,3,6})) === {1} )
assert( (jumpingDenominators sortedGens(R,{4,5,11})) === {1,16} )
assert( (potentialJumpingNumbers sortedGens(R,{2,3,6}) ) === {2/1} )
assert( (potentialJumpingNumbers(sortedGens(R,{2,3,6}),1,5)) === {2/1,3/1,4/1,5/1} )
assert( (potentialJumpingNumbers(sortedGens(R,{2,3,6}),1,1)) === {} )
assert( (potentialJumpingNumbers sortedGens(R,{4,5,11})) === {21/16,11/8,23/16,3/2,25/16,13/8,27/16,7/4,29/16,15/8,31/16,2/1,33/16,17/8,35/16,9/4,37/16,19/8,39/16,5/2,41/16,21/8,43/16,11/4,45/16,23/8,47/16,3/1} )
///


----Test 10 - monomialSpaceCurveLCT
TEST ///
needsPackage "SpaceCurvesMultiplierIdeals";
R = QQ[x,y,z];
assert( (monomialSpaceCurveLCT(R,{2,3,4})) === 11/6 )
assert( (monomialSpaceCurveLCT(R,{3,4,5})) === 13/9 )
assert( (monomialSpaceCurveLCT(R,{3,4,11})) === 19/12 )
///




----Test 11 - monomialSpaceCurveJumpingNumbers
TEST ///
needsPackage "SpaceCurvesMultiplierIdeals";
R = QQ[x,y,z];
assert( (monomialSpaceCurveJumpingNumbers(R,{2,3,4})) == ({11/6,2/1},{ideal(z,y,x,x^2-z),ideal(-y^2+x*z,-x^2+z)}) )
assert( (monomialSpaceCurveJumpingNumbers(R,{3,4,5})) == ({13/9,16/9,17/9,2/1,22/9,23/9,25/9,26/9,3/1},{ideal(z,y,x),ideal(z,y,x^2),ideal(z,y^2,x*y,x^2),ideal(-y^2+x*z,-y^2*z+x*z^2,x*y^2-x^2*z,-x^2*y+z^2,-x^3+y*z),ideal(-y^2*z+x*z^2,-y^3+x*y*z,-x*y^2+x^2*z,-x^2*y+z^2,-y^2*z^2+x*z^3,x*y^2*z-x^2*z^2,-x^2*y*z+z^3,-x^3*z+y*z^2,-x^3*z+y*z^2,-x^4+x*y*z),ideal(-y^2*z+x*z^2,-y^3+x*y*z,-x*y^2+x^2*z,y^2*z^2-x*z^3,x*y^2*z-x^2*z^2,-x^2*y*z+z^3,-x^3*z+y*z^2,-x^3*z+y*z^2,-x^3*y+x*z^2,-x^4+x*y*z),ideal(-y^2*z+x*z^2,-y^3+x*y*z,y^2*z^2-x*z^3,-x^2*y*z+z^3,-x^3*z+y*z^2,-x^2*y^2+y*z^2,-x^3*y+x*z^2,-x^2*y*z^2+z^4,-x^3*z^2+y*z^3,-x^5+z^3),ideal(-y^2*z+x*z^2,y^2*z^2-x*z^3,-x^2*y*z+z^3,-x^3*z+y*z^2,-y^4+x^2*z^2,-x*y^3+z^3,-x^2*y^2+y*z^2,-x^2*y*z^2+z^4,x^3*z^2-y*z^3,-x^4*y+x^2*z^2,-x^5+z^3),ideal(-y^4+2*x*y^2*z-x^2*z^2,-y^4*z+2*x*y^2*z^2-x^2*z^3,x*y^4-2*x^2*y^2*z+x^3*z^2,-x^2*y^3+x^3*y*z+y^2*z^2-x*z^3,-x^3*y^2+x^4*z+y^3*z-x*y*z^2,-x^5*z-x*y^3*z+3*x^2*y*z^2-z^4,-x^5*y-x*y^4+3*x^2*y^2*z-y*z^3,-x^6-x^2*y^3+3*x^3*y*z-x*z^3)}) )
assert( (monomialSpaceCurveJumpingNumbers(R,{3,4,5},3/2,5/2)) == ({16/9,17/9,2/1,22/9},{ideal(z,y,x^2),ideal(z,y^2,x*y,x^2),ideal(-y^2+x*z,-y^2*z+x*z^2,x*y^2-x^2*z,-x^2*y+z^2,-x^3+y*z),ideal(-y^2*z+x*z^2,-y^3+x*y*z,-x*y^2+x^2*z,-x^2*y+z^2,-y^2*z^2+x*z^3,x*y^2*z-x^2*z^2,-x^2*y*z+z^3,-x^3*z+y*z^2,-x^3*z+y*z^2,-x^4+x*y*z)}) )
///

end

restart
installPackage "SpaceCurvesMultiplierIdeals"
check SpaceCurvesMultiplierIdeals
viewHelp "SpaceCurvesMultiplierIdeals"
debug loadPackage"SpaceCurvesMultiplierIdeals"

