newPackage(
        "PD",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {
     toAmbientField, 
     fromAmbientField, 
     factors
     }

------------------------------
-- Radical containment -------
------------------------------

-- helper function for 'radicalContainment'
radFcn = (I) -> (
     if not I.cache#?"RadicalContainmentFunction" then (
     	  R := ring I;
     	  n := numgens R;
     	  S := (coefficientRing R) (monoid[Variables=>n+1,MonomialSize=>16]);
     	  mapto := map(S,R,submatrix(vars S,{0..n-1}));
     	  I = mapto I;
     	  A := S/I;
	  rad := (g) -> (g1 := promote(mapto g, A); g1 == 0 or ideal(g1 * A_n - 1) == 1);
	  I.cache#"RadicalContainmentFunction" = rad;
	  );
     I.cache#"RadicalContainmentFunction"
     )

radicalContainment = method()

-- Returns true if g is in the radical of I.
-- Assumption: I is in a monomial order for which you are happy to compute GB's.x
radicalContainment(RingElement, Ideal) := (g,I) -> (radFcn I) g

-- Returns the first index i such that I_i is not in the radical of J,
--  and null, if none
-- another way to do something almost identical: select(1, I_*, radFcn J)
radicalContainment(Ideal, Ideal) := (I,J) -> (
     rad := radFcn J;
     G := I_*;
     for i from 0 to #G-1 do if not rad G#i then return i;
     null)

TEST ///
  restart
  debug loadPackage "PrimDecomposition"
  R = ZZ/32003[a..f]
  F = map(R,R,symmetricPower(2,matrix{{a,b,c}}))
  I = ker F
  J = I^2
  G = I_0
  assert radicalContainment(G,J)
  assert not radicalContainment(G-a^2,J)
  assert (radicalContainment(I, I^2) === null)
///

--------------------------------   

-- needs documentation
factors = (F) -> (
     R := ring F;
     facs := if R.?toAmbientField then (
	  F = R.toAmbientField F;
     	  numerator factor F)
        else factor F;
     facs = apply(#facs, i -> (facs#i#1, (1/leadCoefficient facs#i#0) * facs#i#0 ));
     facs = select(facs, (n,f) -> # support f =!= 0);
     if R.?toAmbientField then apply(facs, (r,g) -> (r, R.fromAmbientField g)) else facs
     )
-- need test

makeFiberRings = method()
makeFiberRings(List) := (baseVars) -> (
   -- This function takes a list of variables baseVars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][baseVars].  See example below for behavior
   if #baseVars == 0 then error "expected at least one variable in the base";
   R := ring baseVars#0;
   if any(baseVars, x -> ring x =!= R) then error "expected all base variables to have the same ring";
   allVars := set gens R;
   fiberVars := rsort toList(allVars - set baseVars);
   baseVars = rsort baseVars;
   RU := (coefficientRing R) monoid([fiberVars,baseVars,MonomialOrder=>Lex]);
	     --MonomialOrder=>{#fiberVars,#baseVars}]);
   KK := frac((coefficientRing R)[baseVars]);
   KR := KK[fiberVars, MonomialOrder=>Lex];
   KR.toAmbientField = map(frac RU,KR);
   KR.fromAmbientField = (f) -> (if ring f === frac RU then f = numerator f; (map(KR,RU)) f);
   numerator KR := (f) -> numerator KR.toAmbientField f;
   denominator KR := (f) -> denominator KR.toAmbientField f;
   (RU, KR)
   )
-- Needs test

minimalizeOverFrac = method()
minimalizeOverFrac(Ideal, Ring) := (I, S) -> (
     -- I is an ideal in a ring with an elimination order (maybe Lex)
     -- S is of the form k(basevars)[fibervars].
     -- If G is a GB of I, then G S is a GB if I S.
     -- this function returns a reduced minimal Groebner basis of I S, as a list
     -- of polynomials (defined over S).
     -- caveat: ring I must have either a Lex order or a product order, compatible with
     --  fibervars >> basevars.
     G := flatten entries gens gb I;
     phi := map(ring I, S);
     sz := G/size; -- number of monomials per poly, used to choose which elem to take
     GS := flatten entries sub(gens gb I, S);
     minG := flatten entries mingens ideal(GS/leadMonomial);
     GF := for mon in minG list (
	  z := positions(GS, f -> leadMonomial f == mon);
	  i := minPosition (sz_z);
	  GS_(z#i));
     coeffs := GF/leadCoefficient/phi;
     (flatten entries gens forceGB matrix{GF}, coeffs)
     )
-- Needs test

-- question: What if we want to contract away only some of the basevars, not all of them?  Will this ever
--           be the case?
contractToPolynomialRing = method()
contractToPolynomialRing(Ideal) := (I) -> (
     -- assumes: I is in a ring k(basevars)[fibervars] created with makeFiberRings
     -- returns the intersection of I with k[fibervars,basevars] (also created with makeFiberRing).
     --   note: numerator (and denominator) of element in ring I gives an element in k[fibervars,basevars]
     newI := I_*/numerator//ideal//trim;
     denoms := I_*/denominator;
     denomList := unique flatten for d in denoms list (factors d)/last;
     << "denoms = " << denoms << " and denomList = " << denomList << endl;
     Isat := newI;
     for f in denomList do Isat = saturate(Isat, f);
     Isat
     )
-- Needs test

extendIdeal = method()
extendIdeal Ideal := (I) -> (
     -- I is an ideal
     -- returns an ideal whose elements are a reduced GB of I k(indepset)[fibervars]
     indep := support first independentSets I;
     (S,SF) := makeFiberRings indep;
     IS := sub(I, S);
     time gens gb IS;
     (JSF, coeffs) := minimalizeOverFrac(IS, SF);
     ideal JSF
     )
-- Needs test

-----------------------
-- Splitting methods --
-----------------------
splitBy = (I, h) -> (
     Isat := saturate(I, h);
     f := 1_(ring I);
     while not isSubset(f*Isat, I) do f = f*h;
     if Isat == I or Isat == 1 then error ("alas, your element "|toString h|" is not a splitting element");
     if f == 1 then null else (Isat, trim(I + ideal f))
     )
-- Needs test

splitUsingQuotientsBy = (I, h) -> (
     Isat := saturate(I, h);
     I2 := I : Isat;
     if Isat == I or Isat == 1 then (
	  return null
	  );
     if intersect(Isat, I2) == I then (
	  return (Isat, I2);
	  );
     << "second ideal might introduce non-redundancy" << endl;
     f := 1_(ring I);
     while not isSubset(f*Isat, I) do f = f*h;
     if Isat == I or Isat == 1 then error ("alas, your element "|toString h|" is not a splitting element");
     if f == 1 then null else (Isat, trim(I + ideal f))
     )
-- Needs test

splitViaIndep = method()
splitViaIndep Ideal := (I) -> (
-- documentation needed
     indeps := independentSets I;
     indep := support first indeps;
     << "Number of independent sets: " << #indeps << endl;
     << "  Choosing: " << indep << endl;
     (S, SF) := makeFiberRings indep;
     IS := sub(I, S);
     gens gb IS;
     (ISF, coeffs) := minimalizeOverFrac(IS, SF);
     G := (factors product coeffs)/last//product;
     << "  the factors of the flattener: " << netList((factors G)/last) << endl;
     G = sub(G,ring I);
     J1 := saturate(I, G);
     J2 := I: J1;
     if intersect(J2,J1) == I then (
	  << "  Yes! Quotient method split the ideal" << endl;
	  return (J1,J2);
	  );
     << "  No! Need to manually determine the f^ell from lecture" << endl;
     (J1, G)
     )

splitViaIndeps = (I) -> (
     (J1, J2) := splitViaIndep I;
     if class J2 === Ideal and J2 != 1 then (
	      (equidims2, J) := splitViaIndeps J2;
	      return ({J1} | equidims2, J);
	      );
     ({J1}, J2)
     )
-- Needs test

splitViaIndepNEWER = method()
splitViaIndepNEWER Ideal := (I) -> (
-- documentation needed
     indeps := independentSets I;
     indep := support first indeps;
     << "Number of independent sets: " << #indeps << endl;
     << "  Choosing: " << indep << endl;
     (S, SF) := makeFiberRings indep;
     IS := sub(I, S);
     gens gb IS;
     (ISF, coeffs) := minimalizeOverFrac(IS, SF);
     G := (factors product coeffs)/last//product;
     << "  the factors of the flattener: " << netList((factors G)/last) << endl;
     G = sub(G,ring I);
     J1 := saturate(I, G);
     J2 := I: J1;
     if intersect(J2,J1) == I then (
	  << "  Yes! Quotient method split the ideal" << endl;
	  return ((J1, indep, ISF),J2);
	  );
     << "  No! Need to manually determine the f^ell from lecture" << endl;
     ((J1, indep, ISF), G)
     )

splitViaIndepsNEWER = (I) -> (
     (J1, J2) := splitViaIndepNEWER I;
     if class J2 === Ideal and J2 != 1 then (
	      (equidims2, J) := splitViaIndepsNEWER J2;
	      return ({J1} | equidims2, J);
	      );
     ({J1}, J2)
     )
-- Needs test

splitEquidimFactors = (I) -> (
     -- idea: loop through the gens of I.
     --   if any factors, then try to split the ideal.
     --     if it splits, call recursively on each elem of split, and return joined list.
     --     if not, continue to the next generator
     -- at the end, if it doesn't split, return {I}
     I1 := ideal gens gb I;
     for i from 0 to numgens I1 - 1 do (
	  facs := factors I1_i;
	  if #facs > 1 then (
	       split := splitUsingQuotientsBy(I, facs#0#1);
	       if split =!= null then return(split//toList/splitEquidimFactors//flatten);
	       )
	  );
     {I}
     )
-- needs test

splitEquidimFactorsNEWER = (I,indep,ISF) -> (
     -- idea: loop through the gens of I.
     --   if any factors, then try to split the ideal.
     --     if it splits, call recursively on each elem of split, and return joined list.
     --     if not, continue to the next generator
     -- at the end, if it doesn't split, return {I}
     I1 := ideal gens gb I;
     for i from 0 to numgens I1 - 1 do (
	  facs := factors I1_i;
	  if #facs > 1 then (
	       split := splitUsingQuotientsBy(I, facs#0#1);
	       if split =!= null then return(split//toList/splitEquidimFactors//flatten);
	       )
	  );
     {I}
     )

findPurePowers = method()
findPurePowers Ideal := (IF) -> (
     -- IF is a reduced lex GB for I k(indep)[fiber]
     -- returns the list of n (= #fiber) polynomials, s.t. i-th one has lead term x_i^(a_i),
     --   where x_i are the fiber variables
     select(IF_*, f -> # support leadTerm f == 1)
     )

findNonlinearPurePowers = method()
findNonlinearPurePowers Ideal := (IF) -> (
     -- IF is a reduced lex GB for I k(indep)[fiber]
     -- returns the list of n (= #fiber) polynomials, s.t. i-th one has lead term x_i^(a_i),
     --   where x_i are the fiber variables, and a_i > 1
     select(IF_*, f -> (
	       t := leadTerm f;
	       s := support t;
	       #s === 1 and s#0 != t))
     )

-- Below, IF is a reduced lex GB for I k(indep)[fiber]
-- This function factors the terms that are not linear in a GB for IF and splits the ideal by those factors
splitPurePowers = method()
splitPurePowers Ideal := (IF) -> (
     L := findPurePowers IF;
     for f in L do (
	  facs := factors f;
	  if #facs == 1 and facs#0#0 == 1 then continue;
	  return flatten for fac in facs list splitPurePowers (ideal gens gb ((ideal fac#1) + IF));
	  );
     {IF}
     )
-- needs test

-- Below, IF is a reduced lex GB for I k(indep)[fiber]
-- In this function, the polynomials themselves are irreducible over the field if not considered as a whole,
-- but one can see some linear terms that split if we change coordinates.
-- A good example is if the ideal (over QQ) has r^2-3 and x^2-3y^2 in it.  This should
-- split as r^2-3,x+ry and r^2-3, x-ry.
purePowerCoordinateChange = method()
purePowerCoordinateChange Ideal := (IF) -> (
     purePowers := findNonlinearPurePowers IF;
     otherGens := toList((set IF_*) - (set purePowers));
     J := ideal purePowers;
     L := ideal (J_* / numerator);
     varsList := purePowers / leadTerm / support // flatten;
     F := sum apply(drop(varsList,1), x -> (1 + random 10) * x);
     J1 := sub(J, varsList#0 => varsList#0 + F);
     L1 := ideal(J1_*/numerator);
     varsList = apply(varsList, f -> sub(f, ring L1));
     facs := factors (eliminate(L1, drop(varsList,1)))_0;
     F = sub(F,ring L1);
     facs1 := apply(facs, (mult,h) -> (mult,sub(h, varsList#0 => varsList#0 - F)));
     if #facs1 == 1 and facs1#0#0 == 1 then {IF}
     else for fac in facs1 list (
     	  G := fac#1 % L;
	  C := ideal first minimalizeOverFrac((ideal G) + L, ring J);
	  ideal gens gb (C + ideal otherGens)
       )
     )
TEST ///
  restart
  debug loadPackage "PD"
  
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  J = ideal(r^2-3,
       g_3*r+e_1,
       e_1*r+3*g_3,
       e_4*g_3-e_3*g_4,
       g_2^2-3*g_3^2,
       e_3*g_2-e_2*g_3,
       e_2*g_2-3*e_3*g_3,
       e_1*g_1+4*e_3*g_3+e_4*g_4,
       2*e_4^2+9*g_1^2+24*g_3^2+9*g_4^2,
       4*e_3^2-3*g_1^2-6*g_3^2-3*g_4^2,
       4*e_2^2-9*g_1^2-18*g_3^2-9*g_4^2,
       e_1^2-3*g_3^2,
       e_4*g_2*r-e_2*g_4*r,
       g_1^2*r+g_4^2*r+2*e_3*g_1-4*e_1*g_3,e_4*g_1*r+2*e_3*e_4+3*g_3*g_4,2*e_3*g_1*r+3*g_1^2+12*g_3^2+3*g_4^2,2*e_3*e_4*r+3*e_4*g_1-3*e_1*g_4,2*e_2*e_3*r+3*e_2*g_1-3*e_1*g_2,6*e_3*g_1*g_3-4*e_1*g_3^2+e_4*g_1*g_4-e_1*g_4^2,6*e_2*e_3*g_3+3*g_2*g_3^2+e_2*e_4*g_4,e_1*e_4*g_2-e_1*e_2*g_4,2*e_1*e_3*e_4-3*e_3*g_1*g_4+3*e_1*g_3*g_4,2*e_1*e_2*e_4-3*e_2*g_1*g_4+3*e_1*g_2*g_4,2*e_1*e_2*e_3-3*e_2*g_1*g_3+3*e_1*g_2*g_3)
  JE = extendIdeal J
  
  findNonlinearPurePowers JE
  gbTrace = 3
  newJEs = purePowerCoordinateChange JE
///
----------------------------------------------------
-- "Remove" polynomials which occur as variables ---
----------------------------------------------------
-- Input: ideal I in a polynomial ring
-- Output: (J:Ideal, F:RingMap)
--   where F:R-->R is a ring map s.t. F J == I
--   and J has the polynomials defining a variable x as linear, has  the corresp poly = x.
simplifyIdeal = method()
simplifyIdeal Ideal := (originalI) -> (
     -- input: ideal I in a polynomial ring R
     -- output: (J, phi), J is an ideal in the same ring
     --                   phi : R --> R
     -- such that the only generators of J which are linear in a variable are themselves 
     -- variables, and phi J == I
     I := originalI;
     R := ring I;
     H := new MutableList from gens R;
     for x in gens R do (
	  k := position(I_*, f -> first degree diff(x,f) == 0);
	  if k === null then continue;
	  c := leadCoefficient diff(x,I_k);
	  g := I_k - c*x;  
	  -- at this point f = I_k = c*x + g, and g does not involve x.
	  --  (and c is a constant)
	  p := - 1/c * g;
	  I = ideal(x) + ideal compress sub(gens I, x=>p);
	  H#(index x) = x - p;
	  );
     (ideal compress gens I, map(R,R,toList H))
     )

TEST ///
  restart
  debug loadPackage "PrimDecomposition"
  R = ZZ/32003[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z]
  I = ideal"
    -ab-ad+2ah,
    ad-bd-cf-2ah+2bh+2ck,
    ab-ad-2bh+2dh-2ck+2fk+2gl,
    ac-2cs-at+2bt,
    ac-cs-2at+bt,
    -d-3s+4u,
    -f-3t+4v,
    -g+4w,
    -a+2x,
    -b2-c2+2bx+2cy,
    -d2-f2-g2+2dx+2fy+2gz"
  (J,phi) = simplifyIdeal I
  J1 = ideal gens phi J
  assert(I == J1)
  codim I
  time CJ = splitEquidimFactors J;
  time CI = splitEquidimFactors I;
  assert(intersect CJ == J)
  assert(intersect CI == I)
  ans1 = CJ/(i -> flatten entries gens gb  phi i)
  ans2 = CI/(i -> flatten entries gens gb i)
  assert(ans1 === ans2)
///

-------------------------------------
-- Factorization over a tower -------
-------------------------------------
factorize = method()
factorize(RingElement, Ideal) := (F, I) -> (
     -- factor F mod I
     -- I = (g_(n-1), g_(n-2), ..., g_0) zero dimensional prime over a fraction field, in lex order
     -- F should be a polynomial in a ring R/I, univariate or multivariate?, monic?
     --
     -- steps:
     --  make change of basis xn = xn + c * x(n-1) + ... c' * x(0)
     --  find gb of (phi I, phi F)
     --    this shoud be of the form: xn^r + ..., rest of variables occur linearly
     --  factor this new poly (in one variable).
     --  if it doesn't factor over kk, then F is likely irreducible
     --  if it does, then F is NOT irreducible:
     --    in this case, for each factor, map back, and get gens gb(I + (factor))
     --    get a gb of form: original I, and one new element, the desired factor.
     
     --
     -- ASSUMPTIONS:
     --  1. SF = ring I was made with makeFiberRing
     --  2. F is a univariate polynomial in x over subring generated by variables appearing in I, where
     --     x is a variable occuring in SF
     --  3. F is monic in this variable (we will try to remove this requirement)
     --
     R := ring I;
     xset := toList(set gens ring F - set support I);
     if #xset > 1 then error "expected a univariate polynomial";
     r := last gens R;
     i := index first xset;
     J := I + ideal F;
     randomElem := sum for j from index first xset to numgens R - 2 list (random 10 * R_j);
     phi := map(R,R, {r => r + randomElem});
     phiInverse := map(R,R, {r => r - randomElem});
     J1 := phi J;
     G := first flatten entries gens gb J1;
     facs := factors G;
     --error "debug me";
     if #facs == 1 and facs#0#0 == 1 then return {(1, F)};
     -- otherwise there is a factorization!
     apply(facs, (n,f) -> (
	       f1 := last flatten entries gens gb (J + ideal phiInverse f);
	       (n,f1)
	       ))
     )
-- needs test

beginDocumentation()

doc ///
Key
  PD
Headline
  Primary Decomposition
Description
  Text
    Describe the package here.
  Example
Caveat
SeeAlso
///

end

restart
loadPackage "PD"
