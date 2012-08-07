-- from lecture5.m2 from Stillman's Atlanta lectures, June 2012.

restart
debug loadPackage("PD", Reload=>true)

  -- make ideal
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  I = ideal(r^2-3,e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
  see I
  codim I -- 6
  degree I -- 8

  equis = first splitViaIndeps I;  
  equis/codim
  equis/degree  

  equis = first splitViaIndepsNEWER I;
  equis/first/codim
  equis/first/degree  

  leaves = flatten(equis/splitEquidimFactorsNEWER)
  intersect leaves == I

  leaves = drop(leaves, 1)
  
  gbTrace = 3
  splitLeaves = leaves / extendIdeal / purePowerCoordinateChange // flatten / contractToPolynomialRing

  radI = trim intersect apply(splitLeaves, C -> sub(C,R));
  apply(#(radI_*), i -> radicalContainment(radI_i,I))
  
  -- note: we are just finding minimal primes, so the intersection will not be the original ideal
  apply(#leaves, j -> (
	    A := leaves_j;
            B := apply(splitLeaves_j, C -> sub(contractToPolynomialRing C, R));
            A == intersect B))
  
  J = extendIdeal(leaves_0) -- splits at least into 2 primes (8 points over CC)
  J = ideal(J_0,J_1,J_2)

  purePowers = findPurePowers J
  varsList = purePowers / leadTerm / support // flatten
  J1 = sub(J, (first varsList) => sum varsList)
  L1 = ideal(J1_*/numerator)
  varsList = apply(varsList, f -> sub(f, ring L1))
  facs = factors (eliminate(L1, drop(varsList,1)))_0
  facs1 = apply(facs, (mult,h) -> (mult,sub(h, (first varsList) => (first varsList) - sum drop(varsList,1))))
       
  L = ideal(J_*/numerator)
  use ring J
  J1 = sub(J, r=>r+g_2+g_3)
  L1 = ideal(J1_*/numerator)
  use ring L1
  facs = factors (eliminate(L1, {g_2,g_3}))_0
  facs = apply(facs, (mult,h) -> (mult,sub(h,r=>r-g_2-g_3)))
  
  G = facs1_0_1 % L
  sub(L,R) + ideal (sub(G,R))
  extendIdeal oo
  contractToPolynomialRing oo

 B = matrix basis comodule J
 multMap = (f, B, J) -> (
      -- J is a zero-diml ideal in a poly ring R = kk[vars]
      -- f is the element in R/J
      -- B is a basis of R/J (a matrix)
      -- returns: matrix: kk^#B --> kk^B
      R := ring J;
      kk := coefficientRing R;
      cols := (f * B) % J;
      (mons,cfs) := coefficients(cols, Monomials=>B);
      cfs
      )

  use ring B
  F = r+g_2+g_3
  M = multMap(F, B, J)
  S1 = (ring M)[x]
  sub(M,S1) - x
  D = det oo
  S2 = QQ[x,gens coefficientRing ring J]
  D = sub(D,S2)
  facs = factors D
  use ring M
  phi = map(ring B, S2, flatten {F, gens coefficientRing ring B})
  (phi facs_0_1) % J
  sub(facs_0_1, {x => F, appl)

  -- easiest here would be to use gcd over algebraic function field
