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

  leaves = flatten(equis/splitEquidimFactors)
  intersect leaves == I

  leaves = drop(leaves, 1)
  
  gbTrace = 3
  -- old way
  splitLeaves = leaves / extendIdeal / purePowerCoordinateChange // flatten / contractToPolynomialRing

  -- new way
  netList leaves
 

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

  -- start with J = ideal(J_0,J_1,J_2) above.
  -- Our plan: decompose this ideal
    splitLeaves = leaves / extendIdeal / purePowerCoordinateChange // flatten / contractToPolynomialRing
  J = leaves_0
  J1 = extendIdeal J -- fast
  J2 = purePowerCoordinateChange J1 -- this is the time-consuming step!
  J2/ contractToPolynomialRing -- fast

  J
  A = ZZ/32003[g_2,g_3,r,g_1,g_4,MonomialOrder=>Lex]
  J1 = sub(J,A)
  J1 = sub(J1, {r=>r-g_3-g_2})
  eliminate(J1, {g_2, g_3})  
  R = ring J1
  A = (ZZ/32003)(monoid R)
  B = (ZZ/32003)[gens coefficientRing R]
  C = frac B
  D = C (monoid R)
  describe D
  describe C
  describe B
  J1 = sub(J1, D)

  restart
  load "ModularGCD.m2"
  kk = ZZ/32003
  A = kk[g_2, g_3, r, g_1, g_4, MonomialOrder => Lex]
  B = A[x]
  F = x^8+3*x^6*g_1^2+(9/16)*x^4*g_1^4+4*x^6*g_4^2+5*x^4*g_1^2*g_4^2+(3/4)*x^2*g_1^4*g_4^2+(9/2)*x^4*g_4^4+(7/4)*x^2*g_1^2*g_4^4+(1/16)*g_1^4*g_4^4+x^2*g_4^6+(1/8)*g_1^2*g_4^6+(1/16)*g_4^8-9*x^5*g_1^2-12*x^5*g_4^2-24*x^3*g_1^2*g_4^2-(9/4)*x*g_1^4*g_4^2-24*x^3*g_4^4-(21/4)*x*g_1^2*g_4^4-3*x*g_4^6-12*x^6-9*x^4*g_1^2-(27/8)*x^2*g_1^4-12*x^4*g_4^2+54*x^2*g_1^2*g_4^2+(9/4)*g_1^4*g_4^2+57*x^2*g_4^4+(21/4)*g_1^2*g_4^4+3*g_4^6+54*x^3*g_1^2+72*x^3*g_4^2-72*x*g_1^2*g_4^2-72*x*g_4^4+54*x^4-27*x^2*g_1^2+(81/16)*g_1^4-36*x^2*g_4^2+45*g_1^2*g_4^2+(81/2)*g_4^4-81*x*g_1^2-108*x*g_4^2-108*x^2+81*g_1^2+108*g_4^2+81   
  F = sub(F,{x => g_2+g_3+r})
  G = g_2^2-3*g_3^2
  m1 = r^2-3
  m2 = g_3^4+((3*g_1^2+4*g_4^2)/8)*g_3^2+(g_1^2*g_4^2+g_4^4)/16
  L = ideal(F,G,m1,m2)
  time gens gb L;
  L' = L + ideal(g_1 - random kk, g_4 - random kk)
  time gens gb L';
  kk = coefficientRing A;
  B = kk[g_2, g_3, r, MonomialOrder=>Lex]
  eval1 = map(B,A,vars B | matrix{{random kk, random kk}})
  eval1 F
  eval1 G
  needs "/Users/mike/src/M2-dev/mike/integral-closure-packages/ModularGCD.m2"
  debug ModularGCD
  modpGCD(eval1 F, eval1 G, {eval1 m1, eval1 m2})

  use A
  eval1 = map(A,A,{g_2, g_3, r, g_1, random kk})
  L1 = eval1 L


  -- goal 1: via CRA and rat recon, determine lexGB of L1 (over kk(g_1)[g_2, g_3, r])
  rand = () -> (a := random kk; (map(A,A,{g_2, g_3, r, a, 0_A}), a))

  (phi1, p1) = rand()
  G1 = flatten entries gens gb phi1 L1       

  polyCRA((g1,m1),(g2,m2),t,32003)
  polyRationalReconstruction(g1,t,m1,32003)
  
  (phi2, p2) = rand()
  G2 = flatten entries gens gb phi2 L1       

  (phi3, p3) = rand()
  G3 = flatten entries gens gb phi3 L1 

  (phi4, p4) = rand()
  G4 = flatten entries gens gb phi4 L1 

  -- loop this!
  (H1,e1) = polyCRA((G1_1,g_1-p1),(G2_1,g_1-p2), g_1, 32003)  
  (H2,e2) = polyCRA((G3_1,g_1-p3),(H1,e1), g_1, 32003)  
  (H3,e3) = polyCRA((G4_1,g_1-p4),(H2,e2), g_1, 32003)  
  polyRationalReconstruction(H3,g_1,e3,32003) 

  B = kk[g_2, g_3, r, MonomialOrder=>Lex]
  eval1 = map(B,A,vars B | matrix{{random kk, random kk}})
  gens gb eval1 L

  eval2 = map(B,A,vars B | matrix{{random kk, random kk}})
  gens gb eval2 L

  


