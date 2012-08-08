needsPackage "ModularGCD"

gbRationalReconstruction = method()
gbRationalReconstruction (Ideal,List) := (L, paramList) -> (
  A := ring L;
  kk := coefficientRing A;
  if #paramList === 0 then return (flatten entries gens gb L,1);
  
  evalVar := first paramList;
  paramList = drop(paramList,1);
  ratResult := null;
  (loopG,loopE) := (null,null);
  loopCount := 0;
  (G,newTotal) := (null,totalLoopCount);
  usedCoords := set {};
  totalLoops := 0;
  while ratResult === null do (
    loopCount = loopCount+1;
    -- this next three lines ensure we do not pick the same specialization twice for a coordinate
    a := random kk;
    while member(a,usedCoords) do a = random kk;
    usedCoords = usedCoords + set {a};
    randMap := map(A,A,{evalVar => a});
    (G,subLoops) := gbRationalReconstruction(randMap L,paramList);
    totalLoops = totalLoops + subLoops;
    if loopG === null then (loopG, loopE) = (G,evalVar-a) else (
       H := for i from 0 to #G-1 list (
          polyCRA((loopG#i,loopE), (G#i,evalVar-a), evalVar, char kk)
       );
       loopG = H / first;
       loopE = last first H;
    );
    rrLoopG := for i from 0 to #loopG-1 list (
       retVal := polyRationalReconstruction(loopG#i,evalVar,loopE,char kk);
       if retVal === null then break;
       first retVal
    );
    if #rrLoopG == #loopG then (
	 << "(totalLoopCount,loopCount,paramList) : " << (totalLoops,loopCount,#paramList) << endl;
	 return (rrLoopG,totalLoops);
    )
  );
)  

end

--- baby example
restart
  load "gbRatRecon.m2"
  kk = ZZ/32003
  A = kk[g_2, g_3, r, g_1, g_4, MonomialOrder => Lex]
  B = A[x]
  F = x^8+3*x^6*g_1^2+(9/16)*x^4*g_1^4+4*x^6*g_4^2+5*x^4*g_1^2*g_4^2+(3/4)*x^2*g_1^4*g_4^2+(9/2)*x^4*g_4^4+(7/4)*x^2*g_1^2*g_4^4+(1/16)*g_1^4*g_4^4+x^2*g_4^6+(1/8)*g_1^2*g_4^6+(1/16)*g_4^8-9*x^5*g_1^2-12*x^5*g_4^2-24*x^3*g_1^2*g_4^2-(9/4)*x*g_1^4*g_4^2-24*x^3*g_4^4-(21/4)*x*g_1^2*g_4^4-3*x*g_4^6-12*x^6-9*x^4*g_1^2-(27/8)*x^2*g_1^4-12*x^4*g_4^2+54*x^2*g_1^2*g_4^2+(9/4)*g_1^4*g_4^2+57*x^2*g_4^4+(21/4)*g_1^2*g_4^4+3*g_4^6+54*x^3*g_1^2+72*x^3*g_4^2-72*x*g_1^2*g_4^2-72*x*g_4^4+54*x^4-27*x^2*g_1^2+(81/16)*g_1^4-36*x^2*g_4^2+45*g_1^2*g_4^2+(81/2)*g_4^4-81*x*g_1^2-108*x*g_4^2-108*x^2+81*g_1^2+108*g_4^2+81   
  F = sub(F,{x => g_2+g_3+r})
  G = g_2^2-3*g_3^2
  m1 = r^2-3
  m2 = g_3^4+((3*g_1^2+4*g_4^2)/8)*g_3^2+(g_1^2*g_4^2+g_4^4)/16
  L = ideal(F,G,m1,m2)

  -- single parameter
  eval1 = map(A,A,{g_2, g_3, r, g_1, random kk})
  L1 = eval1 L
  gbRationalReconstruction(L1,{g_1})

  -- try two parameters
  time gbRationalReconstruction(L,{g_4,g_1})
---------------

--- bigger example
restart
load "gbRatRecon.m2"
load "PD.m2"
debug PD
R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l, MonomialOrder=>Lex]
I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
independentSet = support first independentSets I
time gbRationalReconstruction(I,independentSet)

-- cut down on some variables
S = ZZ/32003[a,b,c,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,random kk, random kk, random kk, g,h,j,k,l}})
independentSet = support first independentSets phi I
time gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works!
  
-- cut down on fewer variables
S = ZZ/32003[a,b,c,d,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d, random kk, random kk, g,h,j,k,l}})
independentSet = support first independentSets phi I
time ratGB = gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works (now with denominators)!

-- with many variables in the independent set, the number of evaluations grow exponentially...

-- cut down on still fewer variables
S = ZZ/32003[a,b,c,d,e,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d,e, random kk, g,h,j,k,l}})
independentSet = support first independentSets phi I
time ratGB = gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works!

