newPackage( "PosChar",
Version => "0.1a", Date => "October 18th, 2013", Authors => {
     {Name => "Mordechai Katzman",
     Email=> "m.katzman@sheffield.ac.uk",
     HomePage=> "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email=> "smalec@gsu.edu"
     },
     {Name => "Karl Schwede",
     Email => "schwede@math.psu.edu",
     HomePage => "http://math.psu.edu/schwede/"
     },
     {Name=> "Emily Witt",
     Email=> "ewitt@umn.edu",
     HomePage => "http://math.umn.edu/~ewitt/"
     }
},
Headline => "A package for calculations in positive characteristic", DebuggingMode => true, Reload => true )
export{
	 "aPower",
	 "ascendIdeal", 
	 "ascendIdealSafe",
	 "basePExp",
  	 "basePExpMaxE",
  	 "BinomialCheck",
  	 "binomialFPT",
  	 "carryTest",
     "digit", 	 
     "denom",
  	 "DiagonalCheck", 
  	 "diagonalFPT",
  	 "divideFraction",
  	 "estFPT",
     "ethRoot",
     "ethRootSafe",	
     "fastExp",
     "FinalCheck",
     "findQGorGen",
     "firstCarry", 
     "FPTApproxList",     
     "frobeniusPower",
     "fSig",
     "guessFPT",
	"HSL",
     "isBinomial",
     "isDiagonal",
     "isFJumpingNumberPoly",
     "isFPTPoly",
     "isFRegularPoly",
     "isFRegularQGor",
     "isSharplyFPurePoly",
     "MultiThread",
     "nu",
     "nuList",
     "NuCheck",
     "Origin",
     "OutputRange",
     "sigmaAOverPEMinus1Poly", 
     "sigmaQGorAmb", 
     "sigmaAOverPEMinus1QGor",      
     "tauPoly",
     "tauAOverPEMinus1Poly",
     "tauGor",
     "tauGorAmb",
     "tauQGor",
     "tauQGorAmb",
     "truncation",
     "truncationBaseP"
}
--This file has "finished" functions from the Macaulay2 workshop at Wake Forest
--August 2012.  Sara Malec, Karl Schwede and Emily Witt contributed to it.
--Some functions, are based on code written by Eric Canton and Moty Katzman


----------------------------------------------------------------
--************************************************************--
--Functions for doing particular factorizations with numbers. --
--************************************************************--
----------------------------------------------------------------

denom = method(); --Finds the denominator of a rational number or integer
denom QQ := x -> denominator x;
denom ZZ := x -> 1;

num = method(); --Finds the numerator of a rational number or integer
num QQ := x -> numerator x;
num ZZ := x -> x;

fracPart = (x) -> (x - floor(x)) --Finds the fractional part of a number

--Given a vector w={x,y}, x and y rational in [0,1], returns a number of digits 
--such that it suffices to check to see if x and y add without carrying in base p
aPower = (x,p) -> --find the largest power of p dividing x
(
a:=1; while fracPart(denom(x)/p^a)==0 do a = a+1;
a-1
)
     
-- This function takes in a fraction t and a prime p and spits out a list
-- {a,b,c}, where t = (a/p^b)(1/(p^c-1))
-- if c = 0, then this means that t = (a/p^b)
divideFraction = (t1,pp) -> (
     a := num t1; -- finding a is easy, for now
     b := aPower(t1,pp); -- finding b is easy based upon aPower (written by Emily)
     temp := denom(t1*pp^b); --find the p^c-1 part of the denominator
     pow := 0; --we will look around looking for the power of pp that is 1 mod temp. 
     done := false; --when we found the power, this is set to true.
     if (temp == 1) then done = true; --if there is nothing to do, do nothing.
     while (done==false)  do (
          pow = pow + 1;
	  if (pp^pow % temp == 1) then done = true
     );
     c := pow; --we found c, now we return the list
     if (c > 0) then a = lift(a*(pp^c-1)/temp, ZZ); --after we fix a
     {a,b,c}
)

--Finds the a/pp^e1 nearest t1 from above
findNearPthPowerAbove = (t1, pp, e1) -> (
     ceiling(t1*pp^e1)/pp^e1
)

--Finds the a/pp^e1 nearest t1 from below
findNearPthPowerBelow = (t1, pp, e1) -> (
     floor(t1*pp^e1)/pp^e1
)

--Returns the digits in nn which are nonzero in binary 
--for example, 5 in binary is 101, so this would return {0,2}
--the second term tells me where to start the count, so passing
--5,0 gives {0,2} but 5,1 is sent to {1,3}.  i should be
--used only for recursive purposes
getNonzeroBinaryDigits = (nn, i) -> (
--    error "breakme";
    halfsies := nn//2;
    val1 := nn%2;
    val2 := false; 
    if (halfsies > 0) then val2 = (getNonzeroBinaryDigits(nn//2,i+1));
    if ( (val1 != 0) and (not (val2 === false))) then (
	 flatten {i, val2}
    )
    else if (val1 != 0) then (
	 {i}
    )
    else if ( not (val2 === false)) then (
	 flatten {val2}
    )
    else(
	 false
    )
)

--Returns the entries of myList specified by entryList
--For example, ( {1,2,3}, {0,2}) is sent to {1,3}
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)

--Returns the power set of a given list, except it leaves out
--the emptyset.  
--For example {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)

--This turns a number into a list of factors with repeats
--For example, 12 becomes (2,2,3)
numberToPrimeFactorList = (nn)->(
     prod := factor nn;
     flatten (apply(#prod, i -> toList(((prod#(i))#1):((prod#(i))#0)) ))
)

--Returns a list of all proper factors of nn, for use with sieving...
getFactorList = (nn) ->(
     if (nn < 1) then error "getFactorList: expected an integer greater than 1.";
     powSet := nontrivialPowerSet(numberToPrimeFactorList(nn)); 
     toList ( set apply(#powSet, i->product(powSet#i)) )
)

--This function finds rational numbers in the range of the interval
--with the given denominator
findNumberBetweenWithDenom = (myInterv, myDenom)->(
     upperBound := floor((myInterv#1)*myDenom)/myDenom; 
          --finds the number with denominator myDenom less than the upper 
	  --bound of myInterv
     lowerBound := ceiling((myInterv#0)*myDenom)/myDenom; 
          --finds the number with denominator myDenom greater than the lower
	  -- bound of myInterv
     if (upperBound >= lowerBound) then (
	  --first we check whether there is anything to search for
	  apply( 1+numerator((upperBound-lowerBound)*myDenom), i-> lowerBound+(i/myDenom) )
     )
     else(
	  {}
     )
)

--This function finds rational numbers in the range of 
--the interval; the max denominator allowed is listed. 
findNumberBetween = (myInterv, maxDenom)->(
     divisionChecks :=  new MutableList from maxDenom:true; 
         -- creates a list with maxDenom elements all set to true.
     outList := {};
     i := maxDenom;
     while (i > 0) do (
	  if ((divisionChecks#(i-1)) == true) then --if we need to do a computation..
	      outList = join(outList,findNumberBetweenWithDenom(myInterv, i));
	  factorList := getFactorList(i);
     	  apply(#factorList, j-> (divisionChecks#( (factorList#j)-1) = false) );
	  i = i - 1;
     );
     sort(toList set outList)
)


---------------------------------------------------------------
--***********************************************************--
--Basic functions for computing powers of elements in        --
--characteristic p>0.                                        --
--***********************************************************--
---------------------------------------------------------------

--Computes the non-terminating base p expansion of an integer
basePExp = (N,p) ->
(
e:=1; while p^e<=N do e = e+1;
e = e-1;
E:=new MutableList;
a:=1; while e>=0 do 
(
     while a*p^e<=N do a=a+1;
     E#e = a-1;
     N = N - (a-1)*p^e;
     a=1;
     e=e-1;
);
new List from E
)

--Computes the non-terminating base p expansion of an integer 
--from digits zero to e-1 (little-endian first)
basePExpMaxE = (N,p,e1) ->
(
e:=e1-1;
E:=new MutableList;
a:=1; while e>=0 do 
(
     while a*p^e<=N do a=a+1;
     E#e = a-1;
     N = N - (a-1)*p^e;
     a=1;
     e=e-1;
);
new List from E
)

--Computes powers of elements in char p>0, using that Frobenius
--is an endomorphism
fastExp = (f,N) ->
(
     p:=char ring f;
     E:=basePExp(N,char ring f);
     product(apply(#E, e -> (sum(apply(terms f, g->g^(p^e))))^(E#e) ))
)


---------------------------------------------------------------
--***********************************************************--
--Functions for computing \nu_I(p^e), \nu_f(p^e), and using  --
--these to compute estimates of FPTs.                        --
--***********************************************************--
---------------------------------------------------------------

--Lists \nu_I(p^d) for d = 1,...,e 
nuList = method();
nuList (Ideal,ZZ) := (I,e) ->
(
     p := char ring I;
     m := ideal(first entries vars ring I); 
     L := new MutableList;
     N:=0;
     J:=I;
     for d from 1 to e do 
     (	  
	  J = ideal(apply(first entries gens I, g->fastExp(g, N)));
	  N=N+1;
	  while isSubset(I*J, frobeniusPower(m,d))==false do (N = N+1; J = I*J);
     	  L#(d-1) = N-1;
	  N = p*(N-1)
     );
     L
)
nuList(RingElement,ZZ) := (f,e) -> nuList(ideal(f),e)

--Gives \nu_I(p^e)
nu = method();
nu(Ideal,ZZ) := (I,e) -> (nuList(I,e))#(e-1)
nu(RingElement, ZZ) := (f,e) -> nu(ideal(f),e)

--Gives a list of \nu_I(p^d)/p^d for d=1,...,e
FPTApproxList = method();
FPTApproxList (Ideal,ZZ) := (I,e) ->
(
     p := char ring I;
     apply(#nuList(I,e), i->((nuList(I,e))#i)/p^(i+1)) 
)
FPTApproxList (RingElement,ZZ) := (f,e) -> FPTApproxList(ideal(f),e)


---------------------------------------------------------------
--***********************************************************--
--Basic functions for Frobenius powers of ideals and related --
--constructions (colons).                                    --
--***********************************************************--
---------------------------------------------------------------
 
--The following raises an ideal to a Frobenius power; it was written by Moty Katzman
frobeniusPower=method()

frobeniusPower(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);

-- This function computes the element in the ambient ring S of R=S/I such that
-- I^{[p^e]}:I = (f) + I^{[p^e]}
-- If there is no such unique element, the function returns zero

findQGorGen=method();
findQGorGen (Ring,ZZ) := (Rk,ek) -> (
     Sk := ambient Rk; -- the ambient ring
     Ik := ideal Rk; -- the defining ideal
     pp := char Sk; --the characteristic
     Ikpp := frobeniusPower(Ik,ek);
     
     J1 := trim (Ikpp : Ik); --compute the colon
     Tk := Sk/Ikpp; --determine the ideal in 
     
     J2 := trim sub(J1, Tk);
     
     Lk := first entries gens J2;
     
     nk := #Lk;
     val := 0_Sk;
     
     if (nk != 1) then (
	  error "findGorGen: this ring does not appear to be (Q-)Gorenstein, or
	   you might need to work on a smaller chart.  Or the index may not divide p^e-1
	   for the e you have selected.";
     )
     else (
	  val = lift(Lk#0, Sk);
     );    
     val 
)
findQGorGen(Ring) := (R2) -> ( findQGorGen(R2, 1) )


---------------------------------------------------------------------
--*****************************************************************--
--Functions for computing the F-pure threshold of a diagonal       --
--or binomial hypersurface using the algorithms of Daniel Hernandez--
--(written by E. Witt)                                             --                      
--*****************************************************************--
---------------------------------------------------------------------

--Gives the e-th digit of the non-terminating base p expansion of x in [0,1] 
digit = (e, x, p) -> 
(
     y := 0;
     if fracPart(p^e*x) != 0 then y = floor(p^e*x) - p*floor(p^(e-1)*x);
     if fracPart(p^e*x) == 0 then y = floor(p^e*x) - p*floor(p^(e-1)*x) - 1;
     if fracPart(p^(e-1)*x) == 0 then y = p-1;
     y
)

--Gives the e-th truncation of the non-terminating base p expansion of x in [0,1] 
--as a fraction
truncation = (e,x,p) -> 
(
     y:=0; 
     for i from 1 to e do y = y + digit(i,x,p)/p^i;
     y
)

--Gives the first e digits of the non-terminating base p expansion of x in [0,1]
--as a list
truncationBaseP = (e,x,p) -> 
(
     L := new MutableList;
     for i from 0 to e-1 do L#i = digit(i+1,x,p);
     L
)

--Given a rational number x, if a is the power of p dividing its denomiator, 
--finds an integer b so that p^a(p^b-1)*a is an integer
bPower = (n,p) ->
(
     if aPower(n,p)>0 then n = n*p^(aPower(n,p));
     denom(n)
)

--Given a vector w={x,y}, x and y rational in [0,1], returns a number of digits 
--such that it suffices to check to see if x and y add without carrying in base p
carryTest = (w,p) ->
(
     c := 0; for i from 0 to #w-1 do c = max(c, aPower(w#i, p));
     d := 1; for j from 0 to #w-1 do if bPower(w#j, p)!=0 then d = lcm(d, bPower(w#j, p));
     c+d+1
)

--Given a vector w={x,y} of rational integers in [0,1], returns the first spot 
--e where the x and y carry in base p; i.e., 
--(the e-th digit of x)+(the e-th digit of y) >= p
firstCarry = (w,p) ->
(     
    i:=0;
    d:=0;
    carry:=0;
    zeroTest := false;
    for j from 0 to #w-1 do if w#j == 0 then zeroTest=true;
    if zeroTest == true then carry = -1 else
     (
	       i = 0; while d < p and i < carryTest(w,p) do 
	       (
	       	    i = i + 1;
	       	    d = 0; for j from 0 to #w-1 do  d = d + digit(i,w#j,p);
	   	);
      	       if i == carryTest(w,p) then i = -1;
      	       carry = i;
      );
      carry
)

--Given a vector w, returns a vector of the reciprocals of the entries of w
reciprocal = w ->
(
     v := new MutableList from w;
     for c from 0 to #w-1 do v#c = 1/w#c;
     v
)

--Computes the F-pure threshold of a diagonal hypersurface 
--x_1^(a_1) + ... +x_n^(a_n) using Daniel Hernandez' algorithm
diagonalFPT = f ->
(
     p := char ring f;
     w := apply(terms f, g->first degree(g));
     y := 0; if firstCarry(reciprocal(w),p)==-1 then for i from 0 to #w-1 do y = y + 1/w#i else
     (
	  x := 0; for c from 0 to #w-1 do x = x + truncation(firstCarry(reciprocal(w),p)-1, 1/w#c, p); 
	  y = x+1/p^(firstCarry(reciprocal(w),p)-1);
     );
     y
)

--Given a polynomial f, outputs a list of multi-degrees (under the usual grading)
--of f as lists
multiDegree = f ->
(
     variables := first entries vars ring f;
     apply(terms f, g -> apply(#variables, i ->degree(variables#i,g)))
)

--Determines whether a polynomial f is diagonal; i.e., of the form 
--x_1^(a_1)+...+x_n^(a_n) (up to renumbering variables)
isDiagonal = f ->
(
     d := multiDegree(f);
     alert1 := true;
     alert2 := true;
     for i from 0 to #d-1 do
     (
	  for j from 0 to #(d#0)-1 do
	  (
	       if (d#i)#j!=0 and alert1==false then alert2=false;
	       if (d#i)#j!=0 and alert1==true then alert1=false;
	  );
     alert1=true;
     );
     for j from 0 to #(d#0)-1 do
     (
	  for i from 0 to #d-1 do 
	  (
     	       if alert1==false and (d#i)#j!=0 then alert2=false;
     	       if alert1==true and (d#i)#j!=0 then alert1=false;
	  );
     alert1=true;
     );
     alert2
)

--Given input vectors v={a_1,...,a_n} and w={b_1,...,b_n}, gives the
--corresponding vectors that omit all a_i and b_i such that a_i=b_i
factorOutMonomial = (v,w) ->
(
     v1 := new MutableList;
     w1 := new MutableList;
     c := 0; i := 0; for i from 0 to #v-1 do (if v#i != w#i then (v1#c = v#i; w1#c = w#i; c = c+1; ); );
     (v1,w1)
)

--Given input vectors v={a_1,...,a_n} and w={b_1,...,b_n}, gives the
--vector of the a_i for which a_i=b_i
monomialFactor = (v,w) ->
(
     a := new MutableList;
     c := 0; i := 0; for i from 0 to #v-1 do (if v#i == w#i then (a#c = v#i; c = c+1; ); );
     a
)

--Given two vectors v={v0,v1} and w={w0,w1} in the real plane, finds 
--the intersection of the associated lines v0*x+w0*y=1 and v1*x+w1*y=1
twoIntersection = (v,w) ->
(
     if v#0*w#1-v#1*w#0 != 0 then 
     (
	  x := (w#1-w#0)/(v#0*w#1-v#1*w#0);
	  y := (v#0 - v#1)/(v#0*w#1-v#1*w#0);
	  P := {x,y};
     ) else P = {0,0};
P
)

--Given two vectors v={v0,...vn} and w={w0,...,wn}, list the 
--intersections of all lines vi*x+wi*y=1 and vj*x+wj*y=1
allIntersections = (v,w) ->
(
     L := new MutableList;
     c := 0;
     for i from 0 to #v-1 do
     (
	  for j from i+1 to #v-1 do 
     	  (
     	       if twoIntersection({v#i,v#j}, {w#i,w#j}) != {0,0} then 
     	       (
	  	    L#c = twoIntersection({v#i,v#j}, {w#i,w#j});
	  	    c = c+1;
     	       );
	  );
     );
     for i from 0 to #v-1 do
     (
	  if v#i !=0 then  
	  (
	       L#c = {1/(v#i), 0};
	       c = c + 1;
	  );
     );
     for i from 0 to #v-1 do
     (
	  if w#i !=0 then  
	  (
	       L#c = {0, 1/(w#i)};
	       c = c + 1;
	  );
     ); 
     K := new MutableList;
     c = 0; for i from 0 to #L-1 do
     (
	  if (L#i)#0 >= 0 and (L#i)#1 >=0 then (K#c = {(L#i)#0, (L#i)#1}; c = c+1);
     );
     K
)

--Given a point a=(x,y) in the real plane and two vectors v={v0,...,vn} and w={w0,...,wn}, checks whether a is in the polytope defined by the equations vi*x+wi*y<=1
isInPolytope = (a,v,w) ->
(
     alert := true;
     for i from 0 to #v-1 do
     (
	  if v#i*a#0 + w#i*a#1 > 1 then alert = false;
     );
     alert
)


--Given a point a=(x,y) in the real plane and two vectors
--v={v0,...,vn} and w={w0,...,wn}, checks whether a is in
--the polytope defined by the equations vi*x+wi*y<=1
isInInteriorPolytope = (a,v,w) ->
(
     alert := true;
     for i from 0 to #v-1 do
     (
	  if v#i*a#0 + w#i*a#1 >= 1 then alert = false;
     );
     alert
)

--Given two vectors v and w of the same length, outputs 
--a list of the defining vectors of the polytope as in isInPolytope
polytopeDefiningPoints = (v,w) ->
(
     L := allIntersections(v,w);
     K := new MutableList;
     c := 0;
     for j from 0 to #L-1 do
     (
	  if isInPolytope(L#j,v,w) == true then (K#c = {(L#j)#0, (L#j)#1}; c = c+1;)
     );
     K
)

--Given a list of coordinates in the real plane, 
--outputs the one with the largest coordinate sum
maxCoordinateSum = L ->
(
     K := new MutableList from {0,0};
     for i from 0 to #L-1 do if (L#i)#0 + (L#i)#1 > K#0 + K#1 then K = {(L#i)#0, (L#i)#1};
     K
)

--Finds the "delta" in Daniel Hernandez's algorithm
--for F-pure thresholds of binomials
dCalculation = (w,N,p) ->
(
     d := 0; for j from 0 to #w-1 do  d = d + digit(N+1,w#j,p);
     i := N; while d > p-2 do 
     (
	  d = 0; for j from 0 to #w-1 do  d = d + digit(i,w#j,p);
	  i = i - 1;
     );
     i + 1
)

--Given the "truncation" point (P1,P2) and two vectors 
--defining the binomial v and w, outputs the "epsilon" in 
--Daniel Hernandez's algorithm for F-thresholds of binomials
calculateEpsilon = (P1,P2,v,w) ->
(
     X := new MutableList;
     Y := new MutableList;
     c:=0; d := 0; for i from 0 to #v-1 do 
     (
	  if w#i != 0 then 
     	  (
	       X#c = (1 - (v#i)*(P2#0) - (w#i)*(P2#1))/(w#i);
	       c = c+1;
	  );
          if v#i != 0 then 
	  (
	       Y#d = (1 - (v#i)*(P1#0) - (w#i)*(P1#1))/(v#i);
	       d = d+1;
	  );
     );
     i:=0;
     epsilon:=0;
     if isInInteriorPolytope(P1,v,w)==false and isInInteriorPolytope(P2,v,w)==false then epsilon = -1 else
     (
	  if isInInteriorPolytope(P1,v,w)==false then for i from 0 to #v-1 do X#1 = 0;
	  if isInInteriorPolytope(P2,v,w)==false then for i from 0 to #v-1 do Y#1 = 0;
	  M := X#0; 
	  N := Y#0;
	  for i from 1 to #X-1 do M = min(M, X#i);
	  for j from 1 to #Y-1 do N = min(N, Y#j);
	  epsilon = max(M,N); 
     );
     epsilon
)

--Computes the FPT of a binomial, based on the work of Daniel Hernandez 
--(implemented by Emily Witt)
binomialFPT = g ->
(
     p := char ring g;
     v := (multiDegree(g))#0;
     w := (multiDegree(g))#1;
     FPT := 0;
     f := monomialFactor(v,w);
     x := factorOutMonomial(v,w);
     v = x#0;
     w = x#1;
     Q := maxCoordinateSum(polytopeDefiningPoints(v,w));
     if Q#0+Q#1 > 1 then FPT = 1 else
     (
	  L :=  firstCarry(Q,p);
	  if L == -1 then FPT = Q#0+Q#1 else
     	  (
     	       d := dCalculation(Q,L-1,p);
     	       P := (truncation(d,Q#0,p),  truncation(d,Q#1,p));
     	       P1 := {P#0, P#1+1/p^d};
     	       P2 := {P#0+1/p^d,P#1};
     	       FPT = truncation(L-1,Q#0+Q#1,p);
     	       if calculateEpsilon(P1,P2, v, w) != -1 then FPT = FPT +  calculateEpsilon(P1, P2, v, w);
     	  );
     );
     monFPT := infinity;
     for i from 0 to #f-1 do (if f#i!=0 then monFPT = min(monFPT, 1/(f#i)););
     if monFPT != 0 then FPT = min(FPT, monFPT);
     FPT
)

--Returns true if the polynomial is binomial.
isBinomial = f ->
(
     alert := true;
     if #(terms f)>2 then alert = false;
     alert
)


----------------------------------------------------------------
--************************************************************--
--Functions for computing test ideals, and related objects.   --
--************************************************************--
----------------------------------------------------------------

--Computes I^{[1/p^e]}, we must be over a perfect field. and working with a polynomial ring
--This is a slightly stripped down function due to Moty Katzman, with some changes to avoid the
--use(Rm) which is commented out below
--The real meat of the function is ethRootInternal, this function just looks for a certain error and calls 
--the other function depending on that error.
ethRoot = (Im,e) -> (
     J := Im;
     success := false;
     count := 0;
     try J = ethRootInternal(J,e) then success = true else (
--     print "blew a buffer";
	 while(count < e) do (	 	
	      J = ethRootInternal(J, 1);
	      count = count + 1
	 )
     );
     J
)

--This tries to compute (f^a*I)^{[1/p^e]} in such a way that we don't blow exponent buffers.  It can be much faster as well.
--We should probably just use it.  It relies on the fact that (f^(ap+b))^{[1/p^2]} = (f^a(f^b)^{[1/p]})^{[1/p]}.
ethRootSafe = (f, I, a, e) -> (
	R1 := ring I;
	p1 := char R1;
	
	aRem := a%(p1^e);
	aQuot := floor(a/p1^e);
	
	expOfA := basePExpMaxE(aRem,p1,e); --this gives "a base p", with the left-most term the smallest "endian".
	
	IN1 := ethRoot( I*ideal(f^(expOfA#0)), 1);
	i := 1;
	
	while(i < #expOfA) do (
		IN1 = ethRoot( IN1*ideal(f^(expOfA#i)), 1);
		i = i + 1;
	);
	
	IN1*ideal(f^(aQuot))
)

ethRootInternal = (Im,e) -> (
     if (isIdeal(Im) != true) then (
     	  error "ethRoot: Expted a nonnegative integer."; 
     );
     if (not (e >= 0)) then (error "ethRoot: Expected a nonnegative integer.");
     Rm:=ring(Im); --Ambient ring
     if (not (class Rm === PolynomialRing)) then (error "ethRoot: Expected an ideal in a PolynomialRing.");
     pp:=char(Rm); --characteristic
     Sm:=coefficientRing(Rm); --base field
     n:=rank source vars(Rm); --number of variables
     vv:=first entries vars(Rm); --the variables
     YY:=local YY; -- this is an attempt to avoid the ring overwriting
                         -- the ring in the users terminal
			 -- MonomialOrder=>ProductOrder{n,n}
     myMon := monoid[ (vv | toList(YY_1..YY_n)), MonomialOrder=>ProductOrder{n,n},MonomialSize=>64];
     R1:=Sm myMon; -- a new ring with new variables
     vv2 := first entries vars R1;
     J0:=apply(1..n, i->vv2#(n+i-1)-vv2#(i-1)^(pp^e)); -- 
     --print J0;
     M:=toList apply(1..n, i->vv2#(n+i-1)=>substitute(vv#(i-1),R1));

     G:=first entries compress( (gens substitute(Im,R1))%gens(ideal(J0)) );

     L:=ideal 0_R1;
     apply(G, t-> --this appears to just be a for loop
	  {
    	       L=L+ideal((coefficients(t,Variables=>vv))#1);
	  });
     L2:=mingens L;
     L3:=first entries L2;
     L4:=apply(L3, t->substitute(t,M));
     --use(Rm);
     substitute(ideal L4,Rm)
)

--A short version of ethRoot
eR = (I1,e1)-> (ethRoot(I1,e1) )

--Finds the smallest phi-stable ideal containing the given ideal Jk
--in a polynomial ring Sk
--Jk is the given ideal, ek is the power of Frobenius to use, hk is the function to multiply 
--trace by to give phi:  phi(_) = Tr^(ek)(hk._)
--This is based on ideas of Moty Katzman, and his star closure
ascendIdeal = (Jk, hk, ek) -> (
     Sk := ring Jk;
     pp := char Sk;
     IN := Jk;
     IP := ideal(0_Sk);
     --we want to make the largest ideal that is phi-stable, following Moty Katzman's idea
     --we do the following
     while (isSubset(IN, IP) == false) do(
     	  IP = IN;
--	  error "help";
	  IN = eR(ideal(hk)*IP, ek)+IP
     );

     --trim the output
     trim IP
)

--Works like ascendIdeal but tries to minimize the exponents elements are taken to
ascendIdealSafe = (Jk, hk, ak, ek) -> (
	Sk := ring Jk;
     pp := char Sk;
     IN := Jk;
     IP := ideal(0_Sk);
     --we want to make the largest ideal that is phi-stable, following Moty Katzman's idea
     --we do the following
     while (isSubset(IN, IP) == false) do(
     	  IP = IN;
--	  error "help";
	  IN = ethRootSafe(hk, IP, ak, ek)+IP
     );

     --trim the output
     trim IP
)

--Finds a test element of a ring R = k[x, y, ...]/I (or at least an ideal 
--containing a nonzero test element).  It views it as an element of the ambient ring
--of R.  It returns an ideal with some of these elements in it.
--One could make this faster by not computing the entire Jacobian / singular locus
--instead, if we just find one element of the Jacobian not in I, then that would also work
--and perhaps be substantially faster
findTestElementAmbient = Rk -> (
     --Sk := ambient Rk;
     -- Ik := ideal Sk;
     
     Jk := ideal singularLocus(Rk);
     if (isSubset(Jk, ideal Rk) == true) then 
          error "findTestElementAmbient: No test elements found, is the ring non-reduced?";
	  
     
     Jk          
)


--Outputs the test ideal of a (Q-)Gorenstein ring (with no pair or exponent)
--ek is the number such that the index divides (p^ek - 1)
--It actually spits out the appropriate stable/fixed ideal inside the ambient ring
tauQGorAmb = (Rk, ek) -> (
     Jk := findTestElementAmbient(Rk);
     hk := findQGorGen(Rk, ek);

     sub(ascendIdeal(Jk,hk,ek),Rk)
)

--Computes the test ideal of an ambient Gorenstein ring
tauGorAmb = (Rk) -> (tauQGorAmb(Rk, 1))

--Computes the test ideal of (R, f^(a/(p^e - 1)))
--when R is a polynomial ring.  This is based upon ideas of Moty Katzman.
tauAOverPEMinus1Poly = (fm, a1, e1) -> (
     Rm := ring fm;
     pp := char Rm;
     a2 := a1 % (pp^e1 - 1);
     k2 := a1 // (pp^e1 - 1); --it seems faster to use the fact that tau(f^(1+k)) = f*tau(f^k) 
     --this should be placed inside a try, and then if it fails we should be smarter...
     --fpow := fastExp(fm,a2);
     --IN := eR(ideal(fpow*fm),e1);  --the idea contained inside the test ideal.
     IN := ethRootSafe(fm, ideal(fm), a2, e1);
     
     IN = ascendIdealSafe(IN, fm, a2, e1);
     -- this is going to be the new value.  The *fm is a test element
     --5/0;
     --return the final ideal
     IN*ideal(fm^k2)
)

--Computes the test ideal of (R, f^t) when R 
--is a polynomial ring over a perfect field.
tauPoly = (fm, t1) -> (
     Rm := ring fm; 
     pp := char Rm;
     L1 := divideFraction(t1,pp); --this breaks up t1 into the pieces we need
     local I1;
     --first we compute tau(fm^{a/(p^c-1)})
     if (L1#2 != 0) then 
          I1 = tauAOverPEMinus1Poly(fm,L1#0,L1#2) else I1 = ideal(fm^(L1#0));     
	  
       
     
     --now we compute the test ideal using the fact that 
     --tau(fm^t)^{[1/p^a]} = tau(fm^(t/p^a))
     if (L1#1 != 0) then 
          ethRoot(I1, L1#1) else I1
)

--This is an internal function
--It is used to compute the test ideals of pairs (R, fm^(a1/p^e1-1)) where
--R = Sk/Ik.
--Inputs are Jk, a nonzero ideal contained in the test ideal
--hk, the multiple used to form phi of the ambient ring.  ek is the power associated with hk
--a1 and e1 and fm are as above
tauAOverPEMinus1QGorAmb = (Sk, Jk, hk, ek, fm, a1, e1) -> (
     pp := char Sk;
     et := lcm(ek, e1);
     hk1 := (hk)^(numerator ((pp^et - 1)/(pp^ek - 1)));  
       --hk for higher powers are simply appropriate powers of hk for lower powers, 
       --may as well take advantage of that
     a3 := numerator (a1*(pp^et - 1)/(pp^e1 - 1)); --we need to use a common e for both the 
                                               --index of R and of our divisor.
     
     a2 := a3 % (pp^et - 1);
     k2 := a3 // (pp^et - 1); --it seems faster to use the fact 
                              --that tau(f^(1+k)) = f*tau(f^k) 
     fpow := fm^a2; 
     
     Iasc := ascendIdeal(Jk*ideal(fm), fpow*hk1, et);
    
     Iasc*ideal(fm^k2)
)


--Computes the test ideal of (Rk, fk^t1).  Here we assume the index of the canonical
--divides (p^ek - 1)
tauQGor = (Rk, ek, fk, t1) -> (
     Sk := ambient Rk;
     pp := char Sk;
     L1 := divideFraction(t1,pp); --this breaks up t1 into the pieces we need
     hk := findQGorGen(Rk, ek); --the term in the test ideal
     Jk := findTestElementAmbient(Rk); --this finds some test elements (lifted on the ambient
                                       --ring).  Right now it is slow because of a call to 
				       --singularLocus (ie, computing a Jacobian).
     I1 := ideal(0_Sk); I2 := ideal(0_Sk);
     fm := lift(fk, Sk); --we lift our f to the ambient polynomial ring
     a1 := L1#0; e1 := L1#2; pPow := L1#1; --t1 = a1 / (pp^pPow * (pp^e1 - 1))
     d1 := pp^(pPow); if (e1 != 0) then d1 = d1*(pp^e1-1); --this is our denominator, used
                                                           --for simplifying computations
     a2 := a1 % d1;
     k2 := a1 // d1; --it seems faster to use the fact 
                              --that tau(f^(k+t)) = f^k*tau(f^t).  We'll toss on the multiple 
			      --f^k at the end
     
     --first we compute tau(fk^{a2/(p^e1-1)})
     if (e1 != 0) then 
          I1 = tauAOverPEMinus1QGorAmb(Sk,Jk,hk,ek,fm,a2,e1)
     else (
	  I1 = ideal(fm^(a2))*ascendIdeal(Jk, hk, ek)
      );
 
     --now we compute the test ideal using a generalization of the fact that 
     --tau(fm^t)^{[1/p^b]} = tau(fm^(t/p^b))
     --this follows from Schwede-Tucker.
     if (pPow != 0) then (
          --we do a check to see if the indexes match well enough...
          --the problem is we can only take ek'th roots, but my t1 might be something like
          --1/p.  I fix that by acting as if t1 is p^(ek-1)/p^ek.  
          --We can take an ekth root of that.  Often, t1 = 1, so that will keep things easy.
          remain := pPow % ek;
          dualRemain := ek - remain;
          if (remain != 0) then (
               I1 = I1*ideal(fm^(pp^dualRemain) );
     	       pPow = pPow + dualRemain;
          ); --note in the end here, ek divides pPow.
 
          --I also need to adjust hk if it is different from pPow.
          if (ek != pPow) then (
	       hk = hk^(numerator ((pp^pPow - 1)/(pp^ek - 1)))	       
	  ); --the division above makes sense because ek divides the modified pPow
 
          I2 = ethRoot(I1*ideal(hk), pPow) 
     )
     else --unless we don't have any p's in the denominator
          I2 = I1;
	  
     sub(I2, Rk)*ideal(fk^k2)
)

--Computes tau(Rk,fk^tk), assuming Gorenstein rings
tauGor = (Rg,fg,tg) -> tauQGor (Rg,1,fg,tg)

--Computes Non-Sharply-F-Pure ideals over polynomial rings for (R, fm^{a/(p^{e1}-1)}), 
--at least defined as in Fujino-Schwede-Takagi.
sigmaAOverPEMinus1Poly ={HSL=> false}>> o -> (fm, a1, e1) -> ( 
     Rm := ring fm;
     pp := char Rm;
     m1 := 0;
	e2 := e1;
	a2 := a1;
	--if e1 = 0, we treat (p^e-1) as 1.  
     if (e2 == 0) then (e2 = 1; a2 = a1*(pp-1));
     if (a2 > pp^e2-1) then (m1 = floor((a2-1)/(pp^e2-1)); a2=((a2-1)%(pp^e2-1)) + 1 );
     --fpow := fm^a2;
     IN := eR(ideal(1_Rm),e2); -- this is going to be the new value.
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  This stops after finitely many steps.  
     while (IN != IP) do(
	  IP = IN;
	  IN = ethRootSafe(fm,IP,a2,e2); -- eR(ideal(fpow)*IP,e2);
	  count = count + 1
     );

     --return the final ideal and the HSL number of this function
     if (o.HSL == true) then {IP*ideal(fm^m1),count} else IP*ideal(fm^m1)
)

--Computes Non-Sharply-F-pure ideals for non-polynomial rings with respect to no pair.
sigmaQGor ={HSL=> false}>> o -> (Rm, gg) -> (
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     hk := findQGorGen(Rm, gg);
     
     IN := ideal(1_Sm);
     count := 0;
     IP := ideal(0_Sm);
     
     while (IN != IP) do(
     	IP = IN;
     	IN = eR(ideal(hk)*IP,gg);
     	count = count + 1
     );
     
     --return the ideal and HSL
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP, Rm)
)

--Computes Non-Sharply-F-Pure ideals for non-polynomial rings
--gg is the Gorenstein index
sigmaAOverPEMinus1QGor  ={HSL=> false}>> o -> (fk, a1, e1, gg) -> (
     Rm := ring fk;
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     pp := char Rm;
     ek := lcm(e1,gg); --we need to raise things to common powers
     hk := findQGorGen(Rm, gg); --it will be faster to find the Q-Gorenstein generator
     hl := hk^(sub((pp^ek - 1)/(pp^gg - 1), ZZ) ); --
	fm := lift(fk, Sm); --lift fk to the ambient ring
	fpow := fm^(a1*sub( (pp^ek - 1)/(pp^e1-1), ZZ) );


	IN := sigmaAOverPEMinus1Poly(hk,1,gg);
	count := 0;
	IP := ideal(0_Sm);

	while (IN != IP) do(
		IP = IN;
		IN = eR(ideal(fpow*hl)*IP, e1);
		count = count + 1
	);
	
     --return the final ideal
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP,Rm)
	
)


----------------------------------------------------------------
--************************************************************--
--Functions for checking whether a ring/pair is F-pure/regular--
--************************************************************--
----------------------------------------------------------------

isFRegularPoly = method();

--Determines if a pair (R, f^t) is F-regular at a prime
--ideal Q in R, R is a polynomial ring  
isFRegularPoly (RingElement, QQ, Ideal) := (f1, t1, Q1) -> (
     not isSubset(tauPoly(f1,t1), Q1)
)

--Determines if a pair (R, f^t) is F-regular, R a polynomial ring
isFRegularPoly (RingElement, QQ) := (f1, t1) -> (
     isSubset(ideal(1_(ring f1)), tauPoly(f1,t1))
)

--Checks whether (R, f1^a1) is sharply F-pure at the prime ideal m1
isSharplyFPurePoly = (f1, a1, e1,m1) -> (
     if (isPrime m1 == false) then error "isSharplyFPurePoly: expected a prime ideal.";
     not (isSubset(ideal(f1^a1), frobeniusPower(m1,e1)))
)

--Checks whether a Q-Gorenstein pair is strongly F-regular 
isFRegularQGor = method();

--Computes whether (R, f1^t1) is F-regular, assuming the index of R divides p^e1-1
isFRegularQGor (ZZ, RingElement, QQ) := (e1,f1, t1) ->(
     R := ring f1;
     isSubset(ideal(1_R), tauQGor((ring f1),e1,f1,t1))
)

--Computes whether (R, f1^t1) is F-regular at Q1, assuming the index of R divides p^e1-1
isFRegularQGor (ZZ, RingElement, QQ, Ideal) := (e1,f1, t1, Q1) ->(
     not isSubset(tauQGor((ring f1),e1,f1,t1), Q1)
)

--Assuming no pair
isFRegularQGor (Ring,ZZ) := (R,e1) ->(
     isSubset(ideal(1_R), tauQGor(R,e1,1_R,1/1 ) )
)

--Assuming no pair checking at Q1
isFRegularQGor (Ring,ZZ,Ideal) := (R,e1,Q1) ->(
     not isSubset(tauQGor(R,e1,1_R,1/1 ),Q1 )
)


----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------

--Finds the x-intercept of a line passing through two points
xInt = (x1, y1, x2, y2) ->  x1-(y1/((y1-y2)/(x1-x2)))
 
 
--- Computes the F-signature for a specific value a1/p^e1
--- Input:
---	e1 - some positive integer
---	a1 - some positive integer between 0 and p^e
---	f1 - some polynomial in two or three variables in a ring R of PRIME characteristic
--- Output:
---	returns value of the F-signature of the pair (R, f1^{a1/p^e1})
--- Based on work of Eric Canton
fSig = (f1, a1, e1) -> (
     R1:=ring f1;
     pp:= char ring f1;     
     1-(1/pp^(dim(R1)*e1))*
          degree( (ideal(apply(first entries vars R1, i->i^(pp^e1)))+ideal(fastExp(f1,a1) ))) 
)  

--Calculates the x-int of the secant line between two guesses for the fpt
--Input:
--     t - some positive rational number
--     b - the f-signature of (R,f^{t/p^e})
--     e - some positive integer
--     t1- another rational number > t
--     f - some polynomial in two or three variables in a ring of PRIME characteristic
--
-- Output:
--	fSig applied to (f,t1,e)
--	x-intercept of the line passing through (t,b) and (t1,fSig(f,t1,e))
threshInt = (f,e,t,b,t1)-> (
     b1:=fSig(f,t1,e);
{b1,xInt(t,b,t1/(char ring f)^e,b1)}
)
 
--Guesses the FPT of ff.  It returns a list of all numbers in 
--the range suggested by nu(ff,e1) with maxDenom as the maximum denominator
guessFPT ={OutputRange=>false}>>o -> (ff, e1, maxDenom) ->(
     nn := nu(ff, e1);
     pp := char ring ff;
     if (o.OutputRange == false) then 
          findNumberBetween({nn/(pp^e1-1), (nn+1)/(pp^e1)}, maxDenom)
     else
          {{ nn/(pp^e1-1), (nn+1)/(pp^e1)}, findNumberBetween({nn/(pp^e1-1), (nn+1)/(pp^e1)}, maxDenom)}
)

--F-pure threshold estimation, at the origin
--e is the max depth to search in
--FinalCheck is whether the last isFRegularPoly is run (it is possibly very slow) 
--If MultiThread is set to true, it will compute the two F-signatures simultaneously
estFPT={FinalCheck=> true, Verbose=> false, MultiThread=>false, DiagonalCheck=>true, BinomialCheck=>true, NuCheck=>true} >> o -> (ff,ee)->(
     print "starting estFPT";
     
     maxIdeal := ideal( first entries vars( ring ff) );   --the maximal ideal we are computing the fpt at  

     foundAnswer := false; --this will be set to true as soon as we found the answer.  Setting it to true will stop further tests from being run
     answer := null; --this stores the answer until it can be returned.
     
     --first check if it is diagonal:
     if ( (o.DiagonalCheck==true) and (foundAnswer == false) ) then (
	   if (isDiagonal(ff)==true) then ( 
		if (o.Verbose==true) then print "Polynomial is diagonal."; 
		answer = diagonalFPT(ff); 
		foundAnswer = true
	   )
     );

     --now check if it is binomial:
     if ( (o.BinomialCheck==true) and (foundAnswer == false) ) then (
	  if (isBinomial(ff)==true) then ( 
	       if  (o.Verbose==true) then print "Polynomial is binomial.";
	       answer = binomialFPT(ff);
	       foundAnswer = true
	  )
     );
     
     --compute nu's
     if (foundAnswer == false) then (
     	  pp:=char ring ff;
     	  nn:=nu(ff,ee);
	  if  (o.Verbose==true) then print "nu's have been computed";

     	  --if our nu's aren't fine enough, we just spit back some information
       	  if nn==0 then (
	       answer = {0,1/pp};
	       foundAnswer = true
	   )
      );
 
      --check to see if nu/(p^e-1) is the fpt
      if ((o.NuCheck==true) and (foundAnswer == false)) then (
	   if (isFRegularPoly(ff,(nn/(pp^ee-1)),maxIdeal)==false) then ( 
		if  (o.Verbose==true) then print "Found answer via nu/(p^e-1)."; 
		answer = nn/(pp^ee-1);
		foundAnswer = true
	   ) 
      	   else (
	   	if  (o.Verbose==true) then print "nu/(p^e - 1) is not the fpt.";
	   )
      );
	 
	--check to see if (nu+1)/p^e is the FPT
	if ((o.NuCheck==true) and (foundAnswer == false)) then(
		if (isFPTPoly(ff, (nn+1)/pp^ee,Origin=>true) == true) then (
			answer = (nn+1)/pp^ee;
			foundAnswer = true
		)
	);

     --do the F-signature computation
     if (foundAnswer == false) then (
	   ak := 0;
	   if (o.MultiThread==false ) then (ak=threshInt(ff,ee,(nn-1)/pp^ee,fSig(ff,nn-1,ee),nn) ) else(
		if (o.Verbose==true) then print "Beginning multithreaded F-signature";
		allowableThreads = 4;
		numVars := rank source vars (ring ff);
		YY := local YY;
		myMon := monoid[  toList(YY_1..YY_numVars), MonomialOrder=>RevLex,Global=>false];
		--print myMon;
     		R1:=(coefficientRing ring ff) myMon;
		rMap := map(R1, ring ff, vars myMon);
		gg := rMap(ff);
		
		
		H := (fff,aaa,eee) -> () -> fSig(fff,aaa,eee);
		newSig1 := H(gg,nn-1,ee);
		t1 := schedule newSig1;
	     	s2 := fSig(ff,nn,ee);	
		if (o.Verbose==true) then print "One signature down";
		while ((not isReady t1)) do sleep 1;
		s1 := taskResult t1;
     	      --  print s1; print s2;
		ak = {s2,xInt( (nn-1)/pp^ee, s1, (nn)/pp^ee,s2)};
		--print nn;		
	   );
	   if  (o.Verbose==true) then print "Computed F-signatures.";
	   --now check to see if we cross at (nu+1)/p^e, if that's the case, then that's the fpt.
	   if ( (nn+1)/pp^ee == (ak#1) ) then (
		if  (o.Verbose==true) then print "F-signature line crosses at (nu+1)/p^e."; 
		answer = ak#1;
		foundAnswer = true
	   )
      );	  
      	
      --if we run the final check, do the following
      if ( (foundAnswer == false) and (o.FinalCheck == true)) then ( 
	  if  (o.Verbose==true) then print "Starting FinalCheck."; 
          	if ((isFRegularPoly(ff,(ak#1),maxIdeal)) ==false ) then (	
	      		if  (o.Verbose==true) then print "FinalCheck successful"; 
	      		answer = (ak#1);
	      		foundAnswer = true 
      	  	)
	  		else ( 
	      		if  (o.Verbose==true) then print "FinalCheck didn't find the fpt."; 
	      		answer = {(ak#1),(nn+1)/pp^ee};
	      		foundAnswer = true
	  		)
       );
       
       --if we don't run the final check, do the following
       if ((foundAnswer == false) and (o.FinalCheck == false) ) then (
	  if  (o.Verbose==true) then print "FinalCheck not run.";
	  answer = {(ak#1),(nn+1)/pp^ee};
      	  foundAnswer = true
       );
     
     --return the answer
     answer
)

--isFPTPoly, determines if a given rational number is the FPT of a pair in a polynomial ring. 
--if Origin is specified, it only checks at the origin. 
isFPTPoly ={Verbose=> false,Origin=>false}>> o -> (f1, t1) -> (
	pp := char ring f1;
	if (o.Origin == true) then org := ideal(vars (ring f1));
	funList := divideFraction(t1, pp);
	--this writes t1 = a/(p^b(p^c-1))
	aa := funList#0;
	bb := funList#1;
	cc := funList#2;
	mySigma := ideal(f1);
	myTau := tauPoly(f1, t1*pp^bb);
	if (o.Verbose==true) then print "higher tau Computed";

	--first we check whether this is even a jumping number.
	if (cc == 0) then
		mySigma = (ideal(f1^(aa-1)))*((sigmaAOverPEMinus1Poly(f1, (pp-1), 1)))
	else 
		mySigma = (sigmaAOverPEMinus1Poly(f1, aa, cc));
	if (o.Verbose==true) then print "higher sigma Computed";

	returnValue := false;
	
	if (o.Origin == false) then (--if we are not restricting our check to the origin.
		if ( not (isSubset(mySigma, myTau) ) ) then (--this holds if t1 is a jumping number (but it is not sufficient), perahps it would better not to do this check.
			if (o.Verbose==true) then print "higher sigma is not higher tau";
			if ( isSubset(ideal(sub(1, ring f1)), ethRoot(mySigma, bb) )) then (
				if (o.Verbose==true) then print "we know t1 <= FPT";
				if (not isSubset(ideal(sub(1, ring f1)), ethRoot(myTau, bb) ))  then returnValue = true 
			)
		)
	)
	else( --we are only checking at the origin
		if ( isSubset(ideal(sub(1, ring f1)), ethRoot(mySigma, bb)+org )) then (
			if (o.Verbose==true) then print "we know t1 <= FPT";
			if (not isSubset(ideal(sub(1, ring f1)), ethRoot(myTau, bb)+org ))  then returnValue = true 
		)
	);
	
	returnValue
)

--isFJumpingNumberPoly determines if a given rational number is an F-jumping number
isFJumpingNumberPoly ={Verbose=> false}>> o -> (f1, t1) -> (
	pp := char ring f1;
	funList := divideFraction(t1, pp);
	--this writes t1 = a/(p^b(p^c-1))
	aa := funList#0;
	bb := funList#1;
	cc := funList#2;
	mySigma := ideal(f1);
	myTau := ethRoot(tauPoly(f1, t1*pp^bb), bb);
	if (o.Verbose==true) then print "higher tau Computed";

	--first we check whether this is even a jumping number.
	if (cc == 0) then
		mySigma = ethRoot((ideal(f1^(aa-1)))*((sigmaAOverPEMinus1Poly(f1, (pp-1), 1))), bb)
	else 
		mySigma = ethRoot((sigmaAOverPEMinus1Poly(f1, aa, cc)),bb);
	if (o.Verbose==true) then print "sigma Computed";

	not (isSubset(mySigma, myTau))
)

--****************************************************--
--*****************Documentation**********************--
--****************************************************--

beginDocumentation()
doc ///
   Key
      PosChar 
   Headline
      A package for calculations in positive characteristic 
   Description
      Text    
         This will do a lot of cool stuff someday. 
///

doc ///
     Key
     	isFPTPoly 
     Headline
        Checks whether a given number is the FPT
     Usage
     	  isFPTPoly(f,t,Verbose=>V,Origin=>W)  
     Inputs
         	f:RingElement
	 	t:ZZ
		W:Boolean
		W:Origin
     Outputs
        :Boolean
     Description
     	Text
	     Returns true if t is the FPT, otherwise it returns false.  If Origin is true, it only checks it at ideal(vars ring f).
///

doc ///
     Key
     	isFJumpingNumberPoly 
     Headline
        Checks whether a given number is the FPT
     Usage
     	  isFJumpingNumberPoly(f,t,Verbose=>V)  
     Inputs
         	f:RingElement
	 	t:ZZ
		W:Boolean
     Outputs
        :Boolean
     Description
     	Text
	     Returns true if t is an F-jumping number, otherwise it returns false.
///


doc ///
     Key
     	basePExp 
     Headline
        Base p Expansion of an integer N
     Usage
     	  basePExp(N,p) 
     Inputs
         N:ZZ
	 p:ZZ
     Outputs
        :List
     Description
     	Text
	     Given an integer N and a prime p, outputs the digits of the base p expansion of N in base p.
///

doc ///
     Key
     	fastExp 
     Headline
        Computes powers of elements in rings of characteristic p>0 quickly.
     Usage
     	  fastExp(f,N) 
     Inputs
     	 f:RingElement
         N:ZZ
     Outputs
        :RingElement
     Description
	Text
	     In prime characteristic p > 0, raising a sum (a+b) to a power is more quickly done by simply computing a^p and b^p and adding them.  The basic strategy is to break up the exponent into its base p expansion, and then use the exponent rules.  For example, (x+y)^(3*p^2 + 5*p+2) = ((x+y)^3)^(p^2)*((x+y)^5)^p*(x+y)^2.
///

doc ///
     Key
     	 frobeniusPower
     Headline
        The following raises an ideal to the $p^e$th power.
     Usage
     	  frobeniusPower(I,e) 
     Inputs
     	 I:Ideal
         e:ZZ
     Outputs
        :Ideal
     Description
	Text
	     If I = ideal(x1, ..., xn), then frobeniusPower(I,e) outputs ideal(x1^(p^e), ..., xn^(p^e)) where p is the characteristic of the ring.
///


doc ///
     Key
     	guessFPT 
     Headline
        Tries to guess the FPT in a really naive way (this should be improved).
     Usage
     	  guessFPT(f,e,d) 
     Inputs
     	 f:RingElement
         e:ZZ
	 d:ZZ
     Outputs
        :List
     Description
	Text
	     This tries to guess the FPT.  In particular, it computes the number nu such that nu/(p^e - 1) <= FPT < (nu+1)/p^e.  It then outputs a list of all rational numbers with denominators less than or equal to d, which lie in that range.  WARNING:  There are several improvements which should be made to this function to rule out many of the possibilies.
///


doc ///
     Key
     	 nu
	 (nu,Ideal,ZZ)
	 (nu,RingElement,ZZ)
     Headline
        Gives $\nu_I(p^e)$.
     Usage
     	  nu(I,e)
	  nu(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
        :ZZ
     Description
	Text
	    Given an ideal I in a polynomial ring k[x1, ..., xn], this function outputs the smallest integer nu such that I^nu is not in ideal(x1^(p^e), ..., xn^(p^e) ).  If a RingElement is passed, it computes nu of the principal ideal generated by this element. This is used frequently to compute the F-pure threshold.
///

doc ///
     Key
     	 nuList
	 (nuList,Ideal,ZZ)
	 (nuList,RingElement,ZZ)
     Headline
        Lists $\nu_I(p^d)$ for d = 1,...,e.
     Usage
     	  nuList(I,e)
	  nuList(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
        :List
     Description
	Text
	     Given an ideal I in a polynomial ring k[x1,...,xn], this function computes nu(I,d) for d = 1,...,e.
///

doc ///
     Key
     	 FPTApproxList
	 (FPTApproxList,Ideal,ZZ)
	 (FPTApproxList,RingElement,ZZ)
     Headline
        Gives a list of $\nu_I(p^d)/p^d$ for d=1,...,e.
     Usage
     	  FPTApproxList(I,e)
	  FPTApproxList(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
         :List
     Description
	Text 
 	     This returns a list of nu(I, p^d) for d = 1, ..., e.  The {nu(I, p^d)/p^d} converge to the F-pure threshold.	     
///

doc ///
     Key
     	 digit
     Headline
        Gives the e-th digit of the base p expansion 
     Usage
     	  digit(e,x,p) 
     Inputs
         e:ZZ
         x:RR
         p:ZZ
     Outputs
        :ZZ
     Description
	Text
	     Gives the e-th digit, to the right of the decimal point, of the non-terminating base p expansion of x in [0,1] 
///


doc ///
     Key
     	 ethRoot
     Headline
        Computes $I^{[1/p^e]}$ in a polynomial ring over a perfect field
     Usage
     	  ethRoot(I,e) 
     Inputs
     	 I:Ideal
         e:ZZ
     Outputs
        :Ideal
     Description
	Text
	     In a polynomial ring k[x1, ..., xn], I^{[1/p^e]} is the smallest ideal J such that J^{[p^e]} = FrobeniusPower(J,e) \supseteq I.  This function computes it.
///

doc ///
     Key
     	 tauPoly
     Headline
        Computes the test ideal of $(R, f^t)$.
     Usage
     	  tauPoly(f,t) 
     Inputs
     	 f:RingElement
         t:QQ
     Outputs
        :Ideal
     Description
	Text
	     This computes the test ideal of (R, f^t) when R is a polynomial ring over a perfect field.  It is done as follows.  If t = a/(p^e - 1) then tau(R, f^t) is computed as a sum of (f^{\lceil t \rceil}*f^{\lceil t(p^e-1) \rceil})^{[1/p^e]} until the sum stabilizes.  For the more general case, we use the formula tau(R, f^t)^{[1/p^d]} = tau(R, f^{t/p^d}).
///

doc ///
     Key
     	 isFRegularPoly
     Headline
        Determines if a pair $(R, f^t)$ is F-regular when R is a polynomial ring. 
     Usage
     	  isFRegularPoly
     Inputs
     	 f:RingElement
         t:QQ
     Outputs
        :Boolean
     Description
	Text
	     This computes the test ideal.  The ring is F-regular if the test ideal is the whole ring, in which case this function returns true.  Otherwise, this function returns false.

///
doc ///

     Key
     	 fSig
     Headline
        Computes the F-signature for a specific value $a/p^e$.
     Usage
     	  fSig(f,a,e)
     Inputs
     	 f:RingElement
	 a:ZZ
         e:ZZ
     Outputs
        :QQ
     Description
	Text
	     This computes the F-signature $s(R, f^{a/p^e})$ if R is a polynomial ring over a perfect field.
///

doc ///
     Key
     	 estFPT
     Headline
         Atempts to compute the F-pure threshold, where e is the max depth to search in.  
     Usage
     	  estFPT(f,e,finalCheck=>V,Verbose=>W)
     Inputs
     	 f:RingElement
         e:ZZ
	 V:Boolean
	 W:Boolean
     Outputs
        L:List
	Q:QQ
     Description
     	  Text 
	      This tries to find an exact value for the fpt.  If it can, it returns that value.  Otherwise it should return a range of possible values (eventually).  It first checks to see if the ring is binonmial or diagonal.  In either case it uses methods of D. Hernandez.  Next it tries to estimate the range of the FPT using nu's.  Finally, it tries to use this to deduce the actual FPT via taking advantage of convexity of the F-signature function and a secant line argument.  finalCheck is a Boolean with default value True that determines whether the last isFRegularPoly is run (it is possibly very slow).  If FinalCheck is false, then a last time consuming check won't be tried.  If it is true, it will be.  Verbose set to true displays verbose output.
///

doc ///
     Key
     	 isSharplyFPurePoly
     Headline
        Checks whether (R, f^a) is F-pure at the prime ideal m.
     Usage
     	 isSharplyFPurePoly(f,a,e,m)
     Inputs
     	 f:RingElement
	 a:ZZ
         e:ZZ
	 m:Ideal
     Outputs
         :Boolean
     Description
	Text
	     This checks whether (R, f^a) is F-pure at the prime ideal m at least in the case that R is a polynomial ring.
///

doc ///
     Key
     	findQGorGen
     Headline
        If R = S/I where S is a polynomial ring, returns the ring element with I^{[p^e]} : I = (f) + I^{[p^e]}.
     Usage
     	 findQGorGen(R, e)
     Inputs
     	 R:Ring
     Outputs
         :RingElement
     Description
	Text
	     If R is Q-Gorenstein with index not divisible by p, then I^{[p^e]} : I = (f) + I^{[p^e]}.  For some e.  This function tries to find the f.  If the argument e is left out then e is assumed to be 1.
///

doc ///
     Key
     	tauQGorAmb
     Headline
        Computes tau(R) for a Q-Gorenstein ring with index not dividing p^e - 1.
     Usage
     	 tauQGorAmb(R,e)
     Inputs
     	 R:Ring
	 e:ZZ
     Outputs
         :Ideal
     Description
	Text
	     This computes the test ideal tau(R) for a Q-Gorenstein ring R with index not divisible by p^e - 1.  It uses the fact that if R is a quotient of a polynomial ring S, then tau(R) can be computed as a sort of test/adjoint ideal on S.  The function findQGorGen is used to find the map to use on S.  e is the index of the canonical divisor on R.
///

doc ///
     Key
     	tauGorAmb
     Headline
        Computes tau(R) for a Gorenstein ring.
     Usage
     	 tauGorAmb(R)
     Inputs
     	 R:Ring
     Outputs
         :Ideal
     Description
	Text
	     This computes the test ideal tau(R) for a quasi-Gorenstein ring R.  It uses the fact that if R is a quotient of a polynomial ring S, then tau(R) can be computed as a sort of test/adjoint ideal on S.  The function findQGorGen is used to find the map to use on S. 
///

doc ///
     Key
     	tauQGor
     Headline
        Computes tau(R,f^t) for a Q-Gorenstein ring such that the index divides p^e-1.
     Usage
     	 tauGorAmb(R,e,f,t)
     Inputs
     	 R:Ring
	 e:ZZ
	 f:RingElement
	 t:QQ
     Outputs
         :Ideal
     Description
	Text
	     This computes the test ideal tau(R, f^t) for a Q-Gorenstein ring such that the index divides p^e -1.  First the test ideal of the ambient space is computed (and computed on a polynomial ring S of which R is a quotient).  Then writing t = a/(p^b-1)p^c we compute tau(R, f^{a/(p^b-1)}), or rather a preimage of it on S, by summing images of the map induced by f^{a/(p^b-1)}.  We then compute tau(R, f^t) by multiplying by the output of a findQGorGen on S, and taking [1/p^e]th roots on S.
///

doc ///
     Key
     	tauGor
     Headline
        Computes tau(R,f^t) for a Gorenstein ring such that the index divides p^e-1.
     Usage
     	 tauGorAmb(R,f,t)
     Inputs
     	 R:Ring
	 f:RingElement
	 t:QQ
     Outputs
         :Ideal
     Description
	Text
	     This computes the test ideal tau(R, f^t) for a Gorenstein ring.  First the test ideal of the ambient space is computed (and computed on a polynomial ring S of which R is a quotient).  Then writing t = a/(p^b-1)p^c we compute tau(R, f^{a/(p^b-1)}), or rather a preimage of it on S, by summing the images of the map induced by f^{a/(p^b-1)}.  We then compute tau(R, f^t) by multiplying by the output of a findQGorGen on S, and taking [1/p^e]th roots on S.
///

doc ///
     Key
     	basePExpMaxE
     Headline
        Computes non-terminating base-p expansion of N from digits zero to e-1.
     Usage
     	 basePExpMaxE(N,p,e)
     Inputs
     	 N:ZZ
	 	 p:ZZ
	 	 e:ZZ
     Outputs
         :List
     Description
	Text
	     This computes the base p expansion of N, from digits 0 to e-1.  The digits are given in a list, and come with leading zeros.  If fewer than e digits are required, the list is padded with zeros.  If more digits are required, the final digit lists them.  Little endian is first.  For example, if p=5 and N = 16, the basePExpMaxE(16,5,4) will return {1,3,0,0} (1 one, 3 fives, 0 twentyfives, 0 onehundred twentyfives).
///

doc ///
     Key
     	ethRootSafe
     Headline
        Computes (f^a*I)^{[1/p^e]} in such a way that we don not blow exponent buffers.
     Usage
     	 ethRootSafe(f, I, a, e)
     Inputs
     	 f:RingElement
	 I:Ideal
	 a:ZZ
	 e:ZZ
     Outputs
         :Ideal
     Description
	Text
	     Computes the 1/p^e-th root of (f^a*I).  It does it while trying to minimize the power that f gets raised to (in case a is a large number).  This can either be faster or slower than ethRoot.
///

doc ///
     Key
     	tauAOverPEMinus1Poly
     Headline
        Computes the test ideal of f^(a/(p^e-1)) if f is in a polynomial ring.
     Usage
     	 tauAOverPEMinus1Poly(f, a, e)
     Inputs
     	 f:RingElement
	 a:ZZ
	 e:ZZ
     Outputs
         :Ideal
     Description
	Text
	     Computes the test ideal tau(f^(a/(p^e-1)) ).  The basic idea first appeared in a paper of Mordechai Katzman.
///

doc ///
     Key
     	ascendIdeal
     Headline
        Finds the smallest phi-stable ideal containing a given ideal in a polynomial ring.
     Usage
     	 ascendIdeal(J, h, e)
     Inputs
     	 J:Ideal 
	h:RingElement
	e:ZZ
     Outputs
         :Ideal
     Description
	Text
	     Let phi be the p^(-e) linear map obtained by multiplying e-th Frobenius trace by h.  Then this function finds the smallest phi-stable ideal containing J.  The idea is to consider the ascending chain J, J+phi(J), J+phi(J)+phi^2(J), etc.  We return the stable value.  For instance, this can be used to compute the test ideal.  This method appared first in the work of Mordechai Katzman on star closure.
///

doc ///
     Key
     	ascendIdealSafe
     Headline
        Finds the smallest phi-stable ideal containing a given ideal in a polynomial ring.
     Usage
     	 ascendIdeal(J, h, a, e)
     Inputs
     	 J:Ideal 
	h:RingElement
	a:ZZ
	e:ZZ
     Outputs
         :Ideal
     Description
	Text
	     Let phi be the p^(-e) linear map obtained by multiplying e-th Frobenius trace by h^a.  Then this function finds the smallest phi-stable ideal containing J.  The idea is to consider the ascending chain J, J+phi(J), J+phi(J)+phi^2(J), etc.  We return the stable value.  For instance, this can be used to compute the test ideal.  This method appared first in the work of Mordechai Katzman on star closure.  It differs from ascendIdeal in that it minimizes the exponents that h is raised to, this can make it faster or slower depending on the circumstances.
///

doc ///
     Key
     	sigmaAOverPEMinus1Poly
     Headline
        Computes the non-sharply F-pure ideal of (R, f^{a/(p^e-1)}) when R is a polynomial ring.
     Usage
     	 sigmaAOverPEMinus1Poly (f, a, e, HSL=>W)
     Inputs 
		f:RingElement
	a:ZZ
	e:ZZ
	W:Boolean
     Outputs
         :Ideal
     Description
	Text
	     Let phi be the p^(-e) linear map obtained by multiplying e-th Frobenius trace by f^a.  This computes \phi^n(R) for large n.  This stabilizes by Hartshorne-Speiser-Lyubeznik-Gabber.  If HSL is true, then the function returns a list where the first entry is sigma and the second entry is the HSL number.
///

doc ///
     Key
     	sigmaAOverPEMinus1QGor
     Headline
        Computes the non-sharply F-pure ideal of (R, f^{a/(p^e-1)}).
     Usage
     	 sigmaAOverPEMinus1QGor(f, a, e, g,HSL=>W)
     Inputs 
		f:RingElement
		a:ZZ
		e:ZZ
		g:ZZ
		W:Boolean
     Outputs
         :Ideal
     Description
	Text
	     Let phi be the p^(-e) linear map obtained by multiplying e-th Frobenius trace of R by f^a (we assume that the Q-Gorenstein index of R divides p^g-1).  This computes \phi^n(R) for large n.  This stabilizes by Hartshorne-Speiser-Lyubeznik-Gabber.  If HSL is true, then the function returns a list where the first entry is sigma and the second entry is the HSL number of sigma(ring f) relative to f.
///

doc ///
     Key
     	sigmaQGor
     Headline
        Computes the non-sharply F-pure ideal of R, where R is Q-Gorenstein with index dividing (p^g-1).
     Usage
     	 sigmaQGor(R, g,HSL=>W)
     Inputs 
		R:Ring
		g:ZZ
		W:Boolean
     Outputs
         :Ideal
     Description
	Text
	     Let phi be the  g-th Frobenius trace of R (we assume that g is the Q-Gorenstein index of R).  This computes \phi^n(R) for large n.  This stabilizes by Hartshorne-Speiser-Lyubeznik-Gabber.  If HSL is true, then the function returns a list where the first entry is sigma and the second entry is the HSL number.
///

doc ///
     Key
     	isFRegularQGor
	 (isFRegularQGor, ZZ, RingElement, QQ)
	 (isFRegularQGor, ZZ, RingElement, QQ, Ideal)
	 (isFRegularQGor, Ring, ZZ)
	 (isFRegularQGor, Ring, ZZ, Ideal)
     Headline
        Checks whether a ring or a pair is Q-Gorenstein.
     Usage
     	 isFRegularQGor(e,f,t)
     	 isFRegularQGor(e,f,t,Q)
     	 isFRegularQGor(R,e)
     	 isFRegularQGor(R,e,Q)
     Inputs 
		R:Ring
	 f:RingElement
	 e:ZZ
	 t:QQ
	 Q:Ideal
     Outputs
         :Boolean
     Description
	Text
	     Checks whether R, or the pair (R, f^t),  is strongly F-regular at Q (respectively the origin).  It assumes the Q-Gorenstein index divides (p^e - 1).
///

doc ///
     Key
     	divideFraction
     Headline
        Converts a rational number into something of the form (a/(p^b p^(c-1)).
     Usage
     	 divideFraction(t, p)
     Inputs 
		t:QQ
	p:ZZ
     Outputs
         :List
     Description
	Text
	     Given a rational number t and prime p, this function finds a list of integers {a,b,c} such that t= (a/(p^b p^(c-1)).
///

doc ///
     Key
     	firstCarry
     Headline
        Finds the first spot where (the eth digit of x) + (the eth digit of y) >= p.
     Usage
     	 firstCarry(w,p)
     Inputs 
		w:List
	p:ZZ
     Outputs
         :ZZ
     Description
	Text
	     Set w = {x,y} a list of rational numbers in [0,1].  Finds the first place where (the eth digit of x) + (the eth digit of y) >= p, in other words where the numbers add with carrying.
///

doc ///
     Key
     	carryTest
     Headline
        Finds the number of digits we must check to see whether x and y add without carrying.
     Usage
     	 carryTest(w,p)
     Inputs 
		w:List
	p:ZZ
     Outputs
         :ZZ
     Description
	Text
	     Set w = {x,y} a list of rational numbers in [0,1].  This function finds the number of digit places we must check to see if x and y add without carrying.
///

doc ///
     Key
     	truncationBaseP
     Headline
        Gives the first e digits of the non-terminating base p expansion of x.
     Usage
     	 truncationBaseP(e,x,p)
     Inputs 
		e:ZZ
	x:QQ
	p:ZZ
     Outputs
         :List
     Description
	Text
	     Gives the first e digits of the non-terminating base p expansion of x in [0,1], as a list.
///

doc ///
     Key
     	truncation
     Headline
        Gives the first e digits of the non-terminating base p expansion of x.
     Usage
     	 truncation(e,x,p)
     Inputs 
		e:ZZ
	x:QQ
	p:ZZ
     Outputs
         :List
     Description
	Text
	     Gives the first e digits of the non-terminating base p expansion of x in [0,1], as a fraction.
///

doc ///
     Key
     	denom
     	(denom,ZZ)
     	(denom,QQ)
     Headline
        Returns the denominator of a rational number.
     Usage
     	 denom(x)
     	 denom(y)
     Inputs 
		x:QQ
		y:ZZ
     Outputs
         :ZZ
     Description
	Text
	    Returns the denominator of a rational number or integer (in the latter case it returns 1).
///

doc ///
     Key
     	binomialFPT
     Headline
        Computes the F-pure threshold of a binomial polynomial.
     Usage
     	 binomialFPT(f)
     Inputs 
		f:RingElement
     Outputs
         :QQ
     Description
	Text
	    Returns the F-pure threshold of a binomial in a polynomial ring.  This is based on the work of Daniel Hernandez.
///

doc ///
     Key
     	diagonalFPT
     Headline
        Computes the F-pure threshold of a diagonal polynomial.
     Usage
     	 diagonalFPT(f)
     Inputs 
		f:RingElement
     Outputs
         :QQ
     Description
	Text
	    Returns the F-pure threshold of a diagonal hypersurface in a polynomial ring.  This is based on the work of Daniel Hernandez.
///

doc ///
     Key
     	isBinomial 
     Headline
        Checks whether a polynomial is binomial.
     Usage
     	 isBinomial(f)
     Inputs 
		f:RingElement
     Outputs
         :Boolean
     Description
	Text
	    Returns true if f is a binomial, otherwise returns false.
///

doc ///
     Key
     	isDiagonal 
     Headline
        Checks whether a polynomial is diagonal.
     Usage
     	 isDiagonal(f)
     Inputs 
		f:RingElement
     Outputs
         :Boolean
     Description
	Text
	    Returns true if f is a diagonal, otherwise returns false.  Recall f is called diagonal if it is of the form x_1^(a_1)+...+x_n^(a_n) up to renumbering of the variables.
///

doc ///
     Key
     	aPower
     Headline
        Finds the largest power of p dividing x.
     Usage
     	 aPower(x,p)
     Inputs 
		x:ZZ
		p:ZZ
     Outputs
         :ZZ
     Description
	Text
	    Returns the largest exponent e such that p^e divides x.
///



end
