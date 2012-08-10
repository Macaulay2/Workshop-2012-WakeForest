newPackage( "PosChar",
Version => "1.0", Date => "August 5, 2012", Authors => {
     {Name => "Karl Schwede",
     Email => "",
     HomePage => ""
     },
     {Name=> "Emily Witt",
     Email=> "ewitt@umn.edu",
     HomePage => "http://math.umn.edu/~ewitt/"
     },
     {Name => "Sara Malec",
     Email=> "smalec@gsu.edu"
     }},
Headline => "A package for calculations in positive characteristic", DebuggingMode => true, Reload => true )
export{"basePExp",
     "fastExp",
     "nu",
     "nuList",
     "frobeniusPower",
     "FPTApproxList",
     "ethRoot",
     "tauPoly",
     "isFRegularPoly",
     "fSig",
     "FPTEst",
     "isSharplyFPurePoly",
     "finalCheck",
     "aPower",
     "firstCarry",
     "carryTest",
     "truncationBaseP",
     "truncation",
     "digit",
     "denom",
     "binomialFPT",
     "diagonalFPT",
     "isBinomial",
     "isDiagonal",
     "multiDegree",
     "dCalculation",
     "calculateEpsilon",
     "guessFPT"
}
--This file has "finished" functions from the Macaulay2 workshop at Wake Forest
--August 2012.  Sara Malec, Karl Schwede and Emily Witt contributed to it.
--Some functions, are based on code written by Eric Canton and Moty Katzman

----------------------------------------------------------------
--************************************************************--
--Functions for doing particular factorizations with numbers. --
--************************************************************--
----------------------------------------------------------------

denom = method(); --find the denominator of a rational number or integer
denom QQ := x -> denominator x;
denom ZZ := x -> 1;

fracPart = (x) -> (x - floor(x)) --finds the fractional part of a number

--Given a vector w={x,y}, x and y rational in [0,1], returns a number of digits 
--such that it suffices to check to see if x and y add without carrying in base p
aPower = (x,p) -> --find the largest power of p dividing x
(
a:=1; while fracPart(denom(x)/p^a)==0 do a = a+1;
a-1
)

num = method(); --find the numerator of a rational number or integer
num QQ := x -> numerator x;
num ZZ := x -> x;
     
-- this function takes in a fraction t and a prime p and spits out a list
-- {a,b,c}
-- where t = (a/p^b)(1/(p^c-1))
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

--this finds the a/pp^e1 nearest t1 from above
findNearPthPowerAbove = (t1, pp, e1) -> (
     ceiling(t1*pp^e1)/pp^e1
)

--this finds the a/pp^e1 nearest t1 from below
findNearPthPowerBelow = (t1, pp, e1) -> (
     floor(t1*pp^e1)/pp^e1
)

--returns the digits in nn which are nonzero in binary 
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

--this returns the entries of myList specified by entryList
--for example, ( {1,2,3}, {0,2}) is sent to {1,3}.
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)

--this returns the power set of a given list, except it leaves out
--the emptyset.  
--For example {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)

--this turns a number into a list of factors with repeats.
--for example, 12 becomes (2,2,3)
numberToPrimeFactorList = (nn)->(
     prod := factor nn;
     flatten (apply(#prod, i -> toList(((prod#(i))#1):((prod#(i))#0)) ))
)


--this returns a list of all proper factors of nn, for use with sieving...
getFactorList = (nn) ->(
     if (nn < 1) then error "getFactorList: expected an integer greater than 1.";
     powSet := nontrivialPowerSet(numberToPrimeFactorList(nn)); 
     toList ( set apply(#powSet, i->product(powSet#i)) )
)

--this function finds rational numbers in the range of the interval
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

--this function finds rational numbers in the range of 
--the interval.  The max denominator allowed is listed. 
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

--Computes powers of elements in char p>0 rings using the "Freshman's dream"
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
	  --J = ideal(apply(first entries gens I, g->fastExp(g, N, char ring I)));
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

--The following raises an ideal to a Frobenius power.  It was written by Moty Katzman
frobeniusPower=method()

frobeniusPower(Ideal,ZZ) := (I,e) ->(
     R:=ring I;
     p:=char R;
     local u;
     local answer;
     G:=first entries gens I;
     if (#G==0) then answer=ideal(0_R) else answer=ideal(apply(G, u->u^(p^e)));
     answer
);


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

--Determines whether a polynomial f is diagonal; i.e. of the form 
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

--Given a binomial x_1^(a_1)*...*x_n^(a_n) + x_1^(b_1)*...*x_n^(b_n), input the 
--vectors v={a_1,...,a_n} and w={b_1,...,b_n}, gives the corresponding vector of
--the polynomial that omits all factors where a_i=b_i.
factorOutMonomial = (v,w) ->
(
     v1 := new MutableList;
     w1 := new MutableList;
     c := 0; i := 0; for i from 0 to #v-1 do (if v#i != w#i then (v1#c = v#i; w1#c = w#i; c = c+1; ); );
     (v1,w1)
)


--Gives the monomial factored out from factorOutMonomial
monomialFactor = (v,w) ->
(
     a := new MutableList;
     c := 0; i := 0; for i from 0 to #v-1 do (if v#i == w#i then (a#c = v#i; c = c+1; ); );
     a
)

--Given two vectors v={v0,v1} and w={w0,w1} in the real plane, finds the intersection of the associated lines v0*x+w0*y=1 and v1*x+w1*y=1
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

--Given two vectors v={v0,...vn} and w={w0,...,wn}, list the intersections of all lins vi*x+wi*y=1 and vj*x+wj*y=1
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


--Given a point a=(x,y) in the real plane and two vectors v={v0,...,vn} and w={w0,...,wn}, checks whether a is in the polytope defined by the equations vi*x+wi*y<=1
isInInteriorPolytope = (a,v,w) ->
(
     alert := true;
     for i from 0 to #v-1 do
     (
	  if v#i*a#0 + w#i*a#1 >= 1 then alert = false;
     );
     alert
)

--Given two vectors v and w of the same length, outputs a list of the defining vectors of the polytope as in isInPolytope
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

--Given a list of coordinates in the real plane, outputs the one with the largest coordinate sum
maxCoordinateSum = L ->
(
     K := new MutableList from {0,0};
     for i from 0 to #L-1 do if (L#i)#0 + (L#i)#1 > K#0 + K#1 then K = {(L#i)#0, (L#i)#1};
     K
)

--Finds the "delta" in the algorithm of D. Hernandez for F-pure thresholds of binomials
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

--Given the "truncation" point (P1,P2) and two vectors defining the binomial v and w, outputs the "epsilon" in the algorithm of D. Hernandez for F-thresholds of binomials
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
--use(Rm) which is commented out in a ring
ethRoot = (Im,e) -> (
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

-- a short version of ethRoot
eR = (I1,e1)-> (ethRoot(I1,e1) )

-- the following function computes the test ideal of (R, f^(a/(p^e - 1)))
-- when R is a polynomial ring.  This is based upon ideas of Moty.
tauAOverPEMinus1Poly = (fm, a1, e1) -> (
     Rm := ring fm;
     pp := char Rm;
     a2 := a1 % (pp^e1 - 1);
     k2 := a1 // (pp^e1 - 1); --it seems faster to use the fact that tau(f^(1+k)) = f*tau(f^k) 
     fpow := fastExp(fm,a2);
     IN := eR(ideal(fpow*fm),e1); -- this is going to be the new value.  The *fm is a test element
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     
     --our initial value is something contained in the test ideal.  
     while (IN != IP) do(
	  IP = IN;
	  IN = eR(ideal(fpow)*IP,e1)+IP
     );

     --return the final ideal
     IP*ideal(fm^k2)
)

--the following function computes the test ideal of (R, f^t) when R 
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

--computes Non-F-Pure ideals for (R, fm^{a/(p^{e1}-1)}) 
--at least defined as in Fujin-Schwede-Takagi.
sigmaAOverPEMinus1Poly = (fm, a1, e1) -> (
     Rm := ring fm;
     pp := char Rm;
     fpow := fm^a1;
     IN := eR(ideal(1_Rm),e1); -- this is going to be the new value.
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  This stops after finitely many steps.  
     while (IN != IP) do(
	  IP = IN;
	  IN = eR(ideal(fpow)*IP,e1);
	  count = count + 1
     );

     --return the final ideal and the HSL number of this function
     {IP,count}
)

----------------------------------------------------------------
--************************************************************--
--Functions for checking whether a ring/pair is F-pure/regular--
--************************************************************--
----------------------------------------------------------------

--this function determines if a pair (R, f^t) is F-regular, R is a polynomial ring.  
isFRegularPoly = (f1, t1) -> (
     isSubset(ideal(1_(ring f1)), tauPoly(f1,t1))
)

--this function checks whether (R, f1^a1) is F-pure at the prime ideal m1
isSharplyFPurePoly = (f1, a1, e1,m1) -> (
     if (isPrime m1 == false) then error "isSharplyFPurePoly: expected a prime ideal.";
     not (isSubset(ideal(f1^a1), frobeniusPower(m1,e1)))
)


----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------
--a function to find the x-intercept of a line passing through two points
xInt = (x1, y1, x2, y2) ->  x1-(y1/((y1-y2)/(x1-x2)))
 
 
--- Computes the F-signature for a specific value a/p^e
--- Input:
---	e - some positive integer
---	a - some positive integer between 0 and p^e
---	f - some HOMOGENEOUS polynomial in two or three variables in a ring of PRIME characteristic
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Based on work of Eric Canton
fSig = (f1, a1, e1) -> (
     R1:=ring f1;
     pp:= char ring f1;     
     1-(1/pp^(dim(R1)*e1))*
          degree( (ideal(apply(first entries vars R1, i->i^(pp^e1)))+ideal(fastExp(f1,a1) ))) 
)     

--- Calculates the x-int of the secant line between two guesses for the fpt
--- Input:
---	t - some positive rational number
---	b - the f-signature of (R,f^{t/p^e})
---     e - some positive integer
---     t1- another rational number > t
---	f - some polynomial in two or three variables in a ring of PRIME characteristic
---
--- Output:
---	fSig applied to (f,t1,e)
---	x-intercept of the line passing through (t,b) and (t1,fSig(f,t1,e))

threshInt = (f,e,t,b,t1)-> (
     b1:=fSig(f,t1,e);
{b1,xInt(t,b,t1/(char ring f)^e,b1)}
)

 "/Users/emilyewitt/m2.2012/F-sing/FS/"
 
 --this function guesses the FPT of ff.  It returns a list of all numbers in 
--the range suggested by nu(ff,e1) with maxDenom as the maximum denominator
guessFPT = (ff, e1, maxDenom) ->(
     nn := nu(ff, e1);
     pp := char ring ff;
     findNumberBetween({nn/(pp^e1-1), (nn+1)/(pp^e1)}, maxDenom)
)

---f-pure threshold estimation
---e is the max depth to search in
---finalCheck is whether the last isFRegularPoly is run (it is possibly very slow) 
FPTEst={finalCheck=> true, Verbose=> false} >> o -> (ff,ee)->(
     --error "help";
     if (isDiagonal(ff)==true) then ( if (o.Verbose==true) then print "Polynomial is diagonal."; diagonalFPT(ff))
     else if (isBinomial(ff)==true) then ( if  (o.Verbose==true) then print "Polynomial is binomial.";binomialFPT(ff))
     else
     (
     	  pp:=char ring ff;
     	  nn:=nu(ff,ee);
	  if  (o.Verbose==true) then print "nu's have been computed";
--	  if nn==0 then "Please pick a bigger integer 'e.'"
       	  if nn==0 then {0,1/pp}
     	  --error "help more";
     	  else if (isFRegularPoly(ff,(nn/(pp^ee-1)))==false) then ( if  (o.Verbose==true) then print "Found answer via nu/(p^e-1)."; nn/(pp^ee-1)) 
     	  else 
	  (
	        if  (o.Verbose==true) then print "nu/(p^e - 1) is not the fpt.";
	       --error "help most";
	       ak:=threshInt(ff,ee,(nn-1)/pp^ee,fSig(ff,nn-1,ee),nn); 
	       if  (o.Verbose==true) then print "Computed F-signatures.";
	       --  if (DEBUG == true) then error "help mostest";
	       if ( (nn+1)/pp^ee == (ak#1) ) then (if  (o.Verbose==true) then print "Slope crosses at max nu."; ak#1)
	       else if (o.finalCheck == true) then 
	       ( 
		    if  (o.Verbose==true) then print "Starting finalCheck.";
	       	    if ((isFRegularPoly(ff,(ak#1) )) ==false ) then ( if  (o.Verbose==true) then print "finalCheck successful"; (ak#1) )
	       	    else ( if  (o.Verbose==true) then print "finalCheck didn't find the fpt."; {(ak#1),(nn+1)/pp^ee})
	       )
	       else (
		    if  (o.Verbose==true) then print "finalCheck not run.";
		    {(ak#1),(nn+1)/pp^ee}
	       )
     	  )
     )
)




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
///

doc ///
     Key
     	fastExp 
     Headline
        Computes powers of elements in rings of characteristic p>0 using the Freshman's dream
     Usage
     	  fastExp(f,N) 
     Inputs
     	 f:RingElement
         N:ZZ
     Outputs
        :RingElement
///

doc ///
     Key
     	guessFPT 
     Headline
        Tries to guess the FPT (F-pure threshold) of f by using nu's, with depth controlled by e, with denominator bounded by d
     Usage
     	  guessFPT(f,e,d) 
     Inputs
     	 f:RingElement
         e:ZZ
	 d:ZZ
     Outputs
        :List
///

doc ///
     Key
     	 frobeniusPower
     Headline
        The following raises an ideal to the $p^e$th power
     Usage
     	  frobeniusPower(I,e) 
     Inputs
     	 I:Ideal
         e:ZZ
     Outputs
        :Ideal
///

doc ///
     Key
     	 nu
	 (nu,Ideal,ZZ)
	 (nu,RingElement,ZZ)
     Headline
        Gives$ \nu_I(p^e)$
     Usage
     	  nu(I,e)
	  nu(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
        :ZZ
///

doc ///
     Key
     	 nuList
	 (nuList,Ideal,ZZ)
	 (nuList,RingElement,ZZ)
     Headline
        Lists $/nu_I(p^d)$ for d = 1,...,e
     Usage
     	  nuList(I,e)
	  nuList(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
        :List
///

doc ///
     Key
     	 FPTApproxList
	 (FPTApproxList,Ideal,ZZ)
	 (FPTApproxList,RingElement,ZZ)
     Headline
        Gives a list of $\nu_I(p^d)/p^d$ for d=1,...,e
     Usage
     	  FPTApproxList(I,e)
	  FPTApproxList(f,e) 
     Inputs
     	 I:Ideal
	 f:RingElement
         e:ZZ
     Outputs
         :List
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
///

doc ///
     Key
     	 tauPoly
     Headline
        Computes the test ideal of $(R, f^t)$ when f is in a polynomial ring over a perfect field.
     Usage
     	  tauPoly(f,t) 
     Inputs
     	 f:RingElement
         t:QQ
     Outputs
        :Ideal
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
        :Ideal
///
doc ///
     Key
     	 fSig
     Headline
        Computes the F-signature for a specific value $a/p^e$
     Usage
     	  fSig(f,a,e)
     Inputs
     	 f:RingElement
	 a:ZZ
         e:ZZ
     Outputs
        :Ideal
///
doc ///
     Key
     	 [FPTEst,finalCheck,Verbose]
     Headline
         Atempts to compute the F-pure threshold, where e is the max depth to search in.  If finalCheck is false, then a last time consuming check won't be tried.  If it is true, it will be.  Verbose set to true displays verbose output.
     Usage
     	  FPTEst(f,e,finalCheck=>V,Verbose=>W)
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
	      finalCheck is a Boolean with default value True that determines whether the last isFRegularPoly is run (it is possibly very slow)
///
doc ///
     Key
     	 isSharplyFPurePoly
     Headline
        Checks whether (R, f^a) is F-pure at the prime ideal m
     Usage
     	 isSharplyFPurePoly(f,a,e,m)
     Inputs
     	 f:RingElement
	 a:ZZ
         e:ZZ
	 m:Ideal
     Outputs
         :Boolean
///
end