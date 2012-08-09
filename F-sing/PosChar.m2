newPackage( "PosChar",
Version => "1.0", Date => "August 5, 2012", Authors => {
     {Name => "Karl Schwede",
     Email => "",
     HomePage => ""
     },
     {Name=> "Emily Witt",
     Email=> "",
     HomePage => ""
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
     "aPower"
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


-----------------------------------------------------------------
--*************************************************************--
--Functions for computing the F-pure threshold of a diagonal   --
--or binomial hypersurface using the algorithms of D. Hernandez--                      
--***********************************************************----
-----------------------------------------------------------------

--Gives the e-th digit of the non-terminating base p expansion of x in [0,1] 
digit = (e, x, p) -> 
(
     y := 0;
     if fracPart(p^e*x) != 0 then y = floor(p^e*x) - p*floor(p^(e-1)*x);
     if fracPart(p^e*x) == 0 then y = floor(p^e*x) - p*floor(p^(e-1)*x) - 1;
     if fracPart(p^(e-1)*x) == 0 then y = p-1;
     y
)

--Gives the e-th truncation of the non-terminating base p expansion of x in [0,1] as a fraction
truncation = (e,x,p) -> 
(
     y:=0; 
     for i from 1 to e do y = y + digit(i,x,p)/p^i;
     y
)

--Gives the first e digits of the non-terminating base p expansion of x in [0,1] as a list
truncationBaseP = (e,x,p) -> 
(
     L := new MutableList;
     for i from 0 to e-1 do L#i = digit(i+1,x,p);
     L
)


--Given a rational number x, if a is the power of p dividing its denomiator, finds an integer b so that p^a(p^b-1)*a is an integer
bPower = (n,p) ->
(
     if aPower(n,p)>0 then n = n*p^(aPower(n,p));
     denom(n)
)

--Given a vector w={x,y}, x and y rational in [0,1], returns a number of digits such that it suffices to check to see if x and y add without carrying in base p
carryTest = (w,p) ->
(
     c := 0; for i from 0 to #w-1 do c = max(c, aPower(w#i, p));
     d := 1; for j from 0 to #w-1 do if bPower(w#j, p)!=0 then d = lcm(d, bPower(w#j, p));
     c+d+1
)

--Given a vector w={x,y} of rational integers in [0,1], returns the first spot e where the x and y carry in base p; i.e., (the e-th digit of x)+(the e-th digit of y) >= p
firstCarry := (w,p) ->
(
     zeroTest := false;
     carry:=0;
     i:=0;
     for j from 0 to #w-1 do if w#j == 0 then zeroTest = true;
     if zeroTest == true then carry = -1 else
     d := 0;
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

--Computes the F-pure threshold of a diagonal hypersurface x_1^(a_1) + ... +x_n^(a_n) using D. Hernandez' algorithm
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

--Given a polynomial f, outputs a list of multi-degrees (under the usual grading) of f as lists
multiDegree = f ->
(
     variables := first entries vars ring f;
     apply(terms f, g -> apply(#variables, i ->degree(variables#i,g)))
)

--Determines whether a polynomial f is diagonal; i.e. of the form x_1^(a_1)+...+x_n^(a_n) (up to renumbering variables)
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



---f-pure threshold estimation
---e is the max depth to search in
---finalCheck is whether the last isFRegularPoly is run (it is possibly very slow) 
FPTEst={finalCheck=> true} >> o -> (ff,ee)->(
     --error "help";
     if (isDiagonal(ff)==true) then (diagonalFPT(ff))
    -- else if (isBinomial(ff)==true) then (binomialFPT(ff))
     else
     (
     	  pp:=char ring ff;
     	  nn:=nu(ff,ee);
	  if nn==0 then "Please pick a bigger integer 'e.'"
     	  --error "help more";
     	  else if (isFRegularPoly(ff,(nn/(pp^ee-1)))==false) then nn/(pp^ee-1)
     	  else 
	  (
	       --error "help most";
	       ak:=threshInt(ff,ee,(nn-1)/pp^ee,fSig(ff,nn-1,ee),nn); 
	       --  if (DEBUG == true) then error "help mostest";
	       if ( (nn+1)/pp^ee == (ak#1) ) then (ak#1)
	       else if (o.finalCheck == true) then 
	       ( 
	       	    if ((isFRegularPoly(ff,(ak#1) )) ==false ) then ( (ak#1) )
	       	    else {(ak#1),(nn+1)/pp^ee} 
	       )
	  else {(ak#1),(nn+1)/pp^ee}
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
        :List
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
        :QQ
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
     	 [FPTEst,finalCheck]
     Headline
         Atempts to compute the F-pure threshold, where e is the max depth to search in
     Usage
     	  FPTEst(f,e,finalCheck=>V)
     Inputs
     	 f:RingElement
         e:ZZ
	 V:Boolean
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