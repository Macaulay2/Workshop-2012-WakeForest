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
a=1; while fracPart(denom(x)/p^a)==0 do a = a+1;
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


----------------------------------------------------------------
--************************************************************--
--Functions for computing test ideals, and related objects.   --
--************************************************************--
----------------------------------------------------------------


--Computes I^{[1/p^e]}, we must be over a perfect field. and working with a polynomial ring
--This is a slightly stripped down function due to Moty Katzman.
ethRoot = (Im,e) -> (
     if (isIdeal(Im) != true) then (
     	  print "ethRoot: You need to pass in an ideal"; print Im; assert false
     );
     if (not (e >= 0)) then (print "ethRoot: You must pass a nonnegative integer"; assert false);
     Rm:=ring(Im); --Ambient ring
     pp:=char(Rm); --characteristic
     Sm:=coefficientRing(Rm); --base field
     n:=rank source vars(Rm); --number of variables
     vv:=first entries vars(Rm); --the variables
     R1:=Sm[vv, Y_1..Y_n, MonomialOrder=>ProductOrder{n,n},MonomialSize=>32]; -- a new ring with new variables
     J0:=apply(1..n, i->Y_i-substitute(vv#(i-1)^(pp^e),R1)); -- 
     --print J0;
     M:=toList apply(1..n, i->Y_i=>substitute(vv#(i-1),R1));

     G:=first entries compress( (gens substitute(Im,R1))%gens(ideal(J0)) );

     L:=ideal 0_R1;
     apply(G, t->
	  {
    	       L=L+ideal((coefficients(t,Variables=>vv))#1);
	  });
     L2:=mingens L;
     L3:=first entries L2;
     L4:=apply(L3, t->substitute(t,M));
     use(Rm);
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
     fpow := fm^a2;
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
--Auxiliary functions for F-signature computations.   --
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
     
fSig = (e, a, f) -> (
if not isHomogeneous f   
     then error "expected a homogeneous f";     
p= char ring f;     
1-(1/p^(dim(ring f)*e))*degree((ring f)^1/(ideal(apply(first entries vars R, i->i^(p^e)))+ideal(f^a))))     

--- Estimates the F-pure threshold
--- Input:
---	t - some positive rational number
---	b - the f-signature of (R,f^{t/p^e})
---     e - some positive integer
---     t1- another rational number > t
---	f - some HOMOGENEOUS polynomial in two or three variables in a ring of PRIME characteristic
---
--- Output:
---	fSig applied to (e,t1,f)
---	x-intercept of the line passing through (t,b) and (t1,fSig(e,t1,f))

threshEst = (e,t,b,t1,f)-> (
{b1=fSig(e,t1,f),xInt(t,b,t1,b1)}
)