
--Computes I^{[1/p^e]}, we must be over a perfect field. and working with a polynomial ring
--This is a slightly stripped down function due to Moty Katzman.
ethRoot = (Im,e) -> (
--     print "Called ethRoot";
     if (isIdeal(Im) != true) then (
     	  print "You need to pass in an ideal"; print Im; assert false
     );
     if (not (e >= 0)) then (print "You must pass a nonnegative integer"; assert false);
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


-- the following function computes the test ideal of (R, f^(a/p^(e))) 
--when R is a polynomial ring.  Fortunately this is just (f^a)^{[1/p^e]}.
tauAOverPEPoly = (fm, a1, e1) -> (
     Im := ideal(fm^a1);
     --Once we have a fast power raising, we should use that instead of ^.
     eR(Im,e1)
)

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

denom = method();
denom QQ := x -> denominator x;
denom ZZ := x -> 1;

fracPart = (x) -> (x - floor(x))

aPower = (x,p) ->
(
a=1; while fracPart(denom(x)/p^a)==0 do a = a+1;
a-1
)

num = method();
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


--computes Non-F-Pure ideals for for (R, fm^{a/(p^{e1}-1)})
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




-------------------------------------------------
--***** What follows is worthless since the ******
--***** estimates from BMS08 are not good   ******
--***** enough for our purposes             ******
--------------------------------------------------




--here is a totaldegree function, it returns the total degree of a monomial.
totalDegree = (f1) -> (
     L1 := exponents(f1); -- get the list of exponents
     L2 := apply(L1, i->sum(i)); --get the total degree of each monomial
     max L2 -- return the biggest one
)

--the function finds the smallest e_0 such that pp^{e_0} > n1
intLog = (pp,n1) -> (
     ceiling(log(pp,n1))
)

--The gives an upper bound K such that all F-jumping numbers can be written as a/K
--for some a.  It returns a list (a,b) where K = p^a*(p^b - 1)
--The estimation is done based on Theorem 3.8 of BMS08 (Michigan Math Journal)
--We use the same terminology for the constants.
findFinestJumpingNumber = (f1) -> (
     Rm := ring f1; --base ring
     n:=rank source vars(Rm); --number of variables
     pp:=char(Rm); --characteristic
     d := totalDegree(f1); --find the "total" degree of d. degree would work fine unless
                           --there is a multigrading going on
     N := binomial(d+n,n); --this is a useful degree bound from BMS08.
     e0 :=  intLog(pp,d);
    -- print e0; print N; print d;
     {e0+N,N}
)

--finds the smallest t such that a1 < c/pp^t < b1 for some c. 
--returns c and t.
--assumes a1 <= b1
findAOverPTInRange = (a1,b1,pp) -> (
     if (b1 < a1) then print "findAOverPTInRange has bad inputs";
     dif := b1 - a1;
     invDif := 1/(b1-a1);
     
     t := intLog(pp,invDif);
     c := ceiling(a1*pp^t);
     
     {c,t}
)

--The following function estimates a different exponent for a polynomial 
--f1 in a regular ring.  In particular, it should find an exponent s such that
--tau(R, f^t1) = tau(R, f^s) and such that s = a/p^e.
--It uses the finestJumping# function.
findNearNonJumpingNumber = (f1, t1) -> (
     Rm := ring f1; --base ring
     pp:=char(Rm); --characteristic
     L1 := findFinestJumpingNumber(f1); -- factorization of the finest jumping #
     d1 := pp^(L1#0)*(pp^(L1#1) - 1); -- denominator of the finest jumping number
     d2 := denom t1; -- denominator of t1
      
     --first we handle the case when t1 can't be a jumping number
     --we replace t1 by the largest potential jumping number less than t1
     local ta;
     if ( d1 % d2 != 0 ) then (
     	  ta = floor(t1*d1)/d1;
	  d2 = denom ta;
     ) else ta = t1;

     L2 := divideFraction(ta,pp); -- factorization of the denominator
     
     ne := findAOverPTInRange(ta,ta+(1/d1),pp)
)

--The following function estimates a different exponent for a polynomial 
--f1 in a regular ring.  In particular, it should find an exponent s such that
--tau(R, f^t1) = tau(R, f^s) and such that s = a/(p^e-1).
--It uses the finestJumping# function.
findNearNonJumpingNumberAlt = (f1,t1) -> (
     Rm := ring f1; --base ring
     pp:=char(Rm); --characteristic
     L1 := findFinestJumpingNumber(f1); -- factorization of the finest jumping #
    -- print L1;
     d1 := pp^(L1#0)*(pp^(L1#1) - 1); -- denominator of the finest jumping number
     d2 := denom t1; -- denominator of t1
      
     --first we handle the case when t1 can't be a jumping number
     --we replace t1 by the largest potential jumping number less than t1
     local ta;
     if ( d1 % d2 != 0 ) then (
     	  ta = floor(t1*d1)/d1;
	  d2 = denom ta;
     ) else ta = t1;

     L2 := divideFraction(ta,pp); -- factorization of the denominator
    -- print ta;
     --this then turns p^a/(p^b*(p^c - 1)) into p^a/( (p^b - 1)*(p^c - 1) )
     --first we need to set our actual a,b,c's.
     a1 := lift( (L2#0)*(pp^( (L1#0) - (L2#1) ))*(pp^(L1#1) - 1)/(pp^(L2#2)-1), ZZ);
     b1 := L1#0;
     c1 := L1#1;
     
     
     a1/((pp^b1 - 1)*(pp^c1 - 1))
)