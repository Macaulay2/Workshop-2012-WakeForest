--Test ideals in Gorenstein rings scratch document

load "FS.m2"

-- This function computes the element in the ambient ring S of R=S/I such that
-- I^{[p^e]}:I = (f) + I^{[p^e]}.  
-- If there is no such unique element, the function returns zero.

findQGorGen = (Rk,ek) -> (
     Sk := ambient Rk; -- the ambient ring
     Ik := ideal Rk; -- the defining ideal
     pp := char Sk; --the characteristic
     Ikpp := frobeniusPower(Ik,ek);
     
     J1 := trim (Ikpp : Ik);
     Tk := Sk/Ikpp;
     
     J2 := trim sub(J1, Tk);
     
     Lk := first entries gens J2;
     
     nk := #Lk;
     val := 0_Sk;
     
     if (nk != 1) then (
	  print "findGorGen: this ring does not appear to be (Q-)Gorenstein, or
	   you might need to work on a smaller chart.  Or the index may not divide p^e-1
	   for the e you have selected.";
     )
     else (
	  val = lift(Lk#0, Sk);
     );    
     val 
)


--the function is like the 
--Q-Gorenstien one but assume the index is 1 (or at least divides p-1).
findGorGen = Rk -> findQGorGen(Rk,1)

--this finds a test element of a ring R = k[x, y, ...]/I (or at least an ideal 
--containing a nonzero test element).  It views it as an element of the ambient ring
--of R.  It returns an ideal with some of these elements in it.
--One could make this faster by not computing the entire jacobian / singular locus
--instead, if we just find one element of the jacobian not in I, then that would also work
--and perhaps be substantially faster
findTestElementAmbient = Rk -> (
     --Sk := ambient Rk;
     -- Ik := ideal Sk;
     
     Jk := ideal singularLocus(Rk);
     if (isSubset(Jk, ideal Rk) == true) then 
          error "findTestElementAmbient: No test elements found, is the ring non-reduced?";
	  
     
     Jk          
)

--this function finds the smallest phi-stable ideal containing the given ideal Jk
--in a polynomial ring Sk.
--Jk is the given ideal, ek is the power of Frobenius to use, hk is the function to multiply 
--trace by to give phi.  phi(_) = Tr^(ek)(hk._)
ascendIdeal = (Jk, hk, ek) -> (
     print ".";
     Sk := ring Jk;
     pp := char Sk;
     IN := Jk;
     IP := ideal(0_Sk);
     --we want to make the largest ideal that is phi-stable, following Moty Katzman's idea
     --we do the following
     while (isSubset(IN, IP) == false) do(
     	  IP = IN;
	  IN = eR(ideal(hk)*IP, ek)+IP
     );

     --trim the output
     trim IP
)

--this outputs the test ideal of a (Q-)Gorenstein ring (with no pair or exponent)
--ek is the number such that the index divides (p^ek - 1).  
--It actually spits out the appropriate stable/fixed ideal inside the ambient ring.
tauQGorAmb = (Rk, ek) -> (
     Jk := findTestElementAmbient(Rk);
     hk := findQGorGen(Rk, ek);

     ascendIdeal(Jk,hk,ek)
)

--for Gorenstein rings, or if ek can be taken to be 1.
tauGorAmb = (Rk) -> tauQGorAmb(Rk, 1)

--this is an internal function
--it is used to compute the test ideals of pairs (R, fm^(a1/p^e1-1)) where
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
     
     --TODO:  Experiment with ascending this ideal
     Iasc := ascendIdeal(Jk*ideal(fm), fpow*hk1, et);
    
     Iasc*ideal(fm^k2)    
)


--this computes the test ideal of (Rk, fk^t1).  Here we assume the index of the canonical
--divides (p^ek - 1)
tauQGor = (Rk, ek, fk, t1) -> (
     Sk := ambient Rk;
     pp := char Sk;
     L1 := divideFraction(t1,pp); --this breaks up t1 into the pieces we need
     hk := findQGorGen(Rk, ek); --this is being called twice sometimes, fix it.
     Jk := findTestElementAmbient(Rk); --this finds some test elements (lifted on the ambient
                                       --ring).  Right now it is slow because of a call to 
				       --singularLocus (ie, computing a Jacobian).
     I1 := ideal(0_Sk); I2 := ideal(0_Sk);
     fm := lift(fk, Sk);
     a1 := L1#0; e1 := L1#2; pPow := L1#1;
     d1 := pp^(pPow); if (e1 != 0) then d1 = d1*(pp^e1-1);
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
     --tau(fm^t)^{[1/p^a]} = tau(fm^(t/p^a))
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
          if (hk != pPow) then hk = hk^(numerator ((pp^pPow - 1)/(pp^ek - 1)));
 
          I2 = ethRoot(I1*ideal(hk), pPow) 
     )
     else --unless we don't have any p's in the denominator
          I2 = I1;
	  
     sub(I2, Rk)*ideal(fk^k2)
)
