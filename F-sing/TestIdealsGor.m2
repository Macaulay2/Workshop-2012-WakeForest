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

--this outputs the test ideal of a (Q-)Gorenstein ring (with no pair or exponent)
--ek is the number such that the index divides (p^ek - 1).  
--It actually spits out the appropriate stable/fixed ideal inside the ambient ring.
tauQGorAmb = (Rk, ek) -> (
     Sk := ambient Rk;
     pp := char Sk;
     Ik := ideal Rk;
     Jk := findTestElementAmbient(Rk);
     hk := findQGorGen(Rk, ek);
     IP := ideal(0_Sk); -- this is going to be the old value.
     IN := Jk; -- the new value
     --the plan is to make an ascending chain of ideals that eventually stabilizes
     --our initial value is something contained in the test ideal.  
     while (IN != IP) do(
	  IP = IN;
	  IN = eR(ideal(hk)*IP,ek)+IP
     );

     --return the final ideal (note, this is an ideal of Sk, not Rk, sub it back to 
     --Rk to make it in Rk).
     trim IP
)

--for Gorenstein rings, or if ek can be taken to be 1.
tauGorAmb = (Rk) -> tauQGorAmb(Rk, 1)

--this computes the test ideal
--tau(Rk, f^(a1/(p^e1 - 1))) but leaves it lifted to the ambient space, if Rk = Sk/I, it
--yields an ideal in Sk.
--here ek is a number such that the index of K_R divides (p^ek - 1).  If R is Gorenstein, 
--you may set this 1.
tauAOverPEMinus1QGor = (Rk, ek, fk, a1, e1) -> (
     Sk := ambient Rk;
     pp := char Sk;
     Ik := ideal Rk;
     Jk := findTestElementAmbient(Rk);
     et := lcm(ek, e1);
     hk := (findQGorGen(Rk, ek))^(numerator ((pp^et - 1)/(pp^ek - 1)));  
       --hk for higher powers are simply appropriate powers of hk for lower powers, 
       --may as well take advantage of that
     fm := lift(fk, Sk);
     a3 := numerator (a1*(pp^et - 1)/(pp^e1 - 1)); --we need to use a common e for both the 
                                               --index of R and of our divisor.
     
     a2 := a3 % (pp^et - 1);
     k2 := a3 // (pp^et - 1); --it seems faster to use the fact 
                              --that tau(f^(1+k)) = f*tau(f^k) 
     fpow := fm^a2; 
     
    
     IP := ideal(0_Sk); -- this is going to be the old value.
     IN := Jk*ideal(fm); -- the new value, something in the test ideal
     
     while (IN != IP) do(
	  IP = IN;
	  IN = eR(ideal(fpow*hk)*IP,et)+IP
     );

     trim IP*ideal(fm^k2)    
)


--this computes the test ideal of (Rk, fk^t1).  Here we assume the index of the canonical
--divides (p^ek - 1)
tauQGor = (Rk, ek, fk, t1) -> (
     Sk := ambient Rk;
     pp := char Sk;
     L1 := divideFraction(t1,pp); --this breaks up t1 into the pieces we need
     hk := findQGorGen(Rk, ek); --this is being called twice sometimes, fix it.
     I1 := ideal(0_Sk); I2 := ideal(0_Sk);
     fm := lift(fk, Sk);
     --first we compute tau(fk^{a/(p^c-1)})
     if (L1#2 != 0) then 
          I1 = tauAOverPEMinus1QGor(Rk,ek,fk,L1#0,L1#2) 
     else (
	  I1 = ideal(fm^(L1#0))*tauQGorAmb(Rk,ek)
      );
 
      --we do a check to see if the indexes match well enough...
      --the problem is we can only take ek'th roots, but my t1 might be something like
      --1/p.  I fix that by acting as if t1 is p^(ek-1)/p^ek.  
      --We can take an ekth root of that.  Often, t1 = 1, so that will keep things easy.
      pPow := L1#1;
      remain := pPow % ek;
      dualRemain := ek - remain;
      if (remain != 0) then (
           I1 = I1*ideal(fm^(pp^dualRemain) );
	   pPow = pPow + dualRemain;
      ); --note in the end here, ek divides pPow.
 
     --I also need to adjust hk if it is different from pPow.
     if (hk != pPow) then hk = hk^(numerator ((pp^pPow - 1)/(pp^ek - 1)));
 
     --now we compute the test ideal using a generalization of the fact that 
     --tau(fm^t)^{[1/p^a]} = tau(fm^(t/p^a))
     if (L1#1 != 0) then
          I2 = ethRoot(I1*ideal(hk), pPow) 
     else 
          I2 = I1;
	  
     trim sub(I2, Rk)
)
