newPackage(
	"Kstability",
    	Version => "0.1", 
    	Date => "August 22, 2011",
    	Authors => {
	     {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
	     {Name => "Gabor Szekelyhidi", Email => "gszekely@nd.edu", HomePage => "http://www.nd.edu/~gszekely"},
	     },
    	Headline => "Package for K-stability calculations",
    	DebuggingMode => true
    	)
 
needsPackage"SimpleDoc" 
 
export {
     centralFiber,
     futaki,
     chow
       }


centralFiber = method(TypicalValue=>Ideal)
centralFiber(Ideal, List) := (I, W) ->(
     -- compute flat limit
     n:=#W;
     R:=ring(I);
     degs := apply (n, j-> {1,W_j});
     S := QQ[gens R, Weights => W, Degrees => degs,Global=>false];
     f := map (R/I, S, gens R);
     J := ker f;
     leadJ := ideal leadTerm(1,J);
     g := map (S/leadJ, R, gens S);
     ker g
)    


futaki = method(TypicalValue=>QQ)
futaki(Ideal, List) := (I, W) ->(
     -- compute flat limit
     Wmin := min W;
     m:=#W;
     W = apply(m, j -> W_j - Wmin); -- make weights non-negative
     R:=ring(I);
     degs := apply (m, j-> {1,W_j});
     S := QQ[gens R, Weights => W, Degrees => degs];
     f := map (R/I, S, gens R);
     J := ker f;
     n := dim J;  -- original ideal in ring with new multigrading including weights of action
     newIdeal := ideal leadTerm(1,J); -- initial ideal w.r.t degree
     -- 
     F := hilbertSeries newIdeal;
     numF := value numerator F;
     denomF := value denominator F;
     HilbRing := ring numF;
     HilbVar0 := HilbRing_0;
     HilbVar1 := HilbRing_1;
     P1 := numerator reduceHilbert sub(F, {HilbVar1 => 1});
     d0 := lift(value sub(P1, {HilbVar0 => 1}), ZZ);
     d1 := -lift(value sub(diff(HilbVar0, P1), {HilbVar0 => 1}), ZZ);
     a0 := d0 / (n-1)! ;
     a1 := (d1 + n/2*d0 ) / (n-2)!;
     numF1 := sub(diff(HilbVar1, numF)*denomF - diff(HilbVar1, denomF)*numF, {HilbVar1 => 1});
     denomF1 := sub(denomF^2, {HilbVar1 => 1});
     P2 := (numF1 * (1-HilbVar0)^(n+1)) // denomF1;
     w0 := lift(value sub(P2, {HilbVar0 => 1}), ZZ);
     w1 := -lift(value sub(diff(HilbVar0, P2), {HilbVar0 => 1}), ZZ);
     b0 := w0 / n! ;
     b1 := (w1 + (n+1)/2*w0 ) / (n-1)!;
     b1 - a1*b0/a0
    )


--
chow = method(TypicalValue=>QQ)
chow(Ideal, List) := (I, W) ->(
     -- compute flat limit
     Wmin := min W;
     m:=#W;
     W = apply(m, j -> W_j - Wmin); -- make weights non-negative
     R:=ring(I);
     degs := apply (m, j-> {1,W_j});
     S := QQ[gens R, Weights => W, Degrees => degs];
     f := map (R/I, S, gens R);
     J := ker f;
     n := dim J;
     newIdeal := ideal leadTerm(1,J);
     -- 
     F := hilbertSeries newIdeal;
     numF := value numerator F;
     denomF := value denominator F;
     HilbRing := ring numF;
     HilbVar0 := HilbRing_0;
     HilbVar1 := HilbRing_1;
     P1 := numerator reduceHilbert sub(F, {HilbVar1 => 1});
     d0 := lift(value sub(P1, {HilbVar0 => 1}), ZZ);
     a0 := d0 / (n-1)! ;
     numF1 := sub(diff(HilbVar1, numF)*denomF - diff(HilbVar1, denomF)*numF, {HilbVar1 => 1});
     denomF1 := sub(denomF^2, {HilbVar1 => 1});
     P2 := (numF1 * (1-HilbVar0)^(n+1)) // denomF1;
     w0 := lift(value sub(P2, {HilbVar0 => 1}), ZZ);
     b0 := w0 / n! ;
     sum(W)/#W - b0/a0
    )

-- example of defining a type


----------------------------------
-- DOCUMENTATION
----------------------------------

beginDocumentation()


doc ///
  Key 
      Kstability
  Headline 
      a package for K-stability computations
  Description
      Text
          This package contains functions to compute the Futaki and Chow invariants 
	  of test-configurations. 
///






doc ///
     Key     
     	  futaki
	  (futaki, Ideal, List)
     Headline
     	  computes the Futaki invariant
     Usage
     	  n = futaki(I,w)
     Inputs
     	  I : Ring
	       an ideal in a polynomial ring
	  w : List
	       a list of weights 
     Outputs
     	  n : QQ
	       a rational number
     Description
    	  Text
	       This function computes the Futaki invariant of the test-configuration obtained by 
	       acting by the C* action with the given weights, inside the projective space given by the polynomial
	       ring.
	  Example
	       R = QQ[a,b,c]
	       I=ideal (a*c-b^2)
	       w = {2,1,1}
	       futaki(I,w)
     SeeAlso
     	  centralFiber
	  chow
     	  
///

doc ///
     Key     
     	  centralFiber
	  (centralFiber, Ideal, List)
     Headline
     	  computes the central fiber of a test-configuration
     Usage
     	  J = centralFiber(I,w)
     Inputs
          I : Ideal
	       an ideal in a polynomial ring
	  w : List
	       a list of weights 
     Outputs
     	  J : Ideal
	       an ideal in R
     Description
    	  Text
	       This function computes the central fiber of the test-configuration obtained by 
	       acting by the C* action with the given weights, inside the projective space given by the polynomial
	       ring.
	  Example
	       R = QQ[a,b,c]
	       I= ideal(a*c-b^2)
	       W = {2,1,1}
	       centralFiber(I,W)
     SeeAlso
     	  futaki
	  chow
     	  
///

doc ///
     Key     
     	  chow
	  (chow, Ideal, List)
     Headline
     	  computes the Chow invariant
     Usage
     	  n = chow(I,w)
     Inputs
     	  I : Ideal
	       an ideal in a polynomial ring
	  w : List
	       a list of weights 
     Outputs
     	  n : QQ
	       a rational number
     Description
    	  Text
	       This function computes the Chow invariant of the test-configuration obtained by 
	       acting by the C* action with the given weights, inside the projective space given by the polynomial
	       ring.
	  Example  
	       R = QQ[a,b,c]
	       I=ideal (a*c-b^2)
	       W = {2,1,1}
	       chow(I,W)
     SeeAlso
     	  centralFiber
	  futaki
     	  
///

---------------------------
-- Tests
---------------------------

TEST ///
    R = QQ[x,y,z]
    assert ( centralFiber(ideal(y^2 - x*z), {1,0,0}) == ideal(x*z) )
/// 
