newPackage(
     "Invariants",
     Version => "0.1",
     Date => "August 6, 2012",
     Authors => {{Name => "Federico Galetto",
     	       Email => "galetto.federico@gmail.com",
	       HomePage => "http://www.math.neu.edu/~fgaletto/"}},
     Headline => "compute invariants of linearly reductive groups",
     DebuggingMode => true
     )

needsPackage"SimpleDoc"

export {derksen}

--copied from IntegralClosure; used to make variables from a string
fixvarname = s -> if instance(s,String) then getSymbol s else s

derksen = method(TypicalValue => Ideal,
     Options=>{
	  Variable => "w"
	  }
     )
--Derksen's algorithm for generators of invariants
--Inputs:
--I: vanishing ideal of linearly reductive group G
--A: matrix of a G-representation V
--Outputs:
--J: ideal of G-invariants in the polynomial ring of V
derksen (Ideal, Matrix) := Ideal => o -> (I, A) -> (
     P := ring I;
     kk := coefficientRing P;
     n := numColumns A;
     Q := kk(monoid [(fixvarname o.Variable)_1..(fixvarname o.Variable)_n]); --this ring will contain the invariants
     y := local y;
     R := P ** Q ** kk[y_1..y_n]; --this ring is used for some Groebner basis computations
     phi := map(R,P); --inclusion of P into R
     rho := map(R,Q); --inclusion of Q into R
     psi := map(Q,R); --projection of R onto Q
     use R;
     X := genericMatrix(R,rho(first gens Q),n,1);
     Y := genericMatrix(R,y_1,n,1);
     U := Y - (transpose phi(A))*X;
     B := eliminate(phi(I) + ideal(U),apply(gens P,p->phi(p)));
     return psi(B);
     )

beginDocumentation()
doc ///
     Key
     	  Invariants
     Headline
     	  compute invariants of linearly reductive groups
     Description
     	  Text
     	       This package computes invariants of linearly reductive groups using an algorithm by Derksen (see "Derksen, Kemper - Computational Invariant Theory, Springer, 2002").
///

doc ///
     Key
     	  derksen
	  (derksen,Ideal,Matrix)
     Headline
     	  apply Derksen's algorithm to obtain generators for the ideal of invariants
     Usage
     	  J = derksen(I,A)
     Inputs
     	  I:Ideal
	       the vanishing ideal of a linearly reductive group $G$ viewed as an affine variety
	  A:Matrix
	       over the ring of {\tt I} which defines a rational action of $G$ on finite dimensional representation $V$
	  Variable=>Symbol
	       lets you provide your own symbol for the subscripted variables in the coordinate ring of $V$
     Outputs
     	  J:Ideal
	       containing all $G$-invariant polynomials in the coordinate ring of $V$
     Description
     	  Text
	       Uses the algorithm of Derksen, as described in "Derksen, Kemper - Computational Invariant Theory, Springer, 2002", to get generators of
	       the ideal of $G$-invariant functions on a finite dimensional representation $V$.
	       $G$ can be any linearly redutive group which we view as
	       an affine variety in some affine space. {\tt I} is then an ideal inside the coordinate ring
	       of that affine space which has $G$ has vanishing locus (hint: choose the smallest possible affine space 
	       and equations of the smallest possible degrees as Groebner basis computations will be involved).
	       The matrix {\tt A} describes the action of $G$ on $V$. It must be a matrix over the ring of {\tt I}.
	       Think of it as the image of an element of $G$ under the map $G\rightarrow GL(V)$ which defines
	       the representation structure of $V$.
     Caveat
     	       The generators returned by this algorithm may not be invariants!
	       To obtain invariants use the Reynolds operator (not yet implemented).
     
///

end