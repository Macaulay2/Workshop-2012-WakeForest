newPackage(
        "WaringDecomp",
        Version => "1.0",
        Date => "August 11, 2012",
        Authors => {{Name => "Luke Oeding and Giorgio Ottaviani",
                  Email => "oeding@math.berkeley.edu",
                  HomePage => "http://www.math.berkeley.edu/~oeding/"}},
        Headline => "Compute the Waring decomposition via Sylvester's Catalecticant Algorithm. See Iarobino-Kanev or Oeding-Ottaviani",
        DebuggingMode => true
        )
needsPackage"SimpleDoc"


export {Cat, Kos}
catalecticant := (ff,xac,xaf) -> diff(transpose xac,diff(xaf,ff));

Cat = method(TypicalValue => RingElement)--, Options => {Variable => "w"})
--catalecticant = method(TypicalValue=>RingElement)
--catalecticant (Matrix, Matrix ,RingElement) :=(xac,xaf,f)->contract(transpose xac,contract(xaf,f));
Cat RingElement := f -> (
     --- f is input, R my ring, n-dimensional(projective), KK is the ground field,
     --- d is the degree of f, ...
     --- complain if f is not homogeneous
     R := ring f;
     KK := (R.baseRings)_1;
     n := dim R-1 ;
     d := (degree f)_0;
     af := floor(d/2);
     ac := ceiling(d/2);
     xaf := basis(af,R);
     xac := basis(ac,R);	
     -- construct the most square possible catalecticant matrix
     --catalecticant = method(TypicalValue=>RingElement);
     K:= gens kernel catalecticant(f,xac,xaf); print("rank",(numrows K)-(rank K));
     I := ideal(xaf*K);
     L := decompose saturate I; --print(L);
     b := basis(1,R);
     S := R**KK(monoid[local w_0..symbol w_(length L -1)]);
     bS := sub(b,S); 
     linformsc:= apply(length L,i-> 
	 (bS*(mingens kernel diff(bS, 
			      transpose mingens sub(L_i,S))))_(0,0));
     dformsc:= apply(length L,i-> S_(i+n+1)*linformsc_i^d );
     fc := sum apply(length L, i->dformsc_i );-- print(fc,formsc);
     --print(fc);
     Ic := ideal(sub(diff(basis(d,R),f),S) - diff(sub(basis(d,R),S),fc));--print(Ic);
     Vc := decompose saturate Ic; --print(Vc);
     print("the linear forms in the decomposition are (up to scale) the following:");
     print(apply(linformsc, p ->toString sub( substitute(p,S/Vc_0),R)));
     print("the output produces d-th powers of linear forms with correct constants");
     print("the sum of the output is the original form");
     apply(dformsc, p ->sub( substitute(p,S/Vc_0),R))
     --FF := sub( substitute(fc,S/Vc_0),R)
)
end


restart
loadPackage"WaringDecomp"
S = QQ[x_0..x_2]
Cat(x_0^5+x_1^5 + x_2^5)
f=3*(x_0-x_1)^5 + x_2^5 + (x_1-3*x_2)^5
KC= Cat(f)

KK = QQ
n=2
d=5  -- this is the degree
s=5  -- this is the test rank
R  = KK[x_0..x_n];
ff = 0;
for i from 1 to s do{ll_i=random(1,R); print(toString(ll_i)); ff= ff+ll_i^d;} 
Cat(ff)
sum(Cat(ff))-ff
