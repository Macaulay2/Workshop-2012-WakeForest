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
     E=basePExp(N,char ring f);
     product(apply(#E, e -> (sum(apply(terms f, g->g^(p^e))))^(E#e) ))
)


--computes the Frobenius power of an ideal

frobeniusPower = (I,e) ->
(
     p = char ring I;
     local Frob;
     Gens = first entries gens I;
     if #Gens==0 then Frob = ideal(0_R) else Frob = ideal(apply(Gens, g -> g^(p^e)));
     Frob
)     


{* Old way of computing "\nu"s; less efficient

nuListOld = (I,e) ->
(
     m = ideal(first entries vars ring I); 
     L = new MutableList;
     N=0;
     for d from 1 to e do 
     (	  
	  while isSubset(ideal(apply(first entries gens I, g->fastExp(g, N, char ring I))), frobeniusPower(m,d))==false do N = N+1;
     	  L#(d-1) = N-1;
	  N = p*(N-1)
     );
     L
)

*}


--Lists \nu_I(p^d) for d = 1,...,e 

nuList = method();
nuList (Ideal,ZZ) := (I,e) ->
(
     m = ideal(first entries vars ring I); 
     L = new MutableList;
     N=0;
     for d from 1 to e do 
     (	  
	  J = ideal(apply(first entries gens I, g->fastExp(g, N, char ring I)));
	  N=N+1;
	  while isSubset(I*J, frobeniusPower(m,d))==false do (N = N+1; J = I*J);
     	  L#(d-1) = N-1;
	  N = p*(N-1)
     );
     L
)
nuList (RingElement,ZZ) := (f,e) -> nuList(ideal(f),e)

--Gives \nu_I(p^e)

nu = method();
nu (Ideal,ZZ) := (I,e) -> (nuList(I,e))#(e-1)
nu (RingElement, ZZ) := (f,e) -> nu(ideal(f),e)

--Gives a list of \nu_I(p^d)/p^d for d=1,...,e

FPTApproxList = method();
FPTApproxList (Ideal,ZZ) := (I,e) -> apply(#nuList(I,e), i->((nuList(I,e))#i)/p^(i+1)) 
FPTApproxList (RingElement,ZZ) := (f,e) -> FPTApproxList(ideal(f),e)


