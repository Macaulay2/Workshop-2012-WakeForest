newPackage(
        "PushForward",
        Version => "0.2", 
        Date => "August 7, 2012",
        Authors => {{Name => "Claudiu Raicu", 
                  Email => "craicu@math.princeton.edu", 
                  HomePage => "http://www.math.princeton.edu/~craicu"}},
        Headline => "push forwards of finite ring maps",
        DebuggingMode => true
        )

export {pushFwd}

protect symbol PushforwardOfRingMap;
protect symbol PushforwardOfModule;

pushFwd=method()
pushFwd(RingMap):=(f)->
(
     if f.cache.?PushforwardOfRingMap then f.cache.PushforwardOfRingMap else
     (
     	  A:=source f;
     	  B:=target f;     
     	  psh := pushAux f;
     	  matB:=psh_0;
     	  k:=psh_1;
     	  mapf:=psh_7;
     	  local ke;
     	  ke=kernel map(B^1,A^k,f,matB);
     	  f.cache.PushforwardOfRingMap = (A^k/ke,matB,mapf);
	  f.cache.PushforwardOfRingMap
	  )
     )

pushFwd(Module,RingMap):=(N,f)->
(
     if N.cache.?PushforwardOfModule then N.cache.PushforwardOfModule else
     (
     	  B:=target f;
     	  aN:=ann N;
     	  C:=B/aN;
     	  bc:=map(C,B);
     	  g:=bc*f;
          
	  matB:=(pushAux g)_0;
     	  N.cache.PushforwardOfModule = makeModule(N**C,g,matB);
	  N.cache.PushforwardOfModule
     	  )
     )

pushFwd(Ideal,RingMap) := (I,f) ->
(
     pushFwd(module I,f)
     )

pushFwd(ModuleMap,RingMap):=(d,f)->
(
     A:=source f;
     B:=target f;
     pols:=f.matrix;
     pM:=source d;
     pN:=target d;
     
     amn:=intersect(ann pM,ann pN);
     C:=B/amn;
     bc:=map(C,B);
     g:=bc*f;     
     M:=pM**C;
     N:=pN**C;
   
     psh:=pushAux g;
     (matB,k,R,I,mat,n,varsA,mapf) := psh;

     pushM := if M.cache.?PushforwardOfModule then M.cache.PushforwardOfModule else
                 (
		      M.cache.PushforwardOfModule = makeModule(M,g,matB);
		      M.cache.PushforwardOfModule
		      );
     pushN := if N.cache.?PushforwardOfModule then N.cache.PushforwardOfModule else
                 (
		      N.cache.PushforwardOfModule = makeModule(N,g,matB);
		      N.cache.PushforwardOfModule
		      );

          
     matMap:=symbol matMap;
     gR:=matB**matrix d;
     c:=numgens source gR;
     l:=numgens target gR;
     matMap=mutableMatrix(A,k*l,c);

     for i1 from 0 to c-1 do
     	  for i2 from 0 to l-1 do
	  (
       	       e:=mapf(gR_i1_i2);
	       for i3 from 0 to k-1 do matMap_(i2+l*i3,i1)=e_0_i3;	       
	   );

     map(pushN,pushM,matrix matMap)
     )

pushFwd(ChainComplex,RingMap) := (C,f) ->
(
     complete C;
     d := C.dd;
     chainComplex(apply(splice{min(C)+1..max(C)},i->pushFwd(d_i,f)))
     )

makeModule=method()
makeModule(Module,RingMap,Matrix):=(N,f,matB)->
(
     A := source f;
     B := target f;
     dA := degreeLength A;
     dB := degreeLength B;
     newA := local newA;
     newB := local newB;
     if dA == 0 then newA = newRing(A[],DegreeRank => dB) 
        else if dA < dB then newA = newRing(A,DegreeRank => dB) 
	else newA = A;
     fA := map(newA,A); fAi := map(A,newA);
     if dB == 0 then newB = newRing(B[],DegreeRank => dA) 
        else if dA > dB then newB = newRing(B,DegreeRank => dA) 
	else newB = B;
     fB := map(newB,B); fBi := map(B,newB);

     newN := fB**N;
     newmatB := fB matB;
     newf := map(newB,newA,(flatten entries fB(f.matrix)));
     
     auxN := ambient newN/image relations newN;
     ke := kernel map(auxN,,newf,newmatB**gens newN);
     fAi ** ((super ke)/ke)
     
--     auxN:=ambient N/image relations N;
--     ke:=kernel map(auxN,,f,matB**gens N);
--     (super ke)/ke
     )

pushAux=method()
pushAux(RingMap):=(f)->
(
     if f.cache.?PushforwardComputation then f.cache.PushforwardComputation else
     (
     	  A:=source f;
     	  B:=target f;
     	  pols:=f.matrix;
          
	  FlatA:=flattenRing A;
	  FA:=FlatA_0;
	  varsA:=flatten entries FlatA_1^-1 vars FA;
     	  FlatB:=flattenRing B;
     	  FB:=FlatB_0;
     	  varsB:=flatten entries FlatB_1^-1 vars FB;
     	  m:=numgens FA;
     	  n:=numgens FB;
     	  
	  pols=FlatB_1 pols_{0..(m-1)};
     	  
	  iA := ideal FA;
     	  RA := ring iA;
     	  iB := ideal FB;
     	  RB := ring iB;
     	  Rpols := lift(pols,RB);
     	  Rf := map(RB,RA,Rpols);
     	  
	  Igraph := graphIdeal(Rf,VariableBaseName => local X, MonomialOrder => ProductOrder {n,m});
     	  R := ring Igraph; --first n variables correspond to RB;
     	  IA := sub(iA,matrix{(gens R)_{n..n+m-1}});
     	  IB := sub(iB,matrix{(gens R)_{0..n-1}});
     	  I := Igraph + IA + IB;     	  
     	  inI:=leadTerm I;

     	  r := ideal(sub(inI,matrix{(gens R)_{0..n-1}|{m:0}}));
     	  for i from 1 to n do
	      if ideal(sub(gens r,matrix{{(i-1):0,1_R,(m+n-i):0}}))!=ideal(1_R) then
     	         error "map is not finite";
     	  
	  mat:=lift(basis(R/(r+ideal((gens R)_{n..n+m-1}))),R);
     	  k:=numgens source mat;
     	  matB:=sub(mat,matrix{varsB|toList(m:0_B)});
     	  
	  phi:=map(R,B,matrix{(gens R)_{0..n-1}});
     	  toA:=map(A,R,flatten{n:0_A,varsA});
     	  mapf:=(b)->(
	       (mons,cfs):=coefficients((phi b)%I,Monomials=>mat,Variables=>(gens R)_{0..n-1});
	       toA cfs	  
	       );
     
          f.cache.PushforwardComputation = (matB,k,R,I,mat,n,varsA,mapf);
	  f.cache.PushforwardComputation
	  )
     )

beginDocumentation()

document{
  Key => PushForward,
  Headline => "pushforward functor for finite ring maps",
  EM "PushForward", " is a package that implements the pushforward functor for finite ring maps",
  Caveat => "Works only for maps of rings finitely generated over a base field "
  }

document{
  Key => pushFwd,
  Headline => "push forward",
  "The push forward functor",
  UL {
       {TO (pushFwd,RingMap)," - for a finite ring map"},
       {TO (pushFwd,Ideal,RingMap), " - for an ideal"},
       {TO (pushFwd,Module,RingMap), " - for a module"},
       {TO (pushFwd,ModuleMap,RingMap), " - for a map of modules"},
       {TO (pushFwd,ChainComplex,RingMap)," - for a chain complex"}
     }
  }   

document{
  Key => (pushFwd,RingMap),
  Headline => "push forward of a finite ring map",
  Usage => "pushFwd f",
  Inputs => { "f" },
  Outputs => {{"a presentation of the target of ",TT "f", " as a module over the source"},{"the matrix of generators of the target of ",TT "f"," as a module over the source"},{"a map that assigns to each element of the target of ", TT "f"," its representation as an element of the pushed forward module"}},
  EXAMPLE lines ///
  kk = QQ
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  A = kk[a,d]
  F = map(R,A)
  pushFwd F
  ///
  }

document{
  Key => (pushFwd,Module,RingMap),
  Headline => "push forward of a module",
  Usage => "pushFwd(N,f)",
  Inputs => { "N", "f" },
  Outputs => {{"a presentation of ",TT "N", " as a module over the source of ",TT "f"}},
  TEX "Given a (not necessarily finite) ring map $f:A \\rightarrow{} B$ and a $B$-module $N$ which is finite over $A$, the function returns a presentation of $N$ as an $A$-module.",
  PARA{},
  EXAMPLE lines ///
  A = QQ[a,b,c]
  N = coker map(A^2,A^3,{{a+b,b+c,a+c},{a,b,c}})
  B = QQ[x,y]
  f = map(A,B,{a-b,b+c})
  M = pushFwd(N,f)
  ///
  }

document{
  Key => (pushFwd,Ideal,RingMap),
  Headline => "push forward of an ideal",
  Usage => "pushFwd(I,f)",
  Inputs => { "I", "f" },
  Outputs => {{"a presentation of ",TT "I", " as a module over the source of ",TT "f"}},
  TEX "Given a (not necessarily finite) ring map $f:A \\rightarrow{} B$ and an ideal $I$ of $B$ which is a finite $A$-module, the function returns a presentation of $I$ as an $A$-module.",
  PARA{},
  EXAMPLE lines ///
  kk = QQ
  A = kk[t]
  B = kk[x,y]/(x*y)
  I = ideal(x)
  f = map(B,A,{x})
  pushFwd(I,f)
  ///
  }

document{
  Key => (pushFwd,ChainComplex,RingMap),
  Headline => "push forward of a chain complex",
  Usage => "pushFwd(C,f)",
  Inputs => { "C", "f" },
  Outputs => {{"a chain complex ",TT "pushC", " over the source of ",TT "f"}},
  TEX "Given a (not necessrily finite) ring map $f:A \\rightarrow{} B$ and a chain complex $C$ of $B$-modules which are finite as $A$-modules, the function returns the pushed forward complex.",
  PARA{},
  EXAMPLE lines ///
  kk = QQ
  A = kk[u,v,w]
  B = kk[x,y,z]
  f = map(B,A,{x+y,y+z,z+x})
  M = B^1/ideal(x,y)++B^1/ideal(y,z)++B^1/ideal(z,x);
  C = res M
  C.dd
  pushC = pushFwd(res M,f)
  pushC.dd
  ///
  }

document{
  Key => (pushFwd,ModuleMap,RingMap),
  Headline => "push forward of a map of modules",
  Usage => "pushFwd(d,f)",
  Inputs => { "d", "f" },
  Outputs => {{"the push forward of the map d"}},
  EXAMPLE lines ///
  kk = QQ
  R = kk[a,b]
  S = kk[z,t]
  f = map(S,R,{z^2,t^2})
  M = S^1/ideal(z^3,t^3)
  g = map(M,M,matrix{{z*t}})
  p = pushFwd(g,f)
  kerg = pushFwd(ker g,f)
  kerp = prune ker p
  ///
  }
--test 0
TEST ///
kk=ZZ/32003
R4=kk[a..d]
R5=kk[a..e]
R6=kk[a..f]
M=coker genericMatrix(R6,a,2,3)
pdim M

G=map(R6,R5,{a+b+c+d+e+f,b,c,d,e})
F=map(R5,R4,random(R5^1,R5^{4:-1}))

P=pushFwd(M,G)
assert (pdim P==1)

Q=pushFwd(P,F)
assert (pdim (prune Q)==0)
///

-- test 1
TEST ///
P3=QQ[a..d]
M=comodule monomialCurveIdeal(P3,{1,2,3})

P2=QQ[a,b,c]
F=map(P3,P2,random(P3^1,P3^{-1,-1,-1}))
N=pushFwd(M,F)

assert(hilbertPolynomial M==hilbertPolynomial N)
///

-- test 2
TEST ///
kk = QQ
R = kk[x,y]/(x^2-y^3-y^5)
R' = integralClosure R
pr = pushFwd map(R',R)
q = pr_0 / (pr_0)_0
use R
assert(ann q==ideal(x,y))
///

-- test 3
TEST ///
kkk=ZZ/23
kk=frac(kkk[u])
T=kk[t]
x=symbol x
PR=kk[x_0,x_1]
R=PR/kernel map(T,PR,{t^3-1,t^4-t})
PS=kk[x_0,x_1,x_2]
S=PS/kernel map(T,PS,{t^3-1,t^4-t,t^5-t^2})

rs=map(S,R,{x_0,x_1})
st=map(T,S,{t^3-1,t^4-t,t^5-t^2})

pst=pushFwd st

MT=pst_0
k=numgens MT

un=transpose matrix{{1_S,(k-1):0}}
MT2=MT**MT

mtt2=map(MT2,MT,un**id_MT-id_MT**un)
MMS=kernel mtt2

r1=trim minimalPresentation kernel pushFwd(mtt2,rs)
r2=trim minimalPresentation pushFwd(MMS,rs)
r3=trim (pushFwd rs)_0

assert(r1==r2)
assert(r2==r3)
///

-- test 4
TEST ///
kk=ZZ/3
T=frac(kk[t])
A=T[x,y]/(x^2-t*y)

R=A[p]/(p^3-t^2*x^2)
S=A[q]/(t^3*(q-1)^6-t^2*x^2)
f=map(S,R,{t*(q-1)^2})
pushFwd f

p=symbol p
R=A[p_1,p_2]/(p_1^3-t*p_2^2)
S=A[q]
f=map(S,R,{t*q^2,t*q^3})
pushFwd f

i=ideal(q^2-t*x,q*x*y-t)
p=pushFwd(i/i^3,f)
assert(numgens p==2)
///

-- test 5
TEST ///
kk=QQ
A=kk[x]
B=kk[y]/(y^2)
f=map(B,A,{y})
pushFwd f
use B
d=map(B^1,B^1,matrix{{y^2}})
assert(pushFwd(d,f)==0)
///

-- test 6
TEST ///
kk=QQ
A=kk[t]
B=kk[x,y]/(x*y)
use B
i=ideal(x)
f=map(B,A,{x})
assert(isFreeModule pushFwd(module i,f))
///

-- test 7
TEST ///
kk=ZZ/101
n=3

PA=kk[x_1..x_(2*n)]
iA=ideal
iA=ideal apply(toList(1..n),i->(x_(2*i-1)^i-x_(2*i)^(i+1)))
A=PA/iA

PB=kk[y_1..y_(2*n-1)]
l=apply(toList(1..(2*n-1)),i->(x_i+x_(i+1)))
g=map(A,PB,l)
iB=kernel g;
B=PB/iB

f=map(A,B,l)

h1=pushFwd g;
ph1=cokernel promote(relations h1_0,B);
h2=pushFwd f;
assert(ph1==h2_0)
///

--test 8
TEST///
R = ZZ
S = ZZ[x]/(x^3)
f = map(S,R)
fun = (pushFwd f)#2
assert(fun x^5 == 0)
assert(flatten entries fun ((1+x^2)*(2-x)) === flatten {2,-1,2})
///

--test 9
TEST ///
kk = ZZ/5
R = kk[u,t]
S = kk[u,x,y]/ideal(x^2-y^3)
f = map(R,S,{R_0,t^3,t^2})

M = R^1/ideal(vars R)

rr = (res M).dd
fd1 = pushFwd(rr_1,f)
fd2 = pushFwd(rr_2,f)

assert(fd1*fd2 == 0)
///

--test 10
TEST ///
kk = ZZ/101
R = kk[x]
S = kk[x,y]/ideal(x^2-y^3)
f = map(S,R,{S_0})

M = S^2

d1 = map(M,M,matrix{{x,y},{x,-y}})
d2 = map(M,M,matrix{{x,x},{y^2,-y^2}})

fd1 = pushFwd(d1,f)
fd2 = pushFwd(d2,f)

assert(fd1*fd2 == 2*(R_0)^2)
assert(fd2*fd1 == 2*(R_0)^2)
///

--test 11
TEST ///
p = 2
kk = ZZ/p
R = kk[x,y,z]
f = map(R,R,apply(gens R,i->i^p))

M = R^1/ideal vars R
rr = (res M).dd

cc = chainComplex apply(4,i->pushFwd(rr_i,f))
hd = homology cc
assert (length prune hd_1 == 1)
assert (prune hd_2 == 0)
assert (prune hd_3 == 0)

newhd = homology pushFwd(res M,f)
assert (prune newhd_2 == 0)
assert (prune newhd_3 == 0)
///

--test 12
TEST ///
R = QQ[x,y,z]
I = ideal(x^3-1,y^2-2,z^2-3)
M = R^1/I
S = QQ
f = map(R,S)
assert( pushFwd(M,f) === QQ^12)
g = map(M,M,matrix{{x+y+z}})
assert( det pushFwd(g,f) === -968_QQ)
///

--test 13
TEST ///
R = QQ[x,y,z,Degrees => {{1,1},{1,0},{0,1}}]
I = ideal(x^3-1,y^2-2,z^2-3)
N = R^1/I
S = QQ[t]
f = map(R,S,{x+y})
assert(numgens pushFwd(N,f) <= 2)
g = map(R,S,{x})
assert(numgens pushFwd(N,g) <= 4)
///

--test 14
TEST///
S = QQ[t,Degrees => {{2,3,4,1}}]
R = QQ[t,x,y,z, Degrees => {{1,2},{2,3},{3,4},{4,1}}]
I = ideal(x^3-t,y^2-2,z^2-3)
M = R^1/I
f = map(R,S)

pushFwd(M,f)

g = map(M,M,matrix{{x}})
mat = pushFwd(g,f)

assert(mat^3 - S_0 == 0)
///
end

restart
uninstallPackage"PushForward"
installPackage"PushForward"
check"PushForward"
viewHelp"PushForward"

restart
loadPackage"PushForward"

kk = ZZ/5
R = kk[u,t]
S = kk[u,x,y]/ideal(x^2-y^3)
f = map(R,S,{R_0,t^3,t^2})

M = R^1/ideal(vars R)

rr = (res M).dd
fd1 = pushFwd(rr_1,f)
fd2 = pushFwd(rr_2,f)

assert(fd1*fd2 == 0)
