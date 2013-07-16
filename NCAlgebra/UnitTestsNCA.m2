newPackage(
        "UnitTestsNCA",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "Short tests for basic correctness of NCAlgebra.m2",
        DebuggingMode => true
        )

--- check basic ring operations code
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f = y*z + z*y - x^2
g = x*z + z*x - y^2
h = z^2 - x*y - y*x
assert(f*g == z*y*z*x-z*y^3+z*y*x*z+y*z^2*x-y*z*y^2+y*z*x*z-x^2*z*x+x^2*y^2-x^3*z)
assert(f^2 == z*y*z*y+z*y^2*z-z*y*x^2+y*z^2*y+y*z*y*z-y*z*x^2-x^2*z*y-x^2*y*z+x^4)
assert(f-g == z*y-z*x+y*z+y^2-x*z-x^2)
assert(3*g == 3*z*x-3*y^2+3*x*z)
assert(f+g == z*y+z*x+y*z-y^2+x*z-x^2)
B = A/ncIdeal{f,g,h}
j = -y^3-x*y*z+y*x*z+x^3
k = x^2 + y^2 + z^2
j*k
k^3
assert(k^3 == y^6+3*y*x*y^4+3*y*x*y*x*y^2+y*x*y*x*y*x+3*x*y^5+3*x*y*x*y^3+x*y*x*y*x*y+9*x^2*y^4+9*x^2*y*x*y^2+3*x^2*y*x*y*x+9*x^3*y^3+3*x^3*y*x*y+9*x^4*y^2+3*x^4*y*x+3*x^5*y+x^6)
assert(j*k == -y^5+y*x*y^2*z-y*x*y^3+y*x*y*x*z-x*y^3*z-x*y^4-x*y*x*y*z-x^2*y^3+x^2*y*x*z-x^3*y*z+x^3*y^2+x^3*y*x+x^4*y+x^5)
assert(j-k == -y^3-y^2+y*x*z-y*x-x*y*z-x*y+x^3-x^2)
assert(j+k == -y^3+y^2+y*x*z+y*x-x*y*z+x*y+x^3+x^2)
assert(3*k == 3*y^2+3*y*x+3*x*y+3*x^2)
///

--- checking central elements (skylanin)
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
I = ncIdeal { y*z + z*y - x^2,x*z + z*x - y^2,z^2 - x*y - y*x}
B = A/I
g = -y^3-x*y*z+y*x*z+x^3
h = x^2 + y^2 + z^2
assert (isCentral h)
assert (isCentral g)
assert(centralElements(B,2) == ncMatrix {{x^2, y*x+x*y, y^2}})
assert(centralElements(B,3) == ncMatrix {{y^3-y*x*z+x*y*z-x^3}})
///

--- checking normal form code with non-field base
TEST ///
needsPackage "NCAlgebra"
R = QQ[a,b,c,d]/ideal{a*b+c*d}
A = R {x,y,z}
I = ncIdeal {a*x*y,b*z^2}
Igb = ncGroebnerBasis(I, InstallGB=>true)
assert(c*z^2 % Igb == c*z^2)
assert(b*z^2 % Igb == 0)
///

--- checking normal form bergman code
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f = y*z + z*y - x^2
g = x*z + z*x - y^2
h = z^2 - x*y - y*x
I = ncIdeal {f,g,h}
Igb = ncGroebnerBasis I
red = y*x*y*x*y*x*y*x*y*x*y*x*y*x*y*x*z+x*y*x*y*x*y*x*y*x*y*x*y*x*y*x*y*z+8*x^2*y*x*y*x*y*x*y*x*y*x*y*x*y^2*z+8*x^3*y*x*y*x*y*x*y*x*y*x*y^3*z+28*x^4*y*x*y*x*y*x*y*x*y^4*z+28*x^5*y*x*y*x*y*x*y^5*z+56*x^6*y*x*y*x*y^6*z+56*x^7*y*x*y^7*z+70*x^8*y^8*z
assert(normalFormBergman(z^17,Igb) == red)
///

--- checking basis of algebra (sklyanin)
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f = y*z + z*y - x^2
g = x*z + z*x - y^2
h = z^2 - x*y - y*x
I = ncIdeal {f,g,h}
B = A/I
basis1 = ncMatrix {{x^4, x^3*y, x^3*z, x^2*y*x, x^2*y^2, x^2*y*z, x*y*x*y, x*y*x*z, x*y^3, x*y^2*z, y*x*y*x, y*x*y^2, y*x*y*z, y^4, y^3*z}}
basis2 = basis(4,B)
assert(basis1 == basis2)
///

--- checking basis of algebra (quantum polynomial ring)
TEST ///
needsPackage "NCAlgebra"
B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w})
basis1 = ncMatrix {{x^3, x^2*y, x^2*z, x^2*w, x*y^2, x*y*z, x*y*w, x*z^2, x*z*w, x*w^2, y^3, y^2*z, y^2*w, y*z^2, y*z*w, y*w^2, z^3, z^2*w, z*w^2, w^3}}
basis2 = basis(3,B)
assert(basis1 == basis2)
///

--- checking ore extensions
TEST ///
needsPackage "NCAlgebra"
B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w})
sigma = ncMap(B,B,{y,z,w,x})
C = oreExtension(B,sigma,a)
sigmaC = ncMap(C,C,{y,z,w,x,a})
assert(normalElements(sigmaC,1) == ncMatrix {{a}})
assert(normalElements(sigmaC,2) == 0)
assert(normalElements(sigmaC @@ sigmaC,2) == ncMatrix {{a^2}})
assert(matrix normalAutomorphism a == ncMatrix {{y,z,w,x,a}})
assert(matrix normalAutomorphism a^2 == ncMatrix {{z,w,x,y,a}})
///

--- checking endomorphism ring code
TEST ///
needsPackage "NCAlgebra"
Q = QQ[a,b,c]
R = Q/ideal{a*b-c^2}
kRes = res(coker vars R, LengthLimit=>7);
M = coker kRes.dd_5
B = endomorphismRing(M,X);
gensI = gens ideal B;
gensIMin = minimizeRelations(gensI, Verbosity=>1);
checkHomRelations(gensIMin,B.cache.endomorphismRingGens)
///

--- Another example testing out endomorphism code
TEST ///
needsPackage "NCAlgebra"
Q = QQ[a,b,c,d]
R = Q/ideal{a*b+c*d}
kRes = res(coker vars R, LengthLimit=>7);
M = coker kRes.dd_5
time B = endomorphismRing(M,X);
gensI = gens ideal B;
time gensIMin = minimizeRelations(gensI, Verbosity=>1);
checkHomRelations(gensIMin,B.cache.endomorphismRingGens);
///

--- Test creation of matrices, as matrices of matrices
TEST ///
needsPackage "NCAlgebra"
A = QQ{a,b,c,d}
M = ncMatrix {{a,b,c,d}}
N = ncMatrix {{M,2*M,3*M},{4*M,5*M,6*M}}
assert (N == ncMatrix {{a, b, c, d, 2*a, 2*b, 2*c, 2*d, 3*a, 3*b, 3*c, 3*d}, {4*a, 4*b, 4*c, 4*d, 5*a, 5*b, 5*c, 5*d, 6*a, 6*b, 6*c, 6*d}})
///

--- Test NCMatrix % NCGroebnerBasis
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f = y*z + z*y - x^2
g = x*z + z*x - y^2
h = z^2 - x*y - y*x
I = ncIdeal {f,g,h}
Igb = ncGroebnerBasis I
M = ncMatrix {{x, y, z}}
sigma = ncMap(A,A,{y,z,x})
N = ncMatrix {{M},{sigma M}, {sigma sigma M}}
Nred = N^3 % Igb
B = A/I
phi = ncMap(B,A,gens B)
NB = phi N
N3B = NB^3
answer = ncMatrix {{-y^2*z+y^3+y*x*z-y*x*y+x*y*z+x*y^2+2*x*y*x+x^2*z+3*x^2*y, y^2*z+y*x*z+2*y*x*y+x*y*z+3*x*y^2-x*y*x-x^2*z+x^2*y+x^3, 2*y^2*z+y^3+y*x*y+x*y*x+2*x^2*z+x^3}, {y^2*z+y*x*z+2*y*x*y+x*y*z+3*x*y^2-x*y*x-x^2*z+x^2*y+x^3, 2*y^2*z+y^3+y*x*y+x*y*x+2*x^2*z+x^3, -y^2*z+y^3+y*x*z-y*x*y+x*y*z+x*y^2+2*x*y*x+x^2*z+3*x^2*y}, {2*y^2*z+y^3+y*x*y+x*y*x+2*x^2*z+x^3, -y^2*z+y^3+y*x*z-y*x*y+x*y*z+x*y^2+2*x*y*x+x^2*z+3*x^2*y, y^2*z+y*x*z+2*y*x*y+x*y*z+3*x*y^2-x*y*x-x^2*z+x^2*y+x^3}}
assert(N3B == phi Nred)
assert(N3B == answer)
///

--- checking matrix multiplication, addition, etc
--- operations to test: +,-,^,|,||,*.  In this,
--- also check that source/target are correct.
TEST ///
///

--- Check mingens of a NCMatrix
TEST ///
///

--- Check rightKernel (ordinary)
TEST ///
///

--- Check rightKernelBergman
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
g = -y^3-x*y*z+y*x*z+x^3
I = ncIdeal {f1,f2,f3,g}
B = A/I
M3 = ncMatrix {{x,y,z,0},
               {-y*z-2*x^2,-y*x,z*x-x*z,x},
               {x*y-2*y*x,x*z,-x^2,y},
               {-y^2-z*x,x^2,-x*y,z}}
assignDegrees(M3,{1,0,0,0},{2,2,2,1})
assert isHomogeneous M3
ker1M3 = rightKernelBergman(M3)
assert isHomogeneous ker1M3
assert(M3*ker1M3 == 0)
ker2M3 = rightKernelBergman(ker1M3)
assert isHomogeneous ker2M3
assert(ker1M3*ker2M3 == 0)
ker3M3 = rightKernelBergman(ker2M3)
assert isHomogeneous ker3M3  
assert(ker2M3*ker3M3 == 0)
///

--- Check NCIdeal operations
TEST ///
///

--- Check basis of ideal code
TEST ///
///

--- Check NCRightIdeal operations
TEST ///
///

--- Check NCLeftIdeal operations
TEST ///
///

--- Check NCGroebnerBasis code (Bergman)
TEST ///
///

--- Test gbFromOutputFile
TEST ///
///

TEST ///
--- Test factoring code with skew polynomial ring
needsPackage "NCAlgebra"
-- n is the number of variables in skew poly ring
n = 3
rk = 2^(n-1)
B = skewPolynomialRing(QQ,-1_QQ,{x_1..x_n})
A = ambient B
-- tau is cyclic ring automorphism
tau = ncMap(B,B,drop(gens B,1) | {(gens B)#0})
-- create an Ore extension with a new variable w and tau
C = oreExtension(B,tau,w)
A' = ambient C
use A'
J = ideal C
J = J + ncIdeal {w^2}
D = A'/J
DtoC = ncMap(C,D,gens C)
-- need inverse maps, since \varphi^\sigma is obtained by applying \sigma^{-1}
-- to all the matrix entries
tauCInv = ncMap(C,C,{(gens C)#(n-1)} | drop(drop(gens C,-1),-1) | {DtoC w})
-- have to compose twice, because the normalizing automorphism of w^2 is tau^2
sigmaInv = tauCInv @@ tauCInv
-- build the presentation of the example module
M1 = ncMatrix {drop(gens D,-2) | {w}}
assignDegrees M1
hiSyz = M1
-- take a sufficiently high syzygy over D to make sure we have a MCM module
-- Note that since the algebra is Koszul, we may use the rightKernel code
-- that does not make a call to Bergman.
scan(n, i -> (<< "Computing " << i+2 << "th syzygy" << endl; hiSyz = rightKernel(hiSyz,1)));
-- lift the map to the ambient ring
hiSyzC = DtoC hiSyz
assignDegrees hiSyzC;
assert(isHomogeneous hiSyzC)
use C
-- build f*id map
-- (this needs to be easier to make)
fId = w^2*(ncMatrix applyTable(entries id_(ZZ^rk), i -> promote(i,C)));
assignDegrees fId;
assert(isHomogeneous fId)
-- now factor through w^2*identity
hiSyzC' = fId // hiSyzC
--- check that these satisfy the twisted matrix factorization condition
assert(hiSyzC*hiSyzC' == fId)
assert(hiSyzC'*(sigmaInv hiSyzC) == fId)
///

--- Factoring map code over Sklyanin
TEST ///
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3}
-- note that this is not a 'generic' sklyanin, and has a finite GB
Igb = ncGroebnerBasis I
g = 2*(-y^3-x*y*z+y*x*z+x^3)
J = I + ncIdeal {g}
B = A/I
B' = A/J
BprimeToB = ncMap(B,B',gens B)
k = ncMatrix {{x,y,z}}
assignDegrees k
M = BprimeToB rightKernelBergman rightKernelBergman k
fId = g*(ncMatrix applyTable(entries id_(ZZ^4), i -> promote(i,B)));
assignDegrees(fId,{2,2,2,3},{5,5,5,6});
assert(isHomogeneous fId)
-- now factor through g*id
M' = fId // M
assert(M*M' == fId)
assert(M'*M == fId)
///

--- Check NCGroebnerBasis code (InstallGB)
TEST ///
///

--- Check hilbert series code
TEST ///
///

--- Check left and right multiplication map
TEST ///
///

--- checking normal elements code
TEST ///
///

--- Check NCRingMap code
TEST ///
///

--- Make sure ring variables don't leak out when several rings are created
--- Also test 'use' code
TEST ///
///

--- Test coefficients
TEST ///
///

--- Test NCMatrix // NCMatrix
TEST ///
///

--- Include some matrix factorization tests
TEST ///
///

--- Check variables with non-standard weights
TEST ///
///

--- Check various NCRingElement commands
--- leadTerm, leadMonomial, size, etc
TEST ///
///

--- Skew polynomial ring, abelianization, and isCommutative
TEST ///
needsPackage "NCAlgebra"
R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
B = skewPolynomialRing(R,q,{x,y,z,w})
assert(x*y == q*y*x)
C = skewPolynomialRing(QQ,1_QQ, {x,y,z,w})
assert(isCommutative C)
assert(not isCommutative B)
abC = abelianization C
abC' = abelianization ambient C
assert(ideal abC == 0)
assert(ideal abC' == 0)
Bop = oppositeRing B
assert(y*x == q*x*y)
///

end

--- matrix factorizations over sklyanin algebra
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3}
Igb = ncGroebnerBasis I
z*x^3 % Igb
g = -y^3-x*y*z+y*x*z+x^3
J = I + ncIdeal {g}
g % Igb
normalFormBergman(g,Igb)
B = A/I
use A
B' = A/J
use B
leftMultiplicationMap(x,3)
leftMultiplicationMap(z,3)
centralElements(B,3)
basis(3,B)
g = -y^3-x*y*z+y*x*z+x^3
---- broken?
isLeftRegular(g,6)
M=ncMatrix{{z,-x,-y},{-y,z,-x},{x,y,z}}
rightKernel(M,1)
--- again, waaay too many calls to bergman!
rightKernel(basis(1,B),10)
--- skip the next line if you want to work in the tensor algebra
h = x^2 + y^2 + z^2
isCentral h
isCentral g
M3 = ncMatrix {{x,y,z,0},
               {-y*z-2*x^2,-y*x,z*x-x*z,x},
               {x*y-2*y*x,x*z,-x^2,y},
               {-y^2-z*x,x^2,-x*y,z}}
M2 = ncMatrix {{-z*y,-x,z,y},
               {z*x-x*z,z,-y,x},
               {x*y,y,x,-z},
               {2*x*y*z-4*x^3,-2*x^2,2*y^2,2*x*y-2*y*x}}
M3*M2
M2*M3
--- checking homogeneity
assignDegrees M3
isHomogeneous 3M
assignDegrees(M3,{1,0,0,0},{2,2,2,1})
isHomogeneous M3
---
M3' = M3^2
--- can now work in quotient ring!
M3*M4
M4*M3
M3*(x*y) - (x*y)*M3
M1 = ncMatrix {{x}}
M2 = ncMatrix {{y}}
M1*M2
--- apparently it is very important to reduce your entries along the way.
wallTiming (() -> M3^6)
--- still much slower!  It seems that reducing all along the way is much more efficient.
wallTiming (() -> M3'^5)

--- or can work over free algebra and reduce later
M4*M3 % ncgb
M3*M4 % ncgb
M3' = M3 % ncgb'
M4' = M4 % ncgb'
M3'*M4' % ncgb
M4'*M3' % ncgb

M3+M4
2*M3
(g*M3 - M3*g) % ncgb
M3^4 % ncgb
wallTiming (() -> M3^4 % Igb)
---------------------------------------------

---- working in quantum polynomial ring -----
restart
needsPackage "NCAlgebra"
R = toField(QQ[q]/ideal{q^4+q^3+q^2+q+1})
A = R{x,y,z}
--- this is a gb of the poly ring skewed by a fifth root of unity.
I = ncIdeal {y*x - q*x*y, z*y - q*y*z, z*x - q*x*z}
ncgb = ncGroebnerBasis(I,InstallGB=>true)
B = A / I
-- get a basis of the degree n piece of A over the base ring
time bas = basis(10,B);
coefficients(x*y+q^2*x*z)
bas2 = flatten entries basis(2,B)
coeffs = coefficients(x*y+q^2*x*z, Monomials => bas2)
first flatten entries ((ncMatrix{bas2})*coeffs)
-- yay!
matrix {{coeffs, coeffs},{coeffs,coeffs}}
basis(2,B)
basis(3,B)
leftMultiplicationMap(x,2)
rightMultiplicationMap(x,2)
centralElements(B,4)
centralElements(B,5)
--- we can verify that f is central in this ring, for example
f = x^5 + y^5 + z^5
g = x^4 + y^4 + z^4
isCentral f
isCentral g
-- example computation
-- takes waaay too long!  Need to try and speed up reduction code.
time h = f^2
time h = f^3
time h = f^4
------------------------------------------------------

--- testing out Bergman interface
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3}
Igb = twoSidedNCGroebnerBasisBergman I
wallTiming(() -> normalFormBergman(z^17,Igb))
time remainderFunction(z^17,Igb)
B = A / I
g = -y^3-x*y*z+y*x*z+x^3
isCentral g
hilbertBergman B

-----------
-- this doesn't work since it is not homogeneous unless you use degree q = 0, which is not allowed.
restart
needsPackage "NCAlgebra"
A = QQ{q,x,y,z}
I = ncIdeal {q^4+q^3+q^2+q+1,q*x-x*q,q*y-y*q,q*z-z*q,y*x-q*x*y,z*y-q*y*z,z*x-q*x*z}
Igb = twoSidedNCGroebnerBasisBergman I

---- ore extensions
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,z,w}}
M2 = rightKernel(M1,1)
M3 = rightKernel(M2,1)
M4 = rightKernel(M3,1)
M5 = rightKernel(M4,1)
M6 = rightKernel(M5,1)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M4A
M6A

---- ore extensions
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,z,w}}
M2 = rightKernel(M1,1)
M3 = rightKernel(M2,1)
M4 = rightKernel(M3,1)
M5 = rightKernel(M4,1)
M6 = rightKernel(M5,1)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M4A
M6A

---- ore extension of skew ring
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
assignDegrees M1
-- another bug!
rightKernelBergman M1
M2 = rightKernel(M1,1)
M3 = rightKernel(M2,1)
M4 = rightKernel(M3,1)
M5 = rightKernel(M4,1)
M6 = rightKernel(M5,1)
M7 = rightKernel(M6,1)
M8 = rightKernel(M7,1)
M9 = rightKernel(M8,1)
M10 = rightKernel(M9,1)
M3A = promote(M3,A)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M7A = promote(M7,A)
M8A = promote(M8,A)
M9A = promote(M9,A)
M10A = promote(M10,A)

--- make sure ores with subscripts work
restart
needsPackage "NCAlgebra"
n=4
A = QQ {x_1..x_n}
gensA = gens A;
I = ncIdeal apply(subsets(toList(0..(n-1)),2), p -> gensA#(p#0)*gensA#(p#1)+gensA#(p#1)*gensA#(p#0))
B = A/I
sigma = ncMap(B,B,drop(gens B,1) | {(gens B)#0})
matrix sigma
C = oreExtension(B,sigma,w)

---- ore extension of skew ring
restart
debug needsPackage "NCAlgebra"
n = 6
rk = 2^(n-1)
A = QQ {x_1..x_n}
gensA = gens A;
I = ncIdeal apply(subsets(toList(0..(n-1)),2), p -> gensA#(p#0)*gensA#(p#1)+gensA#(p#1)*gensA#(p#0))
B = A/I
sigma = ncMap(B,B,drop(gens B,1) | {(gens B)#0})
matrix sigma
C = oreExtension(B,sigma,w)
A' = ambient C
use A'
J = ideal C
J = J + ncIdeal {w^2}
D = A'/J
DtoC = ncMap(C,D,gens C)
sigmaCInv = ncMap(C,C,{(gens C)#(n-1)} | drop(drop(gens C,-1),-1) | {DtoC w})
M1 = ncMatrix {drop(gens D,-2) | {w}}
assignDegrees M1
hiSyz = M1
scan(n, i -> (<< "Computing " << i+2 << "th syzygy" << endl; hiSyz = rightKernel(hiSyz,1)));
hiSyzC = DtoC hiSyz
assignDegrees hiSyzC;
isHomogeneous hiSyzC
----

--- try factoring code
use C
fId = w^2*(ncMatrix applyTable(entries id_(ZZ^rk), i -> promote(i,C)));
assignDegrees fId;
isHomogeneous fId
hiSyzC' = fId // hiSyzC
hiSyzC*hiSyzC'
hiSyzC'*(sigmaCInv sigmaCInv hiSyzC)
----
M5 = rightKernel(M4,1)
M5C = DtoC M5
M4C*M5C   -- huzzah!

---- ore extension of sklyanin
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
M2 = rightKernel(M1,1)
M2 = rightKernel(M1,2)
M2 = rightKernel(M1,3)
M2 = rightKernel(M1,4)
M3 = rightKernel(M2,1)
M4 = rightKernel(M3,1)
M5 = rightKernel(M4,1)
M6 = rightKernel(M5,1)
M7 = rightKernel(M6,1)
M8 = rightKernel(M7,1)
M9 = rightKernel(M8,1)
M10 = rightKernel(M9,1)
M3A = promote(M3,A)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M7A = promote(M7,A)
M8A = promote(M8,A)
M9A = promote(M9,A)
M10A = promote(M10,A)

---- ore extension of skew ring with infinite automorphism
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*(y+z),y*w-w*(z+x),z*w-w*(x+y),w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
M2 = rightKernel(M1,1)
M3 = rightKernel(M2,1)
M4 = rightKernel(M3,1)
M5 = rightKernel(M4,1)
M6 = rightKernel(M5,1)
M7 = rightKernel(M6,1)
M8 = rightKernel(M7,1)
M9 = rightKernel(M8,1)
M10 = rightKernel(M9,1)
M11 = rightKernel(M10,1)
M12 = rightKernel(M11,1)
M13 = rightKernel(M12,1)
M14 = rightKernel(M13,1)
M15 = rightKernel(M14,1)

assignDegrees M1
M2 = rightKernelBergman M1
M3 = rightKernelBergman M2
M4 = rightKernelBergman M3


--- test for speed of reduction code
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-2*w*y,y*w-2*w*z,z*w-2*w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
time M2 = rightKernel(M1,7,Verbosity=>1);
time M3 = rightKernel(M2,3,Verbosity=>1);

---- andy's example
restart
debug needsPackage "NCAlgebra"
A=QQ{a, b, c, d, e, f, g, h}
-- this got very slow all of a sudden!
I = gbFromOutputFile(A,"UghABCgb6.txt", ReturnIdeal=>true);
Igb = ncGroebnerBasis I;
B=A/I;

M2=ncMatrix{{-b,-f,-c,0,0,0,-g,0,0,0,0,-h,0,0,0,0},
    {a,0,c-f,0,0,0,0,d-g,0,0,0,e,e-h,0,0,0},
    {0,0,a-b,-f,-d,0,0,0,d-g,0,0,0,0,e-h,0,0},
    {0,0,0,0,c-f,0,0,-b,-c,-g,0,0,0,0,-h,0},
    {0,0,0,0,0,-f,0,0,0,0,-g,-b,-b,-c,0,-h},
    {0,a,b,c,d,e,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,a,b,c,d,e,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,a,b,c,d,e}};
M=basis(1,B);

bas=basis(2,B)
use A
f = a^7+b^7+c^7+d^7+e^7+f^7+g^7+h^7
f = promote(f,B);
--- sometimes bergman calls are great!
time X = flatten entries (f*bas);
netList X

-------------------------------
-- Testing NCRingMap code
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z}
I = ncIdeal {x*y-y*x,x*z-z*x,y*z-z*y}
B = A/I
sigma = ncMap(B,B,{y,z,x})
delta = ncMap(B,B,apply(gens B, x -> promote(1,B)))
isWellDefined sigma
oreExtension(B,sigma,w)
-- doesn't really matter that we can handle derivations yet, since bergman doesn't do inhomogeneous
-- gbs very well.
oreIdeal(B,sigma,delta,w)
oreExtension(B,sigma,delta,w)
-------------------------------
--- Testing multiple rings code
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y}
C = QQ{x,y,z}
B = A/I

-----------------------------------
--- Testing out normal element code
restart
debug needsPackage "NCAlgebra"
A = QQ{a,b,c}
I = ncIdeal {a*b+b*a,a*c+c*a,b*c+c*b}
B = A/I
sigma = ncMap(B,B,{b,c,a})
sigma_2   -- testing restriction of NCMap to degree code
isWellDefined sigma
C = oreExtension(B,sigma,w)
normalElements(C,1,x,y)
tau = ncMap(C,C,{b,c,a,w})
normalElements(tau,3)
normalElements(tau,1)
normalElements(tau @@ tau,1)
normalElements(tau @@ tau,2)
normalElements(tau @@ tau,3)
normalElements(tau @@ tau,4)
findNormalComplement(w,x)
isNormal w
phi = normalAutomorphism w
matrix phi
phi2 = normalAutomorphism w^2
matrix phi2

-- another normal element test
restart
debug needsPackage "NCAlgebra"
A = QQ{a,b,c}
I = ncIdeal {a*b+b*a,a*c+c*a,b*c+c*b}
B = A/I
normalElements(B,1,x,y)

-- another test
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z}
I = ncIdeal {y*z + z*y - x^2,x*z + z*x - y^2,z^2 - x*y - y*x}
B = A/I
basis(2,B)
normalElements(B,2,a,b)
f = x^2+2*x*y+2*y*x+3*y^2
isNormal f
isCentral f
findNormalComplement(f,x)
findNormalComplement(f,y)
findNormalComplement(f,z)

--- one more test...
restart
debug needsPackage "NCAlgebra"
A = (QQ[a_0..a_5]) {x,y,z};
gensI = {y^2*x-x*y^2, y*x^2-x^2*y, z*x-y^2+x*z, z*y+y*z-x^2, z^2-y*x-x*y}
I = ncIdeal gensI
Igb = ncGroebnerBasis(I, InstallGB=>true)
B = A/I
f = a_0*x^2 + a_1*x*y + a_1*y*x + a_4*y^2
centralElements(B,3)
normalElements(B,3,b,c)
basis(3,B)

------------------------------------
--- Testing out endomorphism code
restart
debug needsPackage "NCAlgebra"
Q = QQ[a,b,c]
R = Q/ideal{a*b-c^2}
kRes = res(coker vars R, LengthLimit=>7);
M = coker kRes.dd_5
B = endomorphismRing(M,X);
gensI = gens ideal B;
gensIMin = minimizeRelations(gensI, Verbosity=>1)
checkHomRelations(gensIMin,B.cache.endomorphismRingGens);
------------------------------------
--- Testing out endomorphism code
restart
debug needsPackage "NCAlgebra"
Q = QQ[a,b,c,d]
R = Q/ideal{a*b+c*d}
kRes = res(coker vars R, LengthLimit=>7);
M = coker kRes.dd_5
time B = endomorphismRing(M,X);
gensI = gens ideal B;
time gensIMin = minimizeRelations(gensI, Verbosity=>1);   -- new bug here!!!
checkHomRelations(gensIMin,B.cache.endomorphismRingGens);
--------------------------------------
--- Skew group ring example?
restart
debug needsPackage "NCAlgebra"
S = QQ[x,y,z]
Q = QQ[w_1..w_6,Degrees=>{2,2,2,2,2,2}]
phi = map(S,Q,matrix{{x^2,x*y,x*z,y^2,y*z,z^2}})
I = ker phi
R = Q/I
phi = map(S,R,matrix{{x^2,x*y,x*z,y^2,y*z,z^2}})
M = pushForward(phi,S^1)
B = endomorphismRing(M,X)
gensI = gens ideal B;
gensIMin = minimizeRelations(gensI, Verbosity=>1)
checkHomRelations(gensIMin,B.cache.endomorphismRingGens);

first gensI
first newGensI

netList B.cache.endomorphismRingGens
f = sum take(flatten entries basis(1,B),10)
f^2
HomM = Hom(M,M)
map1 = homomorphism(HomM_{0})
map2 = homomorphism(HomM_{1})
gensHomM = gens HomM
elt = transpose flatten matrix (map2*map1)
gensHomM // elt

restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z}
mon = first first pairs (x*y*z).terms
substrings(mon,3)

QQ toList vars(0..14)
QQ{x_1,x_2}
QQ{a..d}

restart
debug needsPackage "NCAlgebra"
R = ZZ/101[a,b,c,d]/ideal{b^5,c^5}
cSubstrings(first exponents (a*b^2*c^3*d^4),0,4)
cSubstrings(first exponents (a*b^2*c^3*d^4),0,0)


-------------------------------------
--- Testing lead terms
restart
debug needsPackage "NCAlgebra"
A = QQ{a,b,c,d}
leadTerm(d*b+d*a*c)

-- Andy test
restart
debug needsPackage "NCAlgebra"
A = QQ {a,b,c,d,e,f,g,h}
J = ncIdeal  {b*a-a*b, f*a-a*f, f*b-c*b+c*a-b*f+b*c-a*c, f*c-c*f, f*d-d*f+d*c-c*d,
     f*e-e*f, g*a-a*g, g*b-d*b-b*g+b*d, g*c-d*c-c*g+c*d, g*d-d*g, g*e-e*g, h*a-e*b+b*e-a*h,
     h*b-e*b-b*h+b*e, h*c-e*c-c*h+c*e, h*d-d*h, h*e-e*h}
Jgb = ncGroebnerBasis(J,InstallGB=>true)
time basis(5,J)
time basis(6,J)

--- nonmonomial rels ker test -- not a good MF example, but a good kernel bug.
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*(y+z),y*w-w*(z+x),z*w-w*(x+y),w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
assignDegrees M1
M2 = rightKernelBergman M1
M3 = rightKernelBergman M2
M4 = rightKernelBergman M3
rightKernelBergman (M2_{0,1,2,3,5,7})
M2_{0,1,2,3,5,7}
rightMingens M2
isHomogeneous M2
---

--- matrix factoring test
M2a = M2_{0,1,2,3}
isHomogeneous M2a
M2b = M2_{4}
isHomogeneous M2b
M2b = M2_{2}*x + M2_{1}*y
isHomogeneous M2b
liftb = M2b // M2a
M2b - M2a*liftb
errTerm = transpose ncMatrix {{x^2,0,0}}
assignDegrees(errTerm,{1,1,1},{3})
M2c = M2_{2}*x + M2_{1}*y - errTerm
isHomogeneous M2c
liftc = M2c // M2a
M2c - M2a*liftc
M2d = M2_{4,5,6,7,8,9,10,11,12,13}
liftd = M2d // M2a
M2d - M2a*liftd

--- submatrices
M2' = M2_{0,1,2,3,4}
M2' = M2_{0,1,2,3,5}
M2' = M2_{0,1,2,3,6}
M2' = M2_{0,1,2,3,7}
M2' = M2_{0,1,2,3,8}
assignDegrees(M2', {0,0,0},{1,1,1,1,2})
isHomogeneous M2'
M3' = rightKernelBergman M2'  --- bug!?!
M4 = rightKernelBergman M3'

-- debugging
g = newGBGens#3
minKerGens2 = minKerGens | {g}
nonminKerGens = flatten apply(take(gens ring first minKerGens2,4), v -> minKerGens2 * v)
tempGb =  twoSidedNCGroebnerBasisBergman(gbIdealB | nonminKerGens | {g},
                                         "NumModuleVars" => numgens C - numgens B,
                                         DegreeLimit => opts#DegreeLimit,
                                         ClearDenominators=>true,
                                         CacheBergmanGB=>false);
apply(newGBGens, f -> f % tempGb)

--- skew poly ring
restart
debug needsPackage "NCAlgebra"
R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
B = skewPolynomialRing(R,q,{x,y,z,w})
C = skewPolynomialRing(QQ,1_QQ, {x,y,z,w})
isCommutative C
abC = abelianization C
abC' = abelianization ambient C

--- opposite ring
restart
debug needsPackage "NCAlgebra"
R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
B = skewPolynomialRing(R,q,{x,y,z,w})
oppositeRing B

--- check NCAlgebra
restart
check "UnitTestsNCA"
