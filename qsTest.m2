-- This is a file of examples to test the code in the
-- QuillenSuslin package.

-- Would like to make nontrivial examples of unimodular rows/matrices
-- in order to test the methods in the package.

-- Is a non-trivial example:
-- Warning: It takes a very long time to do this.
-- it works much better over ZZ/101
restart
load "QuillenSuslin.m2"
R = ZZ/101[x,y,z]
f = matrix{{x*y+x*z+y*z-1, x^2+y^2, y^2+z^2, z^2}}
P = ker f
g = map(R^4,R^6,gens P)
mp = minimalPresentation P
phi = mp.cache.pruningMap
isIsomorphism phi
phi^-1
B = computeFreeBasis mp
phi
source phi
target phi
psi = map(mp,R^5,1)
map(g*phi*(psi*B)


peek C
peek C.cache
peek P
peek P.cache
class C
class P
ambient C
ambient P
P.?generators
C.?generators

phi = map(P,C,1)
isIsomorphism phi
inverse phi
phi2 = map(C,P,1)
isIsomorphism phi2




(image B)/(image map(R^6,R^7,presentation P)) == C
B2 = g*B
image B2 == image map(R^4,R^6,gens P) -- Wow it works.
f*(B2_{2})
P
gens P

f


syz B
rank P
B2 = p
phi(B_{0})


-- Change computeFreeBasis to take last columns of qsAlgorithm?
f = matrix{{x*y+x*z+y*z-1, x^2+y^2, y^2+z^2, z^2}}
isUnimodular f
U = completeMatrix(f,Verbose => 3)


time isProjective P
rank P
time mingens P
time F = computeFreeBasis( P, Verbose => 3 )

restart;
load "QuillenSuslin.m2"
R = QQ[x,y,z]
f1 = sum(2, i -> random(i,R)); f2 = sum(2, i -> random(i,R)); f3 = sum(2, i -> random(i,R));
while not isUnimodular matrix{{f1,f2,f3}} do (
f1 = sum(2, i -> random(i,R));
f2 = sum(2, i -> random(i,R));
f3 = sum(2, i -> random(i,R));
);
f = matrix{{f1,f2,f3}}
isUnimodular f


-- A row over ZZ[x,y] that doesn't use any shortcuts.
-- Can use this as an example of the general algorithm.

restart;
load "QuillenSuslin.m2"
R = ZZ[x,y]
f = matrix{{x^3,3*y+1,y^3+2*x*y^2}}
f = matrix{{x^2,2*y+1,y+x^5*y^2}} -- Seems like a good example.
P = ker f
syz mingens P

isUnimodular f
U = qsAlgorithm(f,Verbose => 2)
inverse U

-- ==================
-- Example for paper?
-- ==================
restart;
load "QuillenSuslin.m2"
R = ZZ[x,y]
f = matrix{{x^2,2*y+1,y+x^5*y^2}}
isUnimodular f
(U1,subs,invSubs) = changeVar(f,{x,y})
f = sub(f*U1,subs)
m1 = getMaxIdeal(ideal(0_R),{x})
L1 = horrocks(f,y,m1)
m2 = getMaxIdeal(sub(ideal(2*x+1),R),{x})
L2 = horrocks(f,y,m2)
sub(ideal(2*x+1,x),R) == ideal(1_R)
L = {L1,L2}
U2 = patch(L,y)
f = f*U2

U = qsAlgorithm f
det U
f*U
A = completeMatrix f
det A
K = ker f
isProjective K
mingens K
B = computeFreeBasis K
syz B
image B == K



R = ZZ[x,y]
f = matrix{{2*x+3,x^2+x*y,y^3}}
isUnimodular f
P = ker f
isProjective P
N = coker transpose presentation P
Ext^1(N,R)
Ext^2(N,R)
Ext^3(N,R) == 0

-- Step-by-step algorithm with this example.

(U1,subs,invSubs) = changeVar(f,{x,y})
f = sub(f*U1,subs)
m1 = getMaxIdeal(ideal(0_R),{x})
L1 = horrocks(f,y,m1)
m2 = getMaxIdeal(sub(ideal(6*x-1),R),{x})
L2 = horrocks(f,y,m2)
sub(ideal(10*x-1,x^3),R) == ideal(1_R)
L = {L1,L2}
U = patch(L,y)
f*U

-- We can stop the local loop and patch the local solutions together.

restart;
load "QuillenSuslin.m2"
R = ZZ[x,y,z,w]
f1 = random(0,R)+random(2,R); f2 = random(0,R) + random(1,R); f3 = random(0,R) + random(2,R);
while not isUnimodular matrix{{f1,f2,f3}} do (
f1 = random(1,R);
f2 = random(0,R)+random(2,R);
f3 = random(0,R)+random(1,R);
);
f = matrix{{f1,f2,f3}}
isUnimodular f
qsAlgorithm f



-- Examples of unimodular rows:
restart;
load "QuillenSuslin.m2"
R = QQ[x,y]
f = matrix{{5*x^2+8*x*y+8*y^2+8*x+6,7*x^2+4*y^2+8*x+6*y+3,7*x^2+4*y^2+8*x+6*y+1}}
isUnimodular f
U = qsAlgorithm f
U = qsAlgorithm(f,Verbose => 3)
f*U

-- Testing new methods for polynomials over fraction fields.
restart;
load("QuillenSuslin.m2")
R = QQ[x,y,z]
f = z^5+z^2
g = x*z^4+((2*x^2+2)/(1-x^2))*z^3+(x/y)*z^2+z-1
h = suslinLemma(f,g,z,ideal(x,y))
coeffVarFF(h#0,z)
matrix{{f,g}} * h#1
(matrix{{f,g}} * h#1)_(0,0) == h#0
coeffVarFF(f,z)
leadCoeffVarFF(f,z)
isLocalUnit(leadCoeffVarFF(f,z),ideal(x,y))
n = numerator f
degVar(f,z)
I = ideal(x,y)
isLocalUnit((2*x+1)/(x+2),I)


restart;
load "QuillenSuslin.m2";
debug QuillenSuslin
R = ZZ[x]
f1 = 2*x+1
f2 = 6*x+7
f3 = 2*x+5
f = matrix{{f1*f2,f1*f3,f2*f3}}

U = qsAlgorithm f
K = ker f
isProjective K
syz gens K
B = computeFreeBasis K
mingens K
image B == K
syz mingens K
syz B


(U,subs,invSubs) = changeVar(f,{x})
f*U
M = horrocks(f*U,x,ideal(2))
solList = getLocalSolutions(f*U,{},x)
#solList
f*U*(solList#0)
f*U*(solList#1)
solList#1
ideal(commonDenom(solList#0),commonDenom(solList#1)) == ideal(1_R)
M = patch(solList,x)
f*U*M
V = qsAlgorithmRow f
f*V
inverse V

restart;
load "QuillenSuslin.m2"
R = QQ[x,y,z]
I = ideal(x^2+1,y-2)
f = x^2*y*z^3+2*x*y^2*z^3
isAlmostMonic(f,{y,x,z})
isAlmostMonic(f,{x,y,z})


restart;
load("QuillenSuslin.m2")
R = QQ
f = sub(matrix{{2,3,4}},R)
isUnimodular(f)
-- ^--Try running all relevant algorithms with this example to try to
-- catch == R issue (versus == ideal(1_R)).
U = qsAlgorithmRow(f)
inverse U

R = ZZ[x,y]
f = 3*6*7*(x+1)^4*(x^2+2*x+2)
L = factorList f
ring L#0


restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
M = matrix{{x^2*y+1,x+y-2,2*x*y}} -- Define a surjective R-linear map from R^3 -> R.
P = ker(M) -- Let P be the stably-free kernel.
isProjective P
rank P -- Notice that P has rank 2.
syz gens P -- Notice that the first generator is a linear combination of the other two.
-- For more complicated examples, how do we find a free generating set?-- The main idea is the completion of unimodular rows.
B = 2*computeFreeBasis(P) -- Use a method from the QuillenSuslin package.
mingens image(B)
mingens P -- Macaulay 2 does not return a minimal generating set.
P == image(B) -- Check that B is a generating set for P.
syz B -- Check that B is a free generating set.


--Ex. No Heuristic (Step by step.)

restart;
load("QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{x^2,3*y+1,x+x^2*y+y^2}} -- f is a unimodular row over R.
U = qsAlgorithm f
U = qsAlgorithm(f,Verbose => 1)
U = qsAlgorithm(f,Verbose => 2)
U = qsAlgorithm(f,Verbose => 3)

K = ker f
isProjective K
P = presentation K
mingens K
syz mingens K
B = computeFreeBasis K
numcols B
image B == K
syz B

isUnimodular(f) -- Verify that f is unimodular.
time qsAlgorithm f -- ~.07 seconds
U = qsAlgorithm f
det U
f*U
-- Here is the method step by step:
currVar = y -- Set y to be the variable that we would like to eliminate.
f -- Notice that the third component of f is monic in y.
(M1,subs,invSubs) = changeVar(f,{x,y})
f = f*M1 -- Put monic component first. (Normalization step.)
I1 = ideal(2,x) -- Choose an arbitrary maximal ideal in ZZ[x].
U1 = horrocks(f,y,I1) -- Compute a local solution with respect to I1.
det(U1) -- The determinant is a unit in the localization.
f*U1 -- U1 really is a local solution to the unimodular row problem.
r1 = commonDenom(U1) -- Set r1 to be the common denominator of the elements of U1.
ideal(r1) == R  -- Since r1 is not a unit in ZZ[x], we need to compute another local solution.
I2 = getMaxIdeal(ideal(r1),{x})
r1 % I2 -- Verify that r1 is actually in I2.
U2 = horrocks(f,y,I2) -- Compute a local solution with respect to I2.
det(U2) -- The determinant is a unit in the localization.
f*U2 -- U2 is a local solution to the unimodular row problem.
r2 = commonDenom(U2) -- Set r2 to be the common denominator of elements of U1.
ideal(r1,r2) == R -- Since r1 and r2 generate the unit ideal, we exit the local loop.
matrixList = {U1,U2} -- Make a list of our local solutions.
M2 = patch(matrixList,y) -- Apply the patching process to create a matrix M2 which kills y.
f*M2
isUnimodular M2

det(M2) -- M2 is unimodular.
f -- Recall what f was.
f = f*M2 -- Multiplying f by M2 is equivalent to setting y=0.
M3 = applyRowShortcut(f) -- Now that f involves only one variable, we can apply a shortcut method.
det(M3) -- M3 is unimodular.
f*M3 -- M3 solves the unimodular row problem for |x 1 x^2|.
U = M1*M2*M3 -- Gather up all of the matrices used in the computation.
det(U) -- U is unimodular and solves the unimodular row problem.
inverse(U) -- Note that f is the first row of U^-1.
-- So U^-1 extends f to a square invertible matrix over R.

--Ex. GagoVargas (Works fine, uses shortcut 2.2.2(2).)

restart;
load("QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{13,x^2-1,2*x-5}}
K = ker f
P = presentation K
isProjective K

B = computeFreeBasis(K,Verbose => 5)
mingens K
image B == K

isUnimodular(f)
U = qsAlgorithm(f) -- Uses shortcut 2.2.2(2).
time qsAlgorithm(f) -- ~.016 seconds
det(U)
f*U


--Ex. LaubenbacherWoodburn (Works fine, uses shortcut 2.2.1(2).)

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x^2*y+1,x+y-2,2*x*y}}
U = qsAlgorithm(f) -- Uses shortcut 2.2.1(2).
det(U)
f*U

--Ex1. Yengui (Works fine, uses shortcut 2.2.2(1).)

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x-4*y+2,x*y+x,x+4*y^2-2*y+1}}
isUnimodular(f)
U = qsAlgorithm(f)
det(U)
f*U


--Ex.2 Yengui (Works fine, uses shortcut 2.2.2(2).)

restart;
load("QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{x^2+2*x+2,3,2*x^2+2*x}}
U = qsAlgorithm(f) -- Uses shortcut 2.2.2(2).
det(U)
f*U


--Ex.3 Yengui (Works fine, uses shortcut 2.2.2(2).)

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x+y^2-1,-x+y^2-2*x*y,x-y^3+2}}
isUnimodular(f)
U = qsAlgorithm(f)
time qsAlgorithm(f) -- ~.016 seconds
det(U)
f*U


--Ex. Park (Works fine, uses shortcut 2.2.1(2).)

restart;
load("QuillenSuslin.m2");
R = ZZ[x,y,z]
f = matrix{{1-x*y-2*z-4*x*z-x^2*z-2*x*y*z+2*x^2*y^2*z-2*x*z^2-2*x*z^2-2*x^2*z^2+2*x*z^2+2*x^2*y*z^2,2+4*x+x^2+2*x*y-2*x^2*y^2+2*x*z+2*x^2*z-2*x^2*y*z,1+2*x+x*y-x^2*y^2+x*z+x^2*z-x^2*y*z,2+x+y-x*y^2+z-x*y*z}}
ideal(f_(0,1),f_(0,2)) == R
U = qsAlgorithm(f) -- Uses shortcut 2.2.1(2).
det(U)
f*U


--Ex. Van den Essen (No shortcut method works.)

-- ***** This example needs to be fixed for computeFreeBasis.

restart;
load("QuillenSuslin.m2");
R = QQ[t,x,y,z]
f = matrix{{2*t*x*z+t*y^2+1,2*t*x*y+t^2,t*x^2}}
U = qsAlgorithm f
V = transpose submatrix(inverse U,1..2,0..2)
P = ker f
isProjective P
rank P
syz mingens P
L = (presentation P)^{0}

B = computeFreeBasis(P,Verbose => 5)
g = matrix{{-2*x*y^3-4*x^2*y*z-1,-2*x*y^5-4*x^2*y^3*z-y^2-2*x*z,-2*y^6-4*x*y^4*z+2*t*y^3*z+4*t*x*y*z^2}}

transpose f
isUnimodular transpose f
C = coker transpose f
isProjective C
mingens C
rank C
B = computeFreeBasis C
fMap = map(R^3,R^1,transpose f)
(image B)/(image fMap) == coker(fMap)


-- Running through by hand what computeFreeBasis should do.
F = res C
p = length F
A = F.dd_1
numRowsA = numrows A
numColsA = numcols A
print transpose A
completeMatrix(transpose A,Verbose => 5)
C = submatrix'(transpose completeMatrix transpose A,,{0..(numcols A - 1)})
mingens((image map(R^(numRowsA),R^(numRowsA - numColsA),C))/(image map(R^numRowsA,R^numColsA,A)))
     


-- *** coimage also needs to be handled
-- Also make sure this works for free modules such as R^3.
C = coimage f
isProjective coimage f
rank C
B = computeFreeBasis coimage f
syz B
fMap = map(R^1,R^3,f)
minGens = mingens((image B)/(ker fMap))
(image minGens)/(ker fMap) == (coimage fMap) 
presentation coimage f
res coimage f

-- *** Implement this.
completeMatrix(transpose f)
qsAlgorithm transpose f

A = completeMatrix f
At = transpose A
Basis = At_{1,2} -- Residue classes of last two columns should be an R-basis for coker transpose f
syz Basis
Basis % (image transpose f) -- The basis is nonzero modulo image transpose f.
-- Basis from Fabianska's example.
FabBasis = transpose matrix{{t*y^6+6*t*y^4*x*z+8*t*x^3*z^3+12*x^2*z^2*t*y^2+2*t*y^9*x+24*y^5*z^2*x^3*t+12*y^7*z*t*x^2+16*z^3*x^4*t*y^3 , 1-t*y^2+4*t*y^3*z*x^2-2*t*x*z+4*t^2*y^2*x*z+t^2*y^4+4*t*y^8*x^2+4*x^2*z^2*t^2+2*y^7*x*t^2+8*z^2*y*t*x^3+16*t*x^4*z^2*y^4+16*t*x^3*z*y^6+8*x^3*z^2*y^3*t^2+8*x^2*z*y^5*t^2 , 4*t*y^2*z*x^3+t*y^4*x^2+4*x^4*z^2*t+2*y^7*x^3*t+8*x^5*z^2*t*y^3+8*x^4*z*t*y^5},{-4*t*y^(10)-16*x^2*z^3*t*y-4*y^5*z*t-32*t*x^3*z^3*y^4-48*t*z^2*x^2*y^6-24*t*y^8*z*x-16*t*y^3*z^2*x , 4*t*y*z+4*t*y^6-4*t^2*y^8-8*y*x*z^2*t^2-4*y^3*z*t^2-16*x^2*z^2*t*y^2-8*t*y^9*x-16*y^6*z*t^2*x-16*t^2*y^4*z^2*x^2-32*y^5*z^2*x^3*t-32*y^7*z*t*x^2 , 1-4*t*y^3*z*x^2-4*t*y^8*x^2-8*z^2*y*t*x^3-16*t*x^4*z^2*y^4-16*t*x^3*z*y^6}}
syz FabBasis
g = map(R^3,R^1,transpose f)
FabBasis = map(R^3,R^2,FabBasis)
(image Basis)/(image g) == (image FabBasis)/(image g)
prune((image Basis)/(image g))
minGens = mingens((image Basis)/(image g)) -- Macaulay2 will calculate a 'better' basis.
syz minGens
(image minGens)/(image g) == (image Basis)/(image g)
C
K = ker f
presentation K
syz mingens K
class ker f


isUnimodular f
time qsAlgorithm f -- ~.35 seconds
U = qsAlgorithm f
det U
f*U

-- Illustration of step by step method:
(M,subs,invSubs) = changeVar(f,{t,x,y,z})
f = f*M
g = sub(f,subs)
I1 = ideal(t,x,y)
U1 = horrocks(g,z,I1)
det U1
g*U1
r1 = commonDenom(U1)
ideal(r1) == R
-- Need to find a maximal ideal containing r1.
I2 = getMaxIdeal(ideal(r1),{t,x,y})
U2 = horrocks(g,z,I2)
g*U2
det U2
r2 = commonDenom(U2)
ideal(r1,r2) == R
U3 = patch({U1,U2},z)
g*U3

-- Using output from Fabianska's horrocks method:
-- Now our output is essentially the same.
R = QQ[t,x,y,z]
d1 = -1-x^2+4*x^2*y*t+2*x*y^3
V1 = matrix{{(-1-x^2+4*y*t*x^2+2*y^3*x+2*z*x*t+z*y^2)/d1, -z*(-4*x^3*y+8*y^2*t*x^3+4*y^4*x^2-2*x*y-z*x^2+4*z*y*t*x^2+2*z*y^3*x-z)/((1+x^2)*d1),-z*(-x^2+4*y*t*x^2+2*z*x*t+2*y^3*x+z*y^2)/d1},
     {-(2*x*t+y^2)^2/d1, -(1+2*x^2+x^4-4*y*t*x^2-2*y^3*x+2*x^3*t*z-8*t^2*y*z*x^3-8*z*y^3*t*x^2+2*z*x*t+z*y^2*x^2-2*z*y^5*x+z*y^2)/((1+x^2)*d1),((2*z*x*t+z*y^2+1)*(2*x*t+y^2))/d1},
     {(2*x*t+y^2)/d1,(2*x^3*y+z*x^2-4*z*y*t*x^2-2*z*y^3*x+z)/((1+x^2)*d1),-(2*z*x*t+z*y^2+1)/d1}}
V2 = matrix{{1,0,-z},{0,1,0},{-(2*x*t+y^2)/x^2,-(2*x*y+z)/x^2,(2*z*x*t+z*y^2+1)/x^2}}
g*V2

V = patch({V1,V2},z) -- Patching code seems to work fine. Gives same output as Fabianska's code.
g*V


--Ex. CoxLittleOShea10 (Works fine, uses shortcut 2.2.2(1).)

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1+x,1-y,x*(1+y)}}
isUnimodular(f)
U = qsAlgorithm(f)
det(U)
f*U


--Ex. CoxLittleOShea27 (Works fine, uses shortcut 2.2.2(2).)

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1+x*y+x^4,y^2+x-1,x*y-1}}
isUnimodular(f)
U = qsAlgorithm(f)
time qsAlgorithm(f) -- ~.012 seconds
det(U)
f*U


--Ex1. Brett (Slightly bigger example, works fine, uses (p-1) x p shortcut.)
restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1,-2*x*y,-x-y+2},{-1/2*x,x^2*y+1,1/2*x^2+1/2*x*y-x}}
isUnimodular(f)
U = qsAlgorithm(f)
time qsAlgorithm(f) --.004 seconds both ways.
det U
f*U


--Ex2. Brett (Testing Fabianska shortcut 2.2.1(3).)

restart;
load("QuillenSuslin.m2");
R = QQ[x]
f = matrix{{x^2+1,x-2,0}} -- Row contains a zero.
U = qsAlgorithm(f)
det(U)
f*U

f = matrix{{x^2+1,x-2,x^2+3,x-3}} -- Row contains a redundant entry.
U = qsAlgorithm(f)
det(U)
f*U

restart;
load "QuillenSuslin.m2"
R = ZZ[x,y]
f = matrix{{x^2,3*y+1,x+x^2*y+y^2}}
qsAlgorithm f

U = matrix{{x^2,3*y+1,x+x^2*y+y^2},{-84*x^2+27*x^3+1,-84+27*x,-84*x+9*x*y+27*x^2-28*y},{243*x^2-3,243,243*x+81*y+1}}


-- Testing 'horrocks':

restart;
load("QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{y^2+x^2*y+x,3*y+1,x^2}}
K = ker f
syz mingens K
computeFreeBasis K
I = ideal(2,x)
U1 = horrocks(f,y,I)
d1 = commonDenom(U1)
ideal(d1) == R
time horrocks(f,y,I) -- ~.05 seconds
I2 = getMaxIdeal(ideal(d1),{x})
U2 = horrocks(f,y,I2)
d2 = commonDenom(U2)
ideal(d1,d2) == R
U = patch({U1,U2},y)
det(U)
f*U

f = matrix{{1,x^2+1,x-2}} -- Test for deg(f1) = 0.
I = ideal(2)
U = horrocks(f,x,I)
det(U)
f*U

f = matrix{{y+6,y+5}} -- Test for nCol = 2.
U = horrocks(f,y,I)
det(U)
f*U

f = matrix{{2,x^2+1,x-2}} -- Test for error: not monic.
U = horrocks(f,x,I)

f = matrix{{x+6,x+4}} -- Test for error: not unimodular.
isUnimodular(f)
U = horrocks(f,x,I,CheckUnimodular => true)


-- Testing normalization process.

-- Testing the special case n = 2.
restart;
load("QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{2*x,2*x-1}}
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{x})
det(M)
f*M

-- Testing case where f already has a monic component.
-- The routine moves the lowest degree monic component to
-- the front.
restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{3*x*y^2+2*x*y+3,y^3+2*x^2*y+4,y^2}} -- The last entry is monic in y of degree 2.  The second entry is monic in y of degree 3.
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{x,y})
det(M)
f*M
sub(f*M,subs) -- The first component is now the smallest degree component that was monic in y.


-- Testing the case where f contains a monic component
-- in a different variable.  The routine finds the smallest
-- degree where this happens and moves this to the front
-- and makes the appropriate substitution.
restart;
load("QuillenSuslin.m2");
R = QQ[t,x,y,z]
-- The second component is monic in t of degree 2.
f = matrix{{2*t*x*z+t*y^2+1,2*t*x*y+t^2,t*x^2}} -- Van den Essen example.
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{t,x,y,z})
det(M)
f*M
g = sub(f*M,subs) -- The first component of the row is now monic in z.


-- Redundant row entry, so changeVar can use a shortcut method.
restart;
load("QuillenSuslin.m2");
R = ZZ[x,y,z]
f = matrix{{1-x*y-2*z-4*x*z-x^2*z-2*x*y*z+2*x^2*y^2*z-2*x*z^2-2*x*z^2-2*x^2*z^2+2*x*z^2+2*x^2*y*z^2,2+4*x+x^2+2*x*y-2*x^2*y^2+2*x*z+2*x^2*z-2*x^2*y*z,1+2*x+x*y-x^2*y^2+x*z+x^2*z-x^2*y*z,2+x+y-x*y^2+z-x*y*z}}
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{x,y,z}) -- One of the row entries is redundant so we can use a shortcut method.
det(M)
g = sub(f*M,subs)


-- Over QQ. No component of the row is monic in x or y or is just a constant times x or y.
-- Also all 3 components are needed to generate the entire ring.
restart;
load("QuillenSuslin.m2");
R = ZZ/7[x,y]
f = matrix{{2*x^2*y+x*y+1,3*x^2*y^2+x*y,5*x^3*y^2+x*y}}
isUnimodular(f)
changeVar(f,{x,y})

-- This would be the result if we just used 1/2 to make
-- the highest total degree term of f1 monic, then used
-- the appropriate change of variables.
M = matrix{{1/2,0,0},{0,1,0},{0,0,1}}
subs = matrix{{x+y,y}}
invSubs = matrix{{x-y,y}}
g = f*M
g = sub(g,subs)
leadCoeffVar(g_(0,0),y)
U = horrocks(g,y,ideal(x)) -- U takes up about 150 lines of output.
commonDenom(U)
sub(det(U),R) % ideal(x)
g*U

-- This would be the result if instead we use the relation
-- in ZZ on the leading coefficients of f2 and f3 (avoiding
-- rational numbers) and then make the change of variables.
subs = matrix{{x+y,y}}
invSubs = matrix{{x-y,y}}
M = matrix{{1,0,0},{2*x,1,0},{-1,0,1}}
g = f*M
g = sub(g,subs)
leadCoeffVar(g_(0,0),y)
U = horrocks(g,y,ideal(x)) -- U takes up about 320 lines of output.
commonDenom(U)
sub(det(U)*commonDenom(matrix{{det(U)}}),R) % ideal(x)
g*U


restart;
load("QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{2*x^2*y+2*x*y+1,2*x^2*y^2+2*x*y,2*x^3*y^2-3*x^2*y^3+x*y}}
leadTerm(x^2*y+x^5*y^2+y^3+x^2*y^3)
isUnimodular(f)
gcd(f_(0,0),f_(0,1))
gcd(f_(0,0),f_(0,2))
gcd(f_(0,1),f_(0,2))
(M,subs,invSubs) = changeVar(f,{x,y})
g = sub(f*M,subs) -- The first term of g is now monic in y.
isMonic(g_(0,0),y) -- Check

restart;
load("QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{2*x^3+2*x^2+1,2*(x^4+x^2),2*(x^5+x^2)}}
computeFreeBasis ker f
completeMatrix f

isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{x})
g = sub(f*M,subs)
I1 = ideal(2,x)
U1 = horrocks(g,x,I1)


--Example:

R = ZZ[x,y]
f = matrix{{2*x^2*y^2+4*x*y+3,2*x^2*y^3+7*x*y+2,2*x^2*y^2+2*x*y+4}}
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,{x,y})
g = sub(f*M,subs)
isMonic(g_(0,0),y)

-- Two variable example.
restart;
load("QuillenSuslin.m2");
debug QuillenSuslin
R = ZZ[x,y]
f1 = (2*x^2+3*x)*y^2+3
f2 = 3*x^2*y^3+7*x*y+2
f3 = 2*x^2*y^2+2*x*y+4     
f4 = x^2*y-x*y^2+2*x*y+3
f5 = 2*x^3*y-x^2*y^2+y

am = findAlmostMonicPoly(ideal(f1,f3),{x,y})
isAlmostMonic(am,{x,y})
(subs,invSubs) = monicPolySubs(am,{x,y})
g = sub(am,subs)
isMonic(g,y)

---

restart;
load("QuillenSuslin.m2");
R = ZZ[z,y,x,MonomialOrder => Lex]
f1 = 2*x^2*y + 3*y^2*z - 4*x*z^2+2
f2 = 3*x*y + 5*x^2*z + 6*x*y^2

f1 = 2*x*y*z^3+3*x
f2 = 2*y^3*z^2+y*z
gcd(f1,f2)
2*f1+1

G = flatten entries gens gb ideal(f1,f2)
lcIdealGens1 = new List from {} -- Polynomials in x,y.
apply(i=0..(#G - 1),i -> lcIdealGens1 = append(lcIdealGens1,leadCoeffVar(G#i,z)))
lcIdealGens1
gbGens1 = flatten entries gens gb ideal(lcIdealGens1)
lcIdealGens2 = new List from {} -- Polynomials in x.
apply(i=0..(#gbGens1 - 1), i -> lcIdealGens2 = append(lcIdealGens2,leadCoeffVar(gbGens1#i,y)))
lcIdealGens2
gbGens2 = flatten entries gens gb ideal(lcIdealGens2)
lcIdealGens3 = new List from {} -- Constants.
apply(i=0..(#gbGens2 - 1), i -> lcIdealGens3 = append(lcIdealGens3,leadCoeffVar(gbGens2#i,x)))
lcIdealGens3
A = map(R^1) // matrix{lcIdealGens3}

xDegList = new List from {}
apply(i=0..(#gbGens2 - 1),i -> xDegList = append(xDegList,degVar(gbGens2#i,x)))
maxXDeg = max(xDegList)
xOffsetMatrix = mutableIdentity(R,#gbGens2)
apply(i=0..(#gbGens2 - 1),i -> xOffsetMatrix_(i,i) = x^(maxXDeg - degVar(gbGens2#i,x)))
xOffsetMatrix = matrix(xOffsetMatrix)

yDegList = new List from {}
apply(i=0..(#gbGens1 - 1),i -> yDegList = append(yDegList,degVar(gbGens1#i,y)))
maxYDeg = max(yDegList)
yOffsetMatrix = mutableIdentity(R,#gbGens1)
apply(i=0..(#gbGens1 - 1),i -> yOffsetMatrix_(i,i) = y^(maxYDeg - degVar(gbGens1#i,y)))
yOffsetMatrix = matrix(yOffsetMatrix)

zDegList = new List from {}
apply(i=0..(#G - 1),i -> zDegList = append(zDegList,degVar(G#i,z)))
maxZDeg = max(zDegList)
zOffsetMatrix = mutableIdentity(R,#G)
apply(i=0..(#G - 1),i -> zOffsetMatrix_(i,i) = z^(maxZDeg - degVar(G#i,z)))
zOffsetMatrix = matrix(zOffsetMatrix)

B = xOffsetMatrix*A
B = (matrix{gbGens2} // matrix{lcIdealGens2})*B
B = yOffsetMatrix*B
B = (matrix{gbGens1} // matrix{lcIdealGens1})*B
B = zOffsetMatrix*B
B = (flatten entries (matrix{G}*B))#0
isAlmostMonic(B,{x,y,z})

restart;
load("QuillenSuslin.m2");
R = ZZ[x,y,z]
f1 = 2*x^2*y + 3*y^2*z - 4*x*z^2+2
f2 = 3*x*y + 5*x^2*z + 6*x*y^2
m = findAlmostMonicPoly(ideal(f1,f2),{x,y,z})
m % ideal(f1,f2)
isAlmostMonic(m,{x,y,z})

restart;
load "QuillenSuslin.m2"
R = ZZ[x,y]
f2 = 3*x^2*y^3+7*x*y+2
f3 = 2*x^2*y^2+2*x*y+4     
am = findAlmostMonicPoly(ideal(f2,f3),{x,y})
am % ideal(f2,f3)
isAlmostMonic(am,{x,y})
(subs,invSubs) = monicPolySubs(am,{x,y})
g = sub(am,subs)
isMonic(g,y)
h = sub(g,invSubs)
h == am

R = ZZ[x,y,z]
f = (x*y^2+x^2*y)*z^3 + 3*x^(50)*y^5*z^2 + 5*x^(70)*y^4*z
(subs,invSubs) = monicPolySubs(f,{x,y,z})
g = sub(f,subs)
isMonic(g,z)
h = sub(g,invSubs)
f == h

restart;
load("QuillenSuslin.m2");
debug QuillenSuslin
R = ZZ[x,y,z]
f1 = sum(i=0..2,i->random(i,R)); f2 = sum(i=0..2,i->random(i,R)); f3 = sum(i=0..1,i->random(i,R)); f4 = sum(i=0..1,i->random(i,R));
f = matrix{{f1,f2,f1*f3+f2*f4+1}}
(M,subs,invSubs) = changeVar(f,{x,y,z})
g = f*M
h = sub(g,subs)
isMonic(h_(0,0),z)
I1 = ideal(2,x,y)
U1 = horrocks(h,z,I1)
det U1
d1 = commonDenom(U1)
ideal(d1) == R
I2 = getMaxIdeal(ideal(d1),{x,y})
U2 = horrocks(h,z,I2)
d2 = commonDenom(U2)
ideal(d1,d2) == R
I3 = getMaxIdeal(ideal(d1,d2),{x,y})
U3 = horrocks(h,z,I3)
d3 = commonDenom(U3)
ideal(d1,d2,d3) == R
patch({U1,U2,U3},z)

-- Testing the maximal ideal code.

restart;
load("QuillenSuslin.m2");
R = QQ[x,y,z]
f = sum(i=0..4,i -> random(i,R))
I = ideal(f)
m = getMaxIdeal(I,{x,y,z})
m:I

R = ZZ/7[x,y,z]
f = sum(i=0..2,i -> random(i,R))
g = sum(i=0..3,i -> random(i,R))
I = ideal(f,g)
M = getMaxIdeal(I,{x,y,z})
(sub(f,R) % sub(M,R),sub(g,R) % sub(M,R))


restart;
R = ZZ/7[x,y,z]
load("QuillenSuslin.m2");
f = 1;
apply(i=0..6, i-> f = f*(x-i));
apply(i=0..6, i-> f = f*(y-i));
apply(i=0..6, i-> f = f*(z-i));
f = f-1;
f
I = ideal(f)
m = getMaxIdeal(I,{x,y,z})
m:I

loadPackage("InvolutiveBases")
factorModuleBasis janetBasis (I + sub(ideal(y-z),R))
factorModuleBasis janetBasis(I)
maxIndepVarSet(I)
S = (frac (ZZ/7[y,z]))[x]
J = sub(I,S)
A = basisElements janetBasis J
B = sub(A,frac(ZZ/7[y,z]))
D = commonDenom(B)
N = toList factor(D)
(N#0)#0 -- Have to go 2 layers down to get the prime factors.
T = ZZ/7[y,z]
N2 = new List from {}
apply(i=0..(#N-1), i -> N2 = append(N2,(N#i)#0))

r = random(1,T)
apply(i=0..(#N2 - 1),i -> if r % sub(ideal(N2#i),T) == 0 then print "No.");

codim I
(z-x) % I == 0
I + ideal(z-x) == R
I = I+ideal(z-x,z-y)
codim I
getMaxIdeal(I,{x,y,z})

--

restart;
load("QuillenSuslin.m2");
-- Example when I is generated by 1 polynomial of degree 2 in 3 var.
R = ZZ[x,y,z]
f = sum(i=0..2,i -> random(i,R))
I = ideal(f)
M = getMaxIdeal(I,{x,y,z})
M:I

f = 5*x  + 4*x*y + 9*y  + 5*x*z + 6*z  + 3*x + 4*y + 2*z + 9
I = ideal(f)
M = getMaxIdeal(I,{x,y,z})
M:I

-- Example when I is generated by 2 polynomials of deg 2 and 3 in 3 var.
R = ZZ[x,y,z]
f = sum(i=0..2,i -> random(i,R))
g = sum(i=0..3,i -> random(i,R))
I = ideal(f,g)
M = getMaxIdeal(I,{x,y,z})
M:I

-- Example where the maximal ideal algorithm needs to add in the prime number 2.
R = ZZ[x,y,z]
I = ideal(45*y^2 , y^2*x^2 + 27*y^2*x + 37*y^2)
gens gb I
m = getMaxIdeal(I,{x,y})
m:I

restart;
R = ZZ[x,y,z]
load("QuillenSuslin.m2");
I = ideal(3,2*x^2+y^3-5,3*z^2+3*x*y^4+3)
gens gb I
M = getMaxIdeal(I,{x,y,z})
M:I

R = ZZ[x,y]
I = ideal(27,x^2+1)
M = getMaxIdeal(I,{x,y})
M:I

R = ZZ[x,y]
I = ideal(x^2+1)
M = getMaxIdeal(I,{x,y})
sub((x^2+1),R) % M

R = ZZ[x,y]
I = ideal(2*x^5+4*x+5,x^5+2*x+1)
gens gb I
m = getMaxIdeal(I,{x,y})
m:I
J = sub(I,ZZ/3[x,y])
m = getMaxIdeal(J,{x,y})
M = sub(m,R)+ideal(3_R)
((gens I)_(0,0) % M,(gens I)_(0,1) % M)

R = ZZ[x,y,z]
I = ideal(6*x*y + 7, 5*x^2*z + 4)

J = sub(I,ZZ/7[x,y,z])
m = getMaxIdeal(J,{x,y,z})
P2 = sub(m,R) + sub(ideal(7),R)
sub((6*x*y+7),R) % sub(P2,R)
sub((5*x^2*z+4),R) % sub(P2,R)

M = getMaxIdeal(sub(I,QQ[x,y,z]),{x,y,z})
gens gb M
gens gb I
I + ideal(2_R) == R
I + ideal(3_R) == R
I + ideal(5_R) == R
I + ideal(7_R) == R
M = getMaxIdeal(I,{x,y,z})

R = ZZ/3[x,y]
loadPackage("InvolutiveBases")
J = ideal(x^2+1)
B = janetBasis(J)
F = factorModuleBasis(B)
maxIndepVarSet(J)
peek F
F#0
values ((F#1)#0)
codim J
(x^3+1) % J == 0
J + ideal(x^3+1) == R
getMaxIdeal(J,{x,y})


-- Testing changeVar code over QQ and ZZ/p.

restart;
load("QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{2*x^2*y+x*y+1,3*x^2*y^2+x*y,5*x^3*y^2+x*y}}
isUnimodular(f)
(U,subs,invSubs) = changeVar(f,{x,y})
sub(f*U,subs)
isMonic((sub(f*U,subs))_(0,0),y)




-- Checking whether we can compute free bases of high syzygies.
-- Need to think about this to make nontrivial examples.

restart
load "QuillenSuslin.m2"
R = QQ[x,y,z]
f = random(R^2,R^{-1,-2,-2,-3,-3})
M = ker f
P = image (res comodule M).dd_2
rank P
syz gens P
computeFreeBasis P == gens P

loadPackage "QuillenSuslin"
R = ZZ/101[x,y]
--while not isProjective B do (
--A = random(R^{0,-1,-3},R^{-3});
--B = coker A;
--)
A = matrix {{-8*x^3+15*x^2*y+31*x*y^2+27*y^3}, {47*x^2-35*x*y+5*y^2}, {49}}
ker A
B = cokernel A
isProjective B
computeFreeBasis B
gens B
mingens B
B
res B
gens B
image A
mingens image A
(R^3)/(image A)
