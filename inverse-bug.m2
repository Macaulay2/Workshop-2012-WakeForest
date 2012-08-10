-- reported by Brett
load "newquot.m2"
R = ZZ/101[x,y]
phi = (minimalPresentation ker matrix{{x^2+1, x, y}}).cache.pruningMap
isIsomorphism phi
 phi^-1 -- fails
 break
f = id_(target phi)
g = phi
quotientRemainder(f,g)					    -- wrong answer
f//g							    -- wrong answer
f%g							    -- insists on free modules
-- from quotientRemainder(Matrix,Matrix) := Matrix => (f,g) -> 
     M = target f
     L = source f
     N = source g
     f = matrix f
     g = matrix g
     ( map(N, L, f//g), map(M, L, f%g) )

The problem is that quotientRemainder doesn't work when M.?generators!


-----------------------------------------------------------------------------

examples possibly affected:

     	  R = ZZ/32003[a..d];
	  I = monomialCurveIdeal(R,{1,3,4})
	  M1 = R^1/I
	  M2 = R^1/ideal(I_0,I_1)
	  f = inducedMap(M1,M2)
	  Ext^1(f,R)
	  g = Ext^2(f,R)
	  source g == Ext^2(M1,R)
	  target g == Ext^2(M2,R)
	  Ext^3(f,R)


     	  R = ZZ/32003[a..d];
	  I = monomialCurveIdeal(R,{1,3,4})
	  M = R^1/I
	  f = inducedMap(R^1,module I)
	  Ext^1(M,f)
	  g = Ext^2(M,f)
	  source g == Ext^2(M,source f)
	  target g == Ext^2(M,target f)
	  Ext^3(f,R)


	  R = QQ[x,y];
	  I = ideal vars R
	  M = image vars R
	  N = prune M
	  f = N.cache.pruningMap
	  isIsomorphism f
	  f^-1


	--/Users/dan/src/M2/trunk/M2/Macaulay2/packages/Macaulay2Doc/doc8.m2:397: location of test code
	R = ZZ/101[a..d]
	A = image matrix {{a}}
	B = image matrix {{b}}
	f = inducedMap((A+B)/A, B/intersect(A,B))
	assert isIsomorphism f
	g = f^-1
	assert( f^-1 === g )			  -- check caching of inverses
	assert( f*g == 1 )
	assert( g*f == 1 )
	assert isWellDefined f
	assert isWellDefined g
	assert not isWellDefined inducedMap(R^1,cokernel matrix {{a}},Verify => false)


	--/Users/dan/src/M2/trunk/M2/Macaulay2/packages/NormalToricVarieties.m2:4421: location of test code
     loadPackage "NormalToricVarieties"
	X = weightedProjectiveSpace {1,2,3};
	assert(rays X == {{-2,-3},{1,0},{0,1}})
	assert(max X == {{0,1},{0,2},{1,2}})
	assert(dim X == 2)	  
	assert(orbits(X,0) === max X)
	assert(orbits(X,1) === apply(3, i -> {i}))
	assert(isDegenerate X === false)
	assert(isSimplicial X === true)
	assert(isSmooth X === false)
	assert(isProjective X === true)
	assert(isFano X === true)
	assert(wDiv X == ZZ^3) 
	assert(fromWDivToCl X == map(ZZ^1,ZZ^3, matrix{{1,2,3}}))
	assert(cl X == ZZ^1)
	assert(cDiv X == ZZ^3)
	assert(fromCDivToPic X == map(ZZ^1,ZZ^3, matrix{{1,0,0}})) -- fails
	assert(pic X == ZZ^1)					   -- fails
	assert(fromPicToCl X == map(ZZ^1,ZZ^1, {{-6}}))            -- fails
	assert(isEffective X_0 === true)
	assert(X_0 + X_1 === toricDivisor({1,1,0},X))
	assert(2*X_0 === X_0 + X_0)
	assert(isNef X_0 === true)
	assert(isCartier X_0 === false)
	assert(isQQCartier X_0 === true)
	assert(isAmple X_1 === false)
	assert(isAmple (3*X_1) === true)
	assert(isVeryAmple (3*X_1) === true)
	assert(vertices (6*X_0) === matrix{{0,3,0},{0,0,2}})
	assert(OO (6*X_0) === OO (3*X_1))
	assert(degrees ring X === apply(3, i -> {i+1}))
	assert(ideal X == ideal gens ring X)
	Y = makeSmooth X;
	assert(isWellDefined Y === true)
	assert(isSmooth Y === true)
	assert(set rays Y === set {{-2,-3},{1,0},{0,1},{-1,-2},{-1,-1},{0,-1}})
	assert(max Y === {{0,3},{0,4},{1,2},{1,5},{2,4},{3,5}})


	--/Users/dan/src/M2/trunk/M2/Macaulay2/packages/NormalToricVarieties.m2:4483: location of test code

	Rho = {{1,0,0},{0,1,0},{0,0,1},{0,-1,-1},{-1,0,-1},{-2,-1,0}};
	Sigma = {{0,1,2},{0,1,3},{1,3,4},{1,2,4},{2,4,5},{0,2,5},{0,3,5},{3,4,5}};
	X = normalToricVariety(Rho,Sigma);
	assert(isWellDefined X === true)
	assert(dim X === 3)
	assert(orbits(X,0) === max X)
	assert(orbits(X,2) === apply(6, i -> {i}))
	assert(isDegenerate X === false)
	assert(isSimplicial X === true)
	assert(isSmooth X === false)
	assert(isComplete X === true)
	assert(isProjective X === false)
	assert(isFano X === false)
	assert(wDiv X == ZZ^6)
	assert(cl X === ZZ^3)
	assert(pic X === ZZ^3)
	assert(isNef(0*X_0) === true)
	assert(all(6, i -> isAmple(X_i) === false))
	Y = makeSmooth X;
	assert(isWellDefined Y === true)
	assert(isSmooth Y === true)


	--/Users/dan/src/M2/trunk/M2/Macaulay2/packages/NormalToricVarieties.m2:4522: location of test code

	setRandomSeed 1
	X = normalToricVariety(id_(ZZ^3) | -id_(ZZ^3));
	assert(isWellDefined X === true)
	assert(set rays X === set entries matrix{{1,1,1},{-1,1,1},{1,-1,1},{-1,-1,1},
	    {1,1,-1},{-1,1,-1},{1,-1,-1},{-1,-1,-1}})
	assert(dim X === 3)
	assert(orbits(X,0) === max X)
	assert(orbits(X,2) === apply(8, i -> {i}))
	assert(isDegenerate X === false)
	assert(isSimplicial X === false)
	assert(isSmooth X === false)
	assert(isProjective X === true)
	assert(isFano X === true)
	assert(wDiv X == ZZ^8) 
	assert(cl X == (cokernel matrix{{2}})^2 ++ ZZ^5)
	assert(pic X == ZZ^1)
	assert(fromWDivToCl X * fromCDivToWDiv X == fromPicToCl X * fromCDivToPic X)
	assert(isEffective X_0 === true)
	assert(isCartier X_0 === false)
	K = toricDivisor X;
	assert(isCartier K == true)
	assert(isNef K == false)
	Y = makeSimplicial X;
	assert(isWellDefined Y === true)
	Y = makeSimplicial X;
	assert(isWellDefined Y === true)
	assert(isSimplicial Y === true)
	assert(isSmooth Y === false)
	Y = makeSimplicial(X, Strategy => 1);
	assert(isWellDefined Y === true)
	assert(isSimplicial Y === true)
	assert(isSmooth Y === false)
	Z = makeSmooth X;
	assert(isWellDefined Z === true)
	assert(isSmooth Z === true)



	--/Users/dan/src/M2/trunk/M2/Macaulay2/packages/NormalToricVarieties.m2:4555: location of test code

	X = normalToricVariety({{1,0,0,0},{0,1,0,0},{0,0,1,0},{1,-1,1,0},{1,0,-2,0}},
	  {{0,1,2,3},{0,4}});
	assert(isWellDefined X === true)
	assert(dim X === 4)
	assert(orbits(X,0) === {})
	assert(orbits(X,1) === {{0,1,2,3}})
	assert(orbits(X,2) === {{0,1},{0,3},{0,4},{1,2},{2,3}})
	assert(orbits(X,3) === apply(5, i -> {i}))
	assert(isDegenerate X === true)
	assert(isSimplicial X === false)
	assert(isSmooth X === false)
	assert(isComplete X === false)
	assert(wDiv X == ZZ^5)
	assert(cl X == ZZ^2)
	assert(pic X == ZZ^1)
	assert(fromWDivToCl X * fromCDivToWDiv X == fromPicToCl X * fromCDivToPic X)
	assert(isEffective X_0 === true)
	assert(isCartier X_0 === false)
	Y = makeSimplicial X;
	assert(isWellDefined Y === true)
	assert(isSimplicial Y === true)
	assert(isSmooth Y === false)
	Y = makeSimplicial(X, Strategy => 0);
	assert(isWellDefined Y === true)
	assert(isSimplicial Y === true)
	assert(isSmooth Y === false)
	Z = makeSmooth X;
	assert(isWellDefined Z === true)
	assert(isSmooth Z === true)


	Macaulay2/packages/Macaulay2Doc/test/extmap.m2