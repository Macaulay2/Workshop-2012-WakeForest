rightHomogKernelOld = method()
rightHomogKernelOld(NCMatrix, ZZ) := (M,d) -> (
   -- Assume (without checking) that the entries of M are homogeneous of the same degree n
   -- This function takes a NCMatrix M and a degree d and returns the left kernel in degree d over the tensor algebra
   rows := # entries M;
   cols := # first M.matrix;
   n := max apply(flatten entries M, i->degree i);
   degnBasis := flatten entries basis(n,M.ring);
   -- We compute the left multiplication maps once and for all. 
   -- In the future, maybe only compute them for elements actually appearing in the matrix.
   maps := apply(degnBasis, e->leftMultiplicationMap(e,d));
   B := basis(d,M.ring);
   dimB := #(flatten entries B); --the number of rows of K is dim*cols
   dimT := #(flatten entries basis(n+d,M.ring)); --the number of rows in multiplication map
   -- Make a big matrix of left multiplication maps for each row and get its kernel
   S := apply(toList(0..(rows-1)), i-> 
        ker matrix{apply(toList(0..(cols-1)), j->(
          if (M.matrix)#i#j==0 then matrix apply(toList(0..(dimT-1)), b->apply(toList(0..(dimB-1)),a->0))
          else
             coeffs := flatten entries last coefficients((M.matrix)#i#j,Monomials=>degnBasis);
             sum(0..(#degnBasis-1),k->(coeffs#k)*(maps#k)))
        )});
   Kscalar := gens intersect S;
   if Kscalar == 0 then return 0
   else
   K := ncMatrix apply(toList(0..(cols-1)), k-> flatten ((lift B)*submatrix(Kscalar,{k*dimB..(k*dimB+dimB-1)},)).matrix)
)

--- this was an attempt at speeding up the computations.  It is significantly slower.  I expect
--- because Bergman is doing the reductions much faster than my code.
rightMingens2 = method(Options => {DegreeLimit => 10})
rightMingens2 NCMatrix := opts -> M -> (
   B := ring M;
   if not B#"BergmanRing" then 
      error "Bergman interface can only handle coefficients over QQ or ZZ/p at the present time.";
   if not isHomogeneous M then
      error "Expected a homogeneous matrix.";
   cols := #(M.source);
   rows := #(M.target);
   maxDeg := max M.source + opts#DegreeLimit;
   matrRels := buildMatrixRelations M;
   C := ring first matrRels;
   gensC := gens C;
   gensBinC := take(gensC, numgens B);
   rowGens := take(gensC, -rows);
   ambBtoC := ambient ncMap(C,B,gensC);
   --- At this point matrRels has the relations of the form Col_i - \sum_j f_ij RoW_j.
   --- Need to zero out Col vars, compute a GB, grab the low degree elements, reduce
   --- others mod a GB for that, grab the first nonzero element, add, repeat...
   phi := ncMap(C,C,gensBinC | toList(cols:promote(0,C)) | rowGens);
   initGB := gens twoSidedNCGroebnerBasisBergman((matrRels / phi) | ((gens ideal B) / ambBtoC),
                                                "NumModuleVars" => numgens C - numgens B,
                                                DegreeLimit => opts#DegreeLimit,
                                                ClearDenominators=>false,
                                                CacheBergmanGB=>false);
   initGB = getKernelElements(initGB,gensBinC,rowGens);
   initGB = sortUsing(initGB, f -> (degree f, size f));
   --- at this point, initGB has a GB of the column space of the matrix.
   minDeg := min (initGB / degree);
   minGens := select(initGB, f -> degree f == minDeg);
   otherGens := select(initGB, f -> degree f != minDeg);
   while otherGens != {} do (
      --- compute a GB of the mingens so far
      minGensGB := twoSidedNCGroebnerBasisBergman(minGens | ((gens ideal B) / ambBtoC),
                                              "NumModuleVars" => numgens C - numgens B,
                                               DegreeLimit => opts#DegreeLimit,
                                               ClearDenominators=>true,
                                               CacheBergmanGB=>false);
      --- reduce the other gens mod this GB, and select the nonzero images
      possGens := select(apply(otherGens, f -> f % minGensGB), g -> g != 0);
      if possGens != {} then (
         -- if some don't reduce to zero, then add the first one, reset and continue
         minGens = minGens | {first possGens};
         otherGens = drop(possGens, 1);
      )
      else
         otherGens = possGens;
   );
   -- at this point, minGens has the minimal generators we want.  Now put them in
   -- a matrix.
   minGensMatrix := getModuleCoefficients(minGens, rowGens);
   assignDegrees(minGensMatrix,M.target, minGens / degree);
   minGensMatrix
)

------------------------------------------------------------
--- fast exponentiation via repeated squaring.
-----------------------------------------------------------
quickExponentiate = method()
quickExponentiate (ZZ, NCRingElement) := (n, f) -> (
   if n == 0 then return promote(1,f.ring);
   expList := rebase(2,n);
   loopPower := f;
   product for i from 0 to #expList-1 list (
      oldLoopPower := loopPower;
      if i != #expList-1 then loopPower = loopPower * loopPower;  -- last time through no need to exp again
      if expList#i == 0 then continue else oldLoopPower
   )
)

-- it seems that reducing at each step is actually much more important than minimizing the
-- number of matrix products computed.  The number of monomials in the tensor algebra is huge!
quickExponentiate (ZZ, NCMatrix) := (n, M) -> (
   rowsM := length M.matrix;
   colsM := length first M.matrix;
   if rowsM != colsM then error "Expected a square matrix.";
   if n == 0 then return ncMatrix apply(0..(rowsM-1), r -> apply(0..(colsM-1), c -> if r == c then promote(1,M.ring) else promote(0,M.ring)));
   expList := rebase(2,n);
   loopPower := M;
   matrList := for i from 0 to #expList-1 list (
      oldLoopPower := loopPower;
      if i != #expList-1 then loopPower = loopPower * loopPower;  -- last time through no need to exp again
      if expList#i == 0 then continue else oldLoopPower
   );
   product matrList
)
