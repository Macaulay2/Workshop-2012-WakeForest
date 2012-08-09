newPackage(
     "EquivariantResolutions",
     Version => "0.1",
     Date => "August 7, 2012",
     Authors => {{Name => "Federico Galetto",
     	       Email => "galetto.federico@gmail.com",
	       HomePage => "http://www.math.neu.edu/~fgaletto/"}},
     Headline => "study resolutions with a semisimple Lie group action",
     DebuggingMode => true
     )

needsPackage "SimpleDoc"
needsPackage "WeylGroups"

export {LieWeights,setLieWeights,getLieWeights,propagate,ToTarget}

--set weights of a ring or module
setLieWeights = method()
--creates a key "LieWeights" within the ring with value a matrix whose rows are weights of the ring variables
--a matrix is created here because it makes computing weights of ring elements easier
setLieWeights (PolynomialRing, List) := Matrix => (R,L) -> (
     if not isTable(L) then error "expected all weights to have the same length";
     for w in L do (for i in w do (if not instance(i,ZZ) then error "expected weights to be integers";););
     if numgens(R)!=#L then error ("expected as many weights as generators of ",toString(R));
     R#LieWeights = matrix L
     )

--creates a key "LieWeights" in the module cache with value a list of weights for the free module generators
setLieWeights (Module, List) := List => (M,L) -> (
     if not isTable(L) then error "expected all weights to have the same length";
     for w in L do (for i in w do (if not instance(i,ZZ) then error "expected weights to be integers";););
     if numgens(M)!=#L then error ("expected as many weights as generators of ",toString(M));
     if not isFreeModule(M) then error "expected a free module";
     M.cache#LieWeights = L
     )

--return the weight of a ring element or the generators of a module
getLieWeights = method(TypicalValue => List)
--weight of ring element (really of its leading monomial)
getLieWeights (RingElement) := List => r -> (
     if r==0 then error "the weight of the zero element is undefined";
     m := matrix exponents leadMonomial r;
     w := m*((ring r).LieWeights);
     return flatten entries w;
     )

getLieWeights (Module) := List => M -> (
     return M.cache.LieWeights;
     )

--propagate weights along maps and resolutions
propagate = method(Options => {ToTarget => false})
--propagate weights along a map of free modules
--the default option ToTarget=>false propagates weights from codomain to domain
--turn it to true to go in the other direction
propagate (Matrix) := List => o -> M -> (
     if o.ToTarget == false then (
	  W := getLieWeights(target M);
	  p := for j to numColumns(M)-1 list position(flatten entries M_j, z -> z != 0);
	  return setLieWeights(source M,for j to #p-1 list (W_(p_j) + getLieWeights(M_(p_j,j))))
	  )
     else (
	  W = getLieWeights(source M);
	  p = for j to numRows(M)-1 list position(flatten entries M^{j}, z -> z != 0);
	  return setLieWeights(target M,for j to #p-1 list (W_(p_j) - getLieWeights(M_(j,p_j))))
	  );
     )

--propagates weights to the whole resolution starting from a given homological degree
propagate (ChainComplex, ZZ) := HashTable => o -> (C,i) -> (
     h := new MutableHashTable from {i => getLieWeights(C_i)};
     for j from i+1 when C_j!=0 do (
	  h#j = propagate(C.dd_j);
	  );
     for j from 1 when C_(i-j)!=0 do (
	  h#(i-j) = propagate(C.dd_(i-j+1),ToTarget=>true);
	  );
     return new HashTable from h;
     )

TEST ///
     A=QQ[x_(1,1)..x_(3,4)];
     RI=res minors(2,genericMatrix(A,4,3));
     setLieWeights(A,{{1,0,0,1,0},{-1,1,0,1,0},{0,-1,1,1,0},{0,0,-1,1,0},{1,0,0,-1,1},{-1,1,0,-1,1},{0,-1,1,-1,1},{0,0,-1,-1,1},{1,0,0,0,-1},{-1,1,0,0,-1},{0,-1,1,0,-1},{0,0,-1,0,-1}});
     setLieWeights(RI_3,{{0, 0, 0, 2, 1}, {0, 0, 0, 0, 2}, {0, 0, 0, -2, 3}, {0, 0, 0, 3, -1}, {1, 0, 1, 1, 0}, {1, 1, -1, 1, 0}, {2, -1, 0, 1, 0}, {-1, 1, 1, 1, 0}, {-1, 2, -1, 1, 0}, {0, 0, 0, 1, 0}, {1, 0, 1, -1, 1}, {1, 1, -1, -1, 1}, {0, -1, 2, 1, 0}, {0, 0, 0, 1, 0}, {0, 0, 0, 1, 0}, {1, -2, 1, 1, 0}, {2, -1, 0, -1, 1}, {0, -1, 2, -1, 1}, {0, 0, 0, -1, 1}, {0, 0, 0, 1, 0}, {0, 1, -2, 1, 0}, {1, -1, -1, 1, 0}, {0, 0, 0, -1, 1}, {0, 1, -2, -1, 1}, {0, 0, 0, -1, 1}, {1, -1, -1, -1, 1}, {0, 0, 0, -3, 2}, {0, 0, 0, 1, 0}, {-2, 1, 0, 1, 0}, {-1, 1, 1, -1, 1}, {-1, 2, -1, -1, 1}, {-1, -1, 1, 1, 0}, {0, 0, 0, -1, 1}, {-2, 1, 0, -1, 1}, {-1, 0, -1, 1, 0}, {-1, 0, -1, -1, 1}, {0, 0, 0, 2, -2}, {1, 0, 1, 0, -1}, {1, 1, -1, 0, -1}, {-1, 1, 1, 0, -1}, {-1, 2, -1, 0, -1}, {0, -1, 2, 0, -1}, {0, 0, 0, 0, -1}, {0, 0, 0, 0, -1}, {0, 0, 0, 0, -1}, {0, 1, -2, 0, -1}, {0, 0, 0, -2, 0}, {0, 0, 0, -1, 1}, {1, -2, 1, -1, 1}, {-1, -1, 1, -1, 1}, {2, -1, 0, 0, -1}, {0, 0, 0, 0, -1}, {1, -2, 1, 0, -1}, {1, -1, -1, 0, -1}, {0, 0, 0, 0, -1}, {-2, 1, 0, 0, -1}, {-1, -1, 1, 0, -1}, {-1, 0, -1, 0, -1}, {0, 0, 0, 1, -3}, {0, 0, 0, -1, -2}});
     W=new HashTable from {0 => {{0, 0, 0, 0, 0}}, 1 => {{0, 1, 0, 0, 1}, {1, -1, 1, 0, 1}, {1, 0, -1, 0, 1}, {-1, 0, 1, 0, 1}, {-1, 1, -1, 0, 1}, {0, -1, 0, 0, 1}, {0, 1, 0, 1, -1}, {1, -1, 1, 1, -1}, {1, 0, -1, 1, -1}, {0, 1, 0, -1, 0}, {1, -1, 1, -1, 0}, {1, 0, -1, -1, 0}, {-1, 0, 1, 1, -1}, {-1, 1, -1, 1, -1}, {-1, 0, 1, -1, 0}, {-1, 1, -1, -1, 0}, {0, -1, 0, 1, -1}, {0, -1, 0, -1, 0}}, 2 => {{0, 0, 1, 1, 1}, {0, 1, -1, 1, 1}, {1, -1, 0, 1, 1}, {-1, 0, 0, 1, 1}, {0, 0, 1, -1, 2}, {0, 1, -1, -1, 2}, {1, -1, 0, -1, 2}, {-1, 0, 0, -1, 2}, {0, 0, 1, 2, -1}, {0, 1, -1, 2, -1}, {1, -1, 0, 2, -1}, {1, 1, 0, 0, 0}, {2, -1, 1, 0, 0}, {2, 0, -1, 0, 0}, {-1, 2, 0, 0, 0}, {0, 0, 1, 0, 0}, {0, 0, 1, 0, 0}, {0, 1, -1, 0, 0}, {0, 1, -1, 0, 0}, {0, 0, 1, 0, 0}, {1, -2, 2, 0, 0}, {1, -1, 0, 0, 0}, {1, -1, 0, 0, 0}, {0, 0, 1, -2, 1}, {0, 1, -1, 0, 0}, {1, -1, 0, 0, 0}, {1, 0, -2, 0, 0}, {0, 1, -1, -2, 1}, {1, -1, 0, -2, 1}, {-1, 0, 0, 2, -1}, {0, 0, 1, 0, 0}, {0, 1, -1, 0, 0}, {-2, 1, 1, 0, 0}, {-2, 2, -1, 0, 0}, {-1, -1, 2, 0, 0}, {-1, 0, 0, 0, 0}, {-1, 0, 0, 0, 0}, {-1, 0, 0, 0, 0}, {-1, 1, -2, 0, 0}, {-1, 0, 0, -2, 1}, {0, 0, 1, 1, -2}, {0, 1, -1, 1, -2}, {0, 0, 1, -1, -1}, {0, 1, -1, -1, -1}, {1, -1, 0, 0, 0}, {-1, 0, 0, 0, 0}, {0, -2, 1, 0, 0}, {0, -1, -1, 0, 0}, {1, -1, 0, 1, -2}, {1, -1, 0, -1, -1}, {-1, 0, 0, 1, -2}, {-1, 0, 0, -1, -1}}, 3 => {{0, 0, 0, 2, 1}, {0, 0, 0, 0, 2}, {0, 0, 0, -2, 3}, {0, 0, 0, 3, -1}, {1, 0, 1, 1, 0}, {1, 1, -1, 1, 0}, {2, -1, 0, 1, 0}, {-1, 1, 1, 1, 0}, {-1, 2, -1, 1, 0}, {0, 0, 0, 1, 0}, {1, 0, 1, -1, 1}, {1, 1, -1, -1, 1}, {0, -1, 2, 1, 0}, {0, 0, 0, 1, 0}, {0, 0, 0, 1, 0}, {1, -2, 1, 1, 0}, {2, -1, 0, -1, 1}, {0, -1, 2, -1, 1}, {0, 0, 0, -1, 1}, {0, 0, 0, 1, 0}, {0, 1, -2, 1, 0}, {1, -1, -1, 1, 0}, {0, 0, 0, -1, 1}, {0, 1, -2, -1, 1}, {0, 0, 0, -1, 1}, {1, -1, -1, -1, 1}, {0, 0, 0, -3, 2}, {0, 0, 0, 1, 0}, {-2, 1, 0, 1, 0}, {-1, 1, 1, -1, 1}, {-1, 2, -1, -1, 1}, {-1, -1, 1, 1, 0}, {0, 0, 0, -1, 1}, {-2, 1, 0, -1, 1}, {-1, 0, -1, 1, 0}, {-1, 0, -1, -1, 1}, {0, 0, 0, 2, -2}, {1, 0, 1, 0, -1}, {1, 1, -1, 0, -1}, {-1, 1, 1, 0, -1}, {-1, 2, -1, 0, -1}, {0, -1, 2, 0, -1}, {0, 0, 0, 0, -1}, {0, 0, 0, 0, -1}, {0, 0, 0, 0, -1}, {0, 1, -2, 0, -1}, {0, 0, 0, -2, 0}, {0, 0, 0, -1, 1}, {1, -2, 1, -1, 1}, {-1, -1, 1, -1, 1}, {2, -1, 0, 0, -1}, {0, 0, 0, 0, -1}, {1, -2, 1, 0, -1}, {1, -1, -1, 0, -1}, {0, 0, 0, 0, -1}, {-2, 1, 0, 0, -1}, {-1, -1, 1, 0, -1}, {-1, 0, -1, 0, -1}, {0, 0, 0, 1, -3}, {0, 0, 0, -1, -2}}, 4 => {{1, 0, 0, 2, 0}, {-1, 1, 0, 2, 0}, {0, -1, 1, 2, 0}, {1, 0, 0, 0, 1}, {1, 0, 0, -2, 2}, {0, 0, -1, 2, 0}, {0, -1, 1, 0, 1}, {0, 0, -1, 0, 1}, {0, 0, -1, -2, 2}, {-1, 1, 0, 0, 1}, {-1, 1, 0, -2, 2}, {1, 0, 0, 1, -1}, {-1, 1, 0, 1, -1}, {0, -1, 1, 1, -1}, {0, 0, -1, 1, -1}, {0, 0, -1, -1, 0}, {0, -1, 1, -2, 2}, {1, 0, 0, -1, 0}, {-1, 1, 0, -1, 0}, {0, -1, 1, -1, 0}, {1, 0, 0, 0, -2}, {-1, 1, 0, 0, -2}, {0, -1, 1, 0, -2}, {0, 0, -1, 0, -2}, {0, 0, 2, 0, 0}, {0, 1, 0, 0, 0}, {0, 2, -2, 0, 0}, {1, -1, 1, 0, 0}, {1, 0, -1, 0, 0}, {2, -2, 0, 0, 0}, {-1, 0, 1, 0, 0}, {-1, 1, -1, 0, 0}, {0, -1, 0, 0, 0}, {-2, 0, 0, 0, 0}}, 5 => {{0, 0, 1, 1, 0}, {0, 1, -1, 1, 0}, {0, 0, 1, -1, 1}, {0, 1, -1, -1, 1}, {1, -1, 0, 1, 0}, {1, -1, 0, -1, 1}, {-1, 0, 0, 1, 0}, {-1, 0, 0, -1, 1}, {0, 0, 1, 0, -1}, {0, 1, -1, 0, -1}, {1, -1, 0, 0, -1}, {-1, 0, 0, 0, -1}}, 6 => {{0, 0, 0, 0, 1}, {0, 0, 0, 1, -1}, {0, 0, 0, -1, 0}}};
     assert(W === propagate(RI,3))
///
     
end

--old documentation
beginDocumentation()
doc ///
     Key
     	  EquivariantResolutions
     Headline
     	  study resolutions with a semisimple Lie group action
     Description
     	  Text
     	       This package helps studying the representation
	       theoretic structure of equivariant free resolutions
	       with an action of a semisimple Lie group.
///

doc ///
     Key
     	  setLieWeights
	  (setLieWeights,PolynomialRing,List)
     Headline
     	  attach (Lie theoretic) weights to the variables of a ring
     Usage
     	  setLieWeights(R,L)
     Inputs
     	  R:PolynomialRing
	  L:List
	       a table of weights given as lists of integers
     Outputs
     	  M:Matrix
	       whose rows are the weights of the variables of @TT "R"@
     Consequences
     	  Item
	       A key is created in the hashTable of @TT "R"@ whose value is the matrix @TT "M"@.
     Description
     	  Text
	       Assume @TT "R"@ is the symmetric algebra of a representation $V$ of a semisimple Lie group.
	       Assume, in addition, that each variable of @TT "R"@ is a weight vector in $V$.
	       This function lets the user assign a (Lie theoretic) weight to each variable of @TT "R"@,
	       allowing Macaulay2 to return the weight of monomials of @TT "R"@ upon request.
	  --Code
	  --Pre
	  --Example
     --Subnodes
     --Caveat
     --SeeAlso
     
///

doc ///
     Key
     	  ToTarget
     Headline
     	  optional argument for propagate
     Description
     	  Text
	       Use this argument to specify whether weights should be propagated from the codomain to the domain of a free module map or viceversa.
     SeeAlso
     	  propagate
///

doc ///
     Key
     	  [propagate,ToTarget]
     Headline
     	  optional argument for propagate
     Description
     	  Text
     	       Use this argument to specify whether weights should be propagated from the codomain to the domain of a free module map or viceversa.
     SeeAlso
     	  propagate
///

doc ///
     Key
     	  propagate
     Headline
     	  propagate (Lie theoretic) weights along equivariant maps and resolutions
     Description
     	  Text
	       This method can be used to propagate (Lie theoretic) weights along maps of free modules or free resolutions
	       over polynomial rings, which are symmetric algebras over representations of semisimple Lie groups.
	       The weights of the variables in the ring must be set a priori (see @TO "setLieWeights"@).
     SeeAlso
     	  setLieWeights
     
///

doc ///
     Key
     	  (propagate,Matrix,List)
     Headline
     	  propagate (Lie theoretic) weights along an equivariant map of free modules
     Usage
     	  W = propagate(M,L)
     Inputs
     	  M:Matrix
	       of an equivariant map
	  L:List
	       a table of weights for the codomain (resp. domain) of @TT "M"@ given as lists of integers
     Outputs
     	  W:List
	       a table of weights for the domain (resp. codomain) of @TT "M"@ given as lists of integers
     Description
     	  Text
	       In its default behavior, this function will use the weights of the variables in the ring of @TT "M"@
	       together with the weights of the codomain of @TT "M"@ to obtain the weights of the domain of @TT "M"@.
	       To obtain the weights of the codomain from the weights of the domain, use the optional argument
	       @TT "ToTarget=>false"@.
     SeeAlso
     	  setLieWeights
     
///

end

doc ///
     Key
     Headline
     Usage
     Inputs
     Outputs
     --Consequences
     	  --Item
     Description
     	  Text
	  --Code
	  --Pre
	  --Example
     --Subnodes
     --Caveat
     --SeeAlso
     
///