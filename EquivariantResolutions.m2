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
--creates a key "LieWeights" within the ring with value a matrix whose rows are
--weights of the ring variables
--a matrix is created here because it makes computing weights of ring elements
--easier
setLieWeights (PolynomialRing, List) := Matrix => (R,L) -> (
     if not isTable(L) then (
	  error "expected all weights to have the same length";
	  );
     for w in L do (
	  for i in w do (
	       if not instance(i,ZZ) then (
		    error "expected weights to be integers";
		    );
	       );
	  );
     if numgens(R)!=#L then (
	  error ("expected as many weights as generators of ",toString(R));
	  );
     R#LieWeights = matrix L
     )

--creates a key "LieWeights" in the module cache with value a list of weights
--for the free module generators
setLieWeights (Module, List) := List => (M,L) -> (
     if not isFreeModule(M) then error "expected a free module";
     if not isTable(L) then (
	  error "expected all weights to have the same length";
	  );
     for w in L do (
	  for i in w do (
	       if not instance(i,ZZ) then (
		    error "expected weights to be integers";
		    );
	       );
	  );
     if numgens(M)!=#L then (
	  error ("expected as many weights as generators of ",toString(M));
	  );
     M.cache#LieWeights = L
     )

--return the weight of a ring element or the generators of a module
getLieWeights = method(TypicalValue => List)
--weight of ring element (really of its leading monomial)
getLieWeights (RingElement) := List => r -> (
     R := ring r;
     if not R#?LieWeights then (
	  error "weights of the variables not assigned";
	  );
     if r==0 then error "the weight of the zero element is undefined";
     m := matrix exponents leadMonomial r;
     w := m*(R.LieWeights);
     return flatten entries w;
     )

--weights of a module
getLieWeights (Module) := List => M -> (
     if not M.cache#?LieWeights then (
	  error "weights of the module not assigned";
	  );
     return M.cache.LieWeights;
     )

--propagate weights along maps and resolutions
propagate = method(Options => {ToTarget => false})
--propagate weights along a map of free modules
--the default option ToTarget=>false propagates weights from codomain to domain
--turn it to true to go in the other direction
propagate (Matrix) := List => o -> M -> (
     if not isHomogeneous(M) then error "expected a homogeneous map";
     --the following checks if M is minimal (no constant non zero entries)
     --it compares degrees of generators of source and target
     --if it finds generators in the same degree it assumes the map is not minimal
     if #(set(degrees source M)*set(degrees target M))!=0 then (
	  error "expected a minimal map";
	  );
     if o.ToTarget == false then (
	  W := getLieWeights(target M);
	  p := for j to numColumns(M)-1 list position(flatten entries M_j, z -> z != 0);
	  q := for j to #p-1 list (W_(p_j) + getLieWeights(M_(p_j,j)));
	  return setLieWeights(source M,q);
	  )
     else (
	  W = getLieWeights(source M);
	  p = for j to numRows(M)-1 list position(flatten entries M^{j}, z -> z != 0);
	  q = for j to #p-1 list (W_(p_j) - getLieWeights(M_(j,p_j)));
	  return setLieWeights(target M,q)
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
     Headline
     	  attach (Lie theoretic) weights to a ring or module
     Description
     	  Text
	       Use this method to assign weights to the variables of a polynomial
	       ring or to a free module.
     SeeAlso
     	  getLieWeights
///

doc ///
     Key
	  (setLieWeights,PolynomialRing,List)
     Headline
     	  attach (Lie theoretic) weights to the variables of a ring
     Usage
     	  M = setLieWeights(R,L)
     Inputs
     	  R:PolynomialRing
	  L:List
	       a table of weights given as lists of integers
     Outputs
     	  M:Matrix
	       whose rows are the weights of the variables of @TT "R"@
     Consequences
     	  Item
	       The key @TT "LieWeights"@ is created in the hashTable of @TT "R"@
	       with value the matrix @TT "M"@.
     Description
     	  Text
	       Assume @TT "R"@ is the symmetric algebra of a representation $V$ of a
	       semisimple Lie group. Assume, in addition, that each variable of
	       @TT "R"@ is a weight vector in $V$. This function lets the user assign
	       a weight to each variable of @TT "R"@, allowing Macaulay2
	       to return the weight of monomials of @TT "R"@ upon request.
     
///

doc ///
     Key
	  (setLieWeights,Module,List)
     Headline
     	  attach (Lie theoretic) weights to a free module
     Usage
     	  W = setLieWeights(M,L)
     Inputs
     	  M:Module
	  L:List
	       a table of weights given as lists of integers
     Outputs
     	  W:List
	       containing the weights of @TT "M"@
     Consequences
     	  Item
	       The key @TT "LieWeights"@ is created in the hashTable @TT "M.cache"@
	       with value the list @TT "W"@.
     Description
     	  Text
	       Assume @TT "M"@ is a free module over a polynomial ring $A$, which is
	       the symmetric algebra of a representation of a semisimple Lie group $G$.
	       Assume, in addition, that @TT "M"@ is of the form $U\otimes A(-d)$,
	       where $U$ is also a representation of $G$. Then @TT "M"@ has an
	       $A$-basis of weight vectors for the $G$-action. This function lets the
	       user assign a weight to each generator of @TT "M"@.
     
///

doc ///
     Key
     	  getLieWeights
     Headline
     	  retrieve the (Lie theoretic) weights of a ring element or module
     Description
     	  Text
	       Use this method to obtain the weight of a monomial or the list of
	       weights previously assigned to a module.
     SeeAlso
     	  setLieWeights
	  propagate
     
///

doc ///
     Key
     	  (getLieWeights,RingElement)
     Headline
     	  retrieve the (Lie theoretic) weight of a monomial
     Usage
     	  w = getLieWeights(r)
     Inputs
     	  r:RingElement
     Outputs
     	  w:List
     Description
     	  Text
	       Obtains the weight of a monomial @TT "r"@ from the weights of the
	       variables in the ring of @TT "r"@. If @TT "r"@ is a polynomial,
	       then the weight of the leading monomial is returned (which may differ
	       from the weight of the other monomials).
     Caveat
     	  The weight of 0 is undefined so an error is returned if @TT "r"@ is 0.
     SeeAlso
     	  setLieWeights
     
///

doc ///
     Key
     	  (getLieWeights,Module)
     Headline
     	  retrieve the (Lie theoretic) weights of a module
     Usage
     	  w = getLieWeights(r)
     Inputs
     	  M:Module
     Outputs
     	  W:List
     Description
     	  Text
	       Simply returns the list of weights previously stored in @TT "M.cache"@.
     SeeAlso
     	  setLieWeights
	  propagate
///

doc ///
     Key
     	  ToTarget
     Headline
     	  optional argument for propagate
     Description
     	  Text
	       Use this argument to specify whether weights should be propagated
	       from the codomain to the domain of a free module map or viceversa.
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
     	       Use this argument to specify whether weights should be propagated
	       from the codomain to the domain of a free module map or viceversa.
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
	       This method can be used to propagate (Lie theoretic) weights along maps
	       of free modules or free resolutions over polynomial rings, which are
	       symmetric algebras over representations of semisimple Lie groups.
	       The weights of the variables in the ring must be set a priori.
     SeeAlso
     	  setLieWeights
///

doc ///
     Key
     	  (propagate,Matrix)
     Headline
     	  propagate (Lie theoretic) weights along an equivariant map of free modules
     Usage
     	  W = propagate(M)
     Inputs
     	  M:Matrix
	       of an equivariant map
	  ToTarget=>Boolean
	       propagate weights to domain (when false) or codomain (when true)
     Outputs
     	  W:List
	       a table of weights for the domain (resp. codomain) of @TT "M"@
     Description
     	  Text
	       In its default behavior, this function will use the weights of the
	       variables in the ring of @TT "M"@ together with the weights of the
	       codomain of @TT "M"@ to obtain the weights of the domain of @TT "M"@.
	       To obtain the weights of the codomain from the weights of the domain,
	       use the optional argument @TT "ToTarget=>true"@.
     SeeAlso
     	  getLieWeights
     
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