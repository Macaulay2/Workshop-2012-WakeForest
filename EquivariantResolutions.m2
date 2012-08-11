newPackage(
     "EquivariantResolutions",
     Version => "0.2",
     Date => "August 10, 2012",
     Authors => {{Name => "Federico Galetto",
     	       Email => "galetto.federico@gmail.com",
	       HomePage => "http://www.math.neu.edu/~fgaletto/"}},
     Headline => "study free resolutions with a semisimple Lie group action",
     DebuggingMode => true
     )

needsPackage "SimpleDoc"
needsPackage "WeylGroups"

export {LieWeights,setLieWeights,getLieWeights,propagate,ToTarget}

--set (lie theoretic) weights of the variables a ring
setLieWeights = method(TypicalValue => Matrix)
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

--return the weight of a ring element
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

--propagate weights along maps and resolutions
propagate = method(Options => {ToTarget => false})
--propagate weights along a map of free modules
--the default option ToTarget=>false propagates weights from codomain to domain
--turn it to true to go in the other direction
propagate (Matrix,List) := List => o -> (M,L) -> (
     if not isHomogeneous(M) then error "expected a homogeneous map";
     --the following checks if M is minimal (no constant non zero entries)
     --it compares degrees of generators of source and target
     --if it finds generators in the same degree it assumes the map is not minimal
     if #(set(degrees source M)*set(degrees target M))!=0 then (
	  error "expected a minimal map";
	  );
     c := 1;
     if o.ToTarget == true then (
	  M = transpose M;
	  c = -1;
	  );
     p := for j to numColumns(M)-1 list position(flatten entries M_j, z -> z != 0);
     --I considered using p:=leadComponent(M) instead of the line above
     --but I think it has a bug
     for j to #p-1 list (L_(p_j) + c*getLieWeights(M_(p_j,j)))
     )

--propagates weights to the whole resolution starting from a given homological degree
propagate (ChainComplex, ZZ, List) := HashTable => o -> (C,i,L) -> (
     h := new MutableHashTable from {i => L};
     for j from i+1 when C_j!=0 do (
	  h#j = propagate(C.dd_j,h#(j-1));
	  );
     for j from 1 when C_(i-j)!=0 do (
	  h#(i-j) = propagate(C.dd_(i-j+1),h#(i-j+1),ToTarget=>true);
	  );
     return new HashTable from h;
     )

TEST ///
     A=QQ[x_(1,1)..x_(2,4)];
     RI=res minors(2,genericMatrix(A,4,2));
     setLieWeights(A,{{1,1,0,0},{1,-1,1,0},{1,0,-1,1},{1,0,0,-1},{-1,1,0,0},
	       {-1,-1,1,0},{-1,0,-1,1},{-1,0,0,-1}});
     L={{0,0,1,0},{0,1,-1,1},{0,1,0,-1},{0,-1,0,1},{0,-1,1,-1},{0,0,-1,0}};
     W=new HashTable from {
	  0 => {{0,0,0,0}},
	  1 => {{0,0,1,0},{0,1,-1,1},{0,1,0,-1},{0,-1,0,1},{0,-1,1,-1},{0,0,-1,0}},
	  2 => {{1,0,0,1},{1,0,1,-1},{1,1,-1,0},{1,-1,0,0},{-1,0,0,1},{-1,0,1,-1},
	       {-1,1,-1,0},{-1,-1,0,0}},
	  3 => {{2,0,0,0},{0,0,0,0},{-2,0,0,0}}
	  };
     assert(W === propagate(RI,1,L))
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
     	  LieWeights
     Headline
     	  stores the (Lie theoretic) weights of the variables of a ring
     Description
     	  Text
	       A key in the hash table of a ring which is used to store the
	       (Lie theoretic) weights of the variables of the ring. Set this
	       using the @TO "setLieWeights"@ command.
     SeeAlso
     	  setLieWeights
///

doc ///
     Key
     	  setLieWeights
     Headline
     	  attach (Lie theoretic) weights to the variables of a ring
     Description
     	  Text
	       Use this method to assign weights to the variables of a polynomial
	       ring.
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
     	  getLieWeights
     Headline
     	  retrieve the (Lie theoretic) weight of a monomial
     Description
     	  Text
	       In a polynomial ring where each variable is a weight vector for the
	       action of a semisimple Lie group, each monomial is also a weight
	       vector. Use this method to obtain the weight of a monomial.
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
	       Returns the weight of a monomial @TT "r"@, which is simply the sum
	       of the weights of the variables in the support of @TT "r"@ counted
	       with the multiplicity corresponding to their power. If @TT "r"@ is a
	       polynomial, then the weight of the leading monomial is returned
	       (which may differ from the weights of the other monomials of @TT "r"@).
     Caveat
     	  The weight of 0 is undefined, so an error is returned if @TT "r"@ is 0.
     SeeAlso
     	  setLieWeights
///

doc ///
     Key
     	  ToTarget
     Headline
     	  optional argument for propagate
     Description
     	  Text
	       Use this argument to specify whether weights should be propagated
	       from the codomain to the domain of a free module map (default
	       behavior) or viceversa (set @TT "ToTarget=>true"@).
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
	       from the codomain to the domain of a free module map (default
	       behavior) or viceversa (set @TT "ToTarget=>true"@).
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
	       Assume to be working over a polynomial ring which is the symmetric
	       algebra of a representation of a semisimple Lie group.
	       This method can be used to propagate (Lie theoretic) weights along
	       equivariant maps of free modules or equivariant free resolutions,
	       thus helping to understand the representation theoretic structure
	       of the modules involved.
	       The weights of the variables in the ring must be set a priori.
     SeeAlso
     	  setLieWeights
///

doc ///
     Key
     	  (propagate,Matrix,List)
     Headline
     	  propagate (Lie theoretic) weights along an equivariant map of free modules
     Usage
     	  W = propagate(M)
     Inputs
     	  M:Matrix
	       an equivariant minimal homogeneous map of free modules
	  L:List
	       a table of weights for the codomain (resp. domain) of @TT "M"@
	  ToTarget=>Boolean
	       propagate weights to domain (when false) or codomain (when true)
     Outputs
     	  W:List
	       a table of weights for the domain (resp. codomain) of @TT "M"@
     Description
     	  Text
	       In its default behavior, this function will use the weights of the
	       variables in the ring of @TT "M"@, together with the weights of the
	       codomain of @TT "M"@, to obtain the weights of the domain of @TT "M"@.
	       To obtain the weights of the codomain from the weights of the domain,
	       use the optional argument @TT "ToTarget=>true"@.
     Caveat
     	  This function does not check that @TT "M"@ is an equivariant map. When used
	  on a map that is not equivariant, this function will produce meaningless
	  results. Moreover, @TT "M"@ must be a minimal homogeneous map.
	  
	  Currently, this function assumes that @TT "M"@ has undergone a reduction
	  where different columns have different leading monomials, which is the case
	  for differentials obtained with the @TT "resolution"@ command. Complexes
	  obtained with @TT "koszul"@, @TT "eagonNorthcott"@, or assembled with
	  @TT "chainComplex"@, may or may not work depending on the input. This might
	  be fixed in a future version of this package.
///

doc ///
     Key
     	  (propagate,ChainComplex,ZZ,List)
     Headline
     	  propagate (Lie theoretic) weights along an equivariant free resolution
     Usage
     	  H = propagate(C,i,L)
     Inputs
     	  C:ChainComplex
	       an equivariant minimal homogeneous complex
	  i:ZZ
	       the homological degree of a non zero module of @TT "C"@
	  L:List
	       a table of weights for @TT "C_i"@
     Outputs
     	  H:HashTable
	       containing the weights of all non zero modules of @TT "C"@
     Description
     	  Text
	       This function uses the weights of the @TT "i"@-th module of @TT "C"@,
	       together with the weights of the variables in the ring of @TT "C"@,
	       to obtain the weights of all the other modules of @TT "C"@. The
	       results are stored in a hash table with keys the homological degrees
	       of the complex and values the weights of the corresponding modules.
     Caveat
     	  This function does not check that @TT "C"@ is an equivariant complex.
	  When used on a complex that is not equivariant, this function will produce
	  meaningless results.
	  
	  Currently this function is designed to work on free resolutions obtained
	  with the @TT "resolution"@ command. See the caveat at
	  @TO "propagate(Matrix,List)"@ for more information.
     SeeAlso
     	  (propagate,Matrix,List)
///

end

--A little version history:
--0.1: wrote a basic working version of the package! :-)
--0.2: completed documentation and tests

restart
installPackage "EquivariantResolutions"
viewHelp
