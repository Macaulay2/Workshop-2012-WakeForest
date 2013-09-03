beginDocumentation()

doc ///
  Key
    DGAlgebras
  Headline
    Data types and basic functions on differential graded (DG) Algebras.
  Description
    Text
      This package is used to define and manipulate DG algebras.
  Subnodes
    "Basic operations on DG Algebras"
    "The Koszul complex as a DG Algebra"
    "Basic operations on DG Algebra Maps"
    "Basic operations on DG Modules Maps"
///

doc ///
  Key
    "Basic operations on DG Algebras"
  Headline
    Outlines some basic operations on DG Algebras
  Description
    Text
      There are several ways to define a DGAlgebra.  One can start by defining one 'from scratch'.  One does
      this by specifying the ring over which the DGAlgebra is defined and the degrees of the generators.  The
      name of the generators of the DGAlgebra by default is $T_i$, but one may change this by specifying the
      optional (string) argument 'Variable'.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
      A = freeDGAlgebra(R,{{1,1},{1,1},{1,1},{1,1}})
    Text
      The command freeDGAlgebra only defines the underlying algebra of A, and not the differential.  To set the differential of A,
      one uses the command setDiff.
    Example
      setDiff(A, gens R)
    Text
      Note that the above is the (graded) Koszul complex on a set of generators of R.  A much easier way to define this is to use the
      function koszulComplexDGA.
    Example
      B = koszulComplexDGA(R, Variable=>"S")
    Text
      One can compute the homology algebra of a DGAlgebra using the homology (or HH) command.
    Example
      HB = HH B
      describe HB
      degrees HB
    Text
      Note that since R is a complete intersection, its Koszul homology algebra is an exterior algebra, which is a
      free graded commutative algebra.  Note that the internal degree is preserved in the computation of the homology algebra
      of B.
    Text
      One can also adjoin variables to kill cycles in homology.  The command killCycles looks for the first positive degree
      nonzero homology (say i), and adjoins variables in homological degree i+1 that differentiate to a minimal generating set of this homology, so that the
      resulting DGAlgebra now only has homology in degree greater than i (note of course this could introduce new homology in higher degrees).
      The command adjoinVariables allows finer control over this procedure.  See @ TO adjoinVariables @ for an example.
    Example
      HB.cache.cycles
      C = adjoinVariables(B,{first HB.cache.cycles})
      homologyAlgebra(C,GenDegreeLimit=>4,RelDegreeLimit=>4)
      C = killCycles(B)
      homologyAlgebra(C,GenDegreeLimit=>4,RelDegreeLimit=>4)
    Text
      Again, note that since R is a complete intersection, once we adjoin the variables in homological degree two to kill the cycles in degree one,
      we obtain a minimal DG Algebra resolution of the residue field of R.  Also, note that since C has generators in even degree, one must specify the
      optional arguments GenDegreeLimit and RelDegreeLimit to specify the max degree of the computation.  To do this, one uses the homologyAlgebra command
      rather than the HH command.
    Text
      This computation could have also been done with the command acyclicClosure.  The command acyclicClosure performs the command killCycles sequentially to ensure that the
      result has homology in higher and higher degrees, thereby computing (part of) a minimal DG Algebra resolution of the residue field.  acyclicClosure has an optional
      argument EndDegree that allows the user to specify the maximum homological degree with which to perform this adjunction of variables.  The default value of this is 3, since if there
      are any variables of degree 3 that need to be added, then each subsequent homological degree will require some variables to be adjoined (Halperin's rigidity theorem).
    Example
      D = acyclicClosure R
      R' = ZZ/101[x,y,z]/ideal{x^2,y^2,z^2,x*y*z}
      E = acyclicClosure(R',EndDegree=>5)
      tally degrees E.natural
    Text
      As you can see, since R' is not a complete intersection, the acyclic closure of E requires infinitely many variables; we display the degrees of the first 6 here.
      The tally that is displayed gives the deviations of the ring R.  One can compute the deviations directly from any minimal free resolution of the residue field
      of R', so that using the one provided by res coker vars R is faster.  To do this, use the command @ TO deviations @.
    Example
      deviations(R,DegreeLimit=>6)
      deviations(R',DegreeLimit=>6)
    Text
      As a brief warning, the command @ TO poincareN @ which is used in @ TO deviations @ uses the symbols S and T internally, and may cause problems accessing such rings with the user interface.
///

doc ///
  Key
    "The Koszul complex as a DG Algebra"
  Headline
    an example
  Description
    Text
      The Koszul complex on a sequence of elements $f_1,\dots,f_r$ is a complex of R-modules whose underlying graded R-module
      is the exterior algebra on R^r generated in homological degree one.  This algebra structure also respects the boundary map
      of the complex in the sense that it satisfies the Liebniz rule.  That is, $d(ab) = d(a)b + (-1)^{deg a}ad(b)$.  When one
      speaks of 'the' Koszul complex of a ring, one means the Koszul complex on a minimal set of generators of the maximal ideal of R.
    Example
--      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
--      KR = koszulComplexDGA R
    Text
      One can specify the name of the variable to easily handle multiple Koszul complexes at once.
    Example
--      S = ZZ/101[x,y,z]/ideal{x^3,y^3,z^3,x^2*y^2,y^2*z^2}
--     KS = koszulComplexDGA(S,Variable=>"U")
    Text
      To obtain the chain complex associated to the Koszul complex, one may use chainComplex.  One can also obtain this complex
      directly without using the DGAlgebras package by using the command @ TO koszul @.
    Example
--      cxKR = chainComplex KR
--      prune HH cxKR
    Text
      Since the Koszul complex is a DG algebra, its homology is itself an algebra.  One can obtain this algebra using the command
      homology, homologyAlgebra, or HH (all commands work).  This algebra structure can detect whether or not the ring is a complete
      intersection or Gorenstein.
    Example
--     HKR = HH KR
--     ideal HKR
--     R' = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3,a*c,a*d,b*c,b*d,a^2*b^2-c^2*d^2}
--     HKR' = HH koszulComplexDGA R'
--     numgens HKR'
--     ann ideal gens HKR'
    Text
      Note that since the socle of HKR' is one dimensional, HKR' has Poincare duality, and hence R' is Gorenstein.
    Text
      One can also consider the Koszul complex of an ideal, or a sequence of elements.
    Example
--      Q = ambient R
--      I = ideal {a^3,b^3,c^3,d^3}
--      KI = koszulComplexDGA I
--      HKI = HH KI
--      describe HKI
--      use Q
--      I' = I + ideal{a^2*b^2*c^2*d^2}
--      KI' = koszulComplexDGA I'
--      HKI' = HH KI'
--      describe HKI'
--      HKI'.cache.cycles
    Text
      Note that since I is a Q-regular sequence, the Koszul complex is acyclic, and that both homology algebras are algebras over the zeroth homology
      of the Koszul complex.
///

doc ///
  Key
    "Basic operations on DG Algebra Maps"
  Headline
    Outlines some basic operations on DGAlgebraMaps
  Description
    Text
      An algebra map between the underlying graded algebras that satisfies the Leibniz rule is a morphism of DG algebras.  Such objects
      are created using the DGAlgebraMap class.  As with DGAlgebras, one can define a DGAlgebraMap 'from scratch' using @ TO dgAlgebraMap @.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
      K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
      K2 = koszulComplexDGA(ideal {b,c},Variable=>"T")
      f = dgAlgebraMap(K2,K1,matrix{{0,T_1,T_2}})
    Text
      Once we define the DGAlgebraMap, it is a good idea to check to see if it indeed satisfies the Leibniz rule.  This can be checked by using
      isWellDefined.
    Example
      isWellDefined f
    Text
      Oops!  Let's try that again.
    Example
      g = dgAlgebraMap(K1,K2,matrix{{Y_2,Y_3}})
      isWellDefined g
    Text
      One can lift a ring homomorphism in degree zero to a map of DGAlgebras (up to a specified degree) using liftToDGMap.  This is helpful
      in some of the internal functions of the DGAlgebras package, such as computing the map induced on Tor algebras by a RingMap.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      S = R/ideal{a^2*b^2*c^2}
      f = map(S,R)
      A = acyclicClosure(R,EndDegree=>3)
      B = acyclicClosure(S,EndDegree=>3)
      phi = liftToDGMap(B,A,f)
    Text
      Once one has a DGAlgebraMap, one can also obtain the underlying map of complexes via toComplexMap.
    Example
      cmPhi = toComplexMap(phi,EndDegree=>3)
    Text
      There are also some auxiliary commands associated with DGAlgebraMaps
    Example
      source phi
      target phi
    Text
      One can also obtain the map on homology induced by a DGAlgebra map.
    Example
      HHg = HH g
      matrix HHg
///


doc ///
  Key
    "Basic operations on DG Modules Maps"
  Headline
    Outlines some basic operations on DGModuleMaps
  Description
    Text
      A module map between the underlying graded modules that satisfies the Leibniz rule and is graded linear over the base @ TO DGAlgebra @  
      is a morphism of DG modules.  Such objects are created using the DGModuleMap class.  As with DGModules, one can define a DGModuleMap 'from scratch' using @ TO dgAlgebraMap @.
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(Q/I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
      V = semifreeDGModule(K,{{0,0},{1,1},{2,3}})
      setDiff(V,sub(matrix{{0,x,-T_1},{0,0,x^2},{0,0,0}}, K.natural))
      f = dgModuleMap(V,U,sub(matrix{{1,0,0},{0,x,0},{0,0,1}},K.natural))
    Text
      Once we define the DGModuleMap, it is a good idea to check to see if it indeed satisfies the Leibniz rule.  This can be checked by using
      isWellDefined.
    Example
     isWellDefined f
    Text
      Once one has a DGAlgebraMap, one can also obtain the underlying map of complexes via toComplexMap.
    Example
     -- cmf = toComplexMap(phi,EndDegree=>3)
    Text
      There are also some auxiliary commands associated with DGModuleMaps
    Example
     -- source phi
     -- target phi
    Text
      One can also obtain the map on homology induced by a DGModule map.
    Example
     -- HHg = HH g
     -- matrix HHg
///

doc ///
  Key
    DGAlgebra
  Headline
    The class of all DG Algebras
  Description
    Text
      A @ TO DGAlgebra @ A is represented as a  MutableHashTable  with three entries: A.ring is the coefficient ring, A.natural is the underlying algebra and A.diff is the differential. 
    
    Text
      Some common ways to create DGAlgebras include @ TO koszulComplexDGA @, @ TO freeDGAlgebra @, @ TO setDiff @, and @ TO acyclicClosure @.
    
    Example
      R = ZZ/101[a,b,c]
      A = koszulComplexDGA(R)
      A.ring
      A.natural
      A.diff   
  SeeAlso
    "Basic operations on DG Algebras"
///

doc ///
  Key
    DGModule
  Headline
    The class of all DG Modules
  Description
    Text
      A @ TO DGModule @ U is represented as a  MutableHashTable  with three entries: U.ring is the @ TO DGAlgebra @ that U is a module over, U.natural is the underlying @TO Module @  and U.diff is the differential. 
    
    Text
      Some common ways to create DGAlgebras include @ TO semifreeDGModule @, @ TO setDiff @, and @ TO acyclicClosure @.
    
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(I)
      M = coker matrix {{x^2}}
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
      degrees U.natural
      use K.natural
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
      U.diff
      chainComplex U
  Caveat
      So far only semifree DGModules can be constructed.
///   
      
      
      

doc ///
  Key
    freeDGAlgebra
    (freeDGAlgebra,Ring,List)
    [freeDGAlgebra,Variable]
  Headline
    Constructs a DGAlgebra
  Usage
    A = freeDGAlgebra(R,degreeList) 
  Inputs
    R:Ring 
      The ring over which the DGAlgebra is defined
    degreeList:List 
      A list of degrees of the algebra generators of R.
  Outputs
    A:DGAlgebra
  Description
    Text
      This function returns a @ TO DGAlgebra @ A whose underlying algebra is a graded commutative
      polynomial ring in a number of variables equal to the number of the degrees input.  The current version of this package
      does not handle algebras A whose underlying algebra is not a polynomial ring.
    Example
      R = ZZ/101[x,y,z]
      A = freeDGAlgebra(R,{{1},{1},{1},{3}})
      A.natural
      setDiff(A,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
    Text
      The resulting @ TO DGAlgebra @ will not be graded since the differential given does not respect the grading due to the degrees assigned in the definition.
    Example
      isHomogeneous(A)
      Add = chainComplex A
      B = freeDGAlgebra(R,{{1,1},{1,1},{1,1},{3,3}})
      B.natural
      setDiff(B,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
    Text
      The result of the above declaration will be graded.
    Example
      isHomogeneous(B)
      Bdd = chainComplex B
    Text  
      Note that the differential is not passed into the constructor.  The reason for this (at the moment)
      is that Macaulay2 does not know what ring the differentials are defined over until after the underlying
      algebra is constructed, so the differential is set later with setDiff.  Many DG algebras that one
      encounters in commutative algebra have been implemented, however, and do not need to be defined 'by hand'.
      For example, if one wants to work with the Koszul complex as a DG algebra, then one should see the command @ TO koszulComplexDGA @.
      Also, if one wishes to specify the name of the variables used, specify the Variable option; see the example in @ TO dgAlgebraMap @.
  Caveat
    There is currently a bug handling DG algebras that have no monomials in some degree, but some monomials in a later degree;
    for example if one replaces the 3 in the above example with a 5.
///

doc ///
  Key
    semifreeDGModule 
    (semifreeDGModule,DGAlgebra,List)
  Headline
    Constructs a DG Module
  Usage
    U = semifreeDGModule(A, degList)  
  Inputs
    A:DGAlgebra
      The DG Algebra over which the DG module will be defined.
    degList:List
      A list of the degrees of the generators of new DG module.
  Outputs
    U:DGModule
  Description
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
    Text
      However, this process does not define the differential, 
      which may be done using @ TO (setDiff,DGModule,Matrix)@.
///

doc ///
  Key
    koszulComplexDGA
    (koszulComplexDGA,Ring)
    [koszulComplexDGA,Variable]
  Headline
    Returns the Koszul complex as a DGAlgebra
  Usage
    A = koszulComplexDGA(R)
  Inputs
    R:Ring 
      Returns the Koszul complex on ideal vars R.
  Outputs
    A:DGAlgebra
  Description
    Text
      To construct the Koszul complex of a minimal set of generators as a @ TO DGAlgebra @ one uses
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      A = koszulComplexDGA(R)
      complexA = chainComplex A
      complexA.dd
      ranks = apply(4, i -> numgens prune HH_i(complexA))
      ranks == apply(4, i -> numgens prune HH_i(koszul vars R))
    Text
      One can also compute the homology of A directly with @ TO (homology,ZZ,DGAlgebra) @.  One may also specify
      the name of the variable using the Variable option.
///

doc ///
  Key
    (koszulComplexDGA,Ideal)
  Headline
    Returns the Koszul complex as a DGAlgebra
  Usage
    A = koszulComplexDGA(I)
  Inputs
    I:Ideal 
      An ideal of a ring R
  Outputs
    A:DGAlgebra
  Description
    Text
      To construct the Koszul complex on the set of generators of I as a @ TO DGAlgebra @ one uses
    Example
      R = ZZ/101[a,b,c]
      I = ideal{a^3,b^3,c^3,a^2*b^2*c^2}
      A = koszulComplexDGA(I)
      complexA = chainComplex A
      complexA.dd
      ranks = apply(4, i -> numgens prune HH_i(complexA))
      ranks == apply(4, i -> numgens prune HH_i(koszul gens I))
    Text
      One can also compute the homology of A directly with @ TO (homology,ZZ,DGAlgebra) @.
///

doc ///
  Key
    (koszulComplexDGA,List)
  Headline
    Define the Koszul complex on a list of elements as a DGAlgebra
  Usage
    A = koszulComplexDGA(diffList)
  Inputs
    diffList:List
      A List of RingElements.  The resulting DGAlgebra will be defined over the ring of these elements.
  Outputs
    A:DGAlgebra
///

doc ///
  Key
    (homology,ZZ,DGAlgebra)
  Headline
    Computes the homology of a DG algebra as a module
  Usage
    H = homology(n,A)
  Inputs
    n:ZZ
    A:DGAlgebra 
  Outputs
    H:Module
      The nth homology of A.
  Description
    Example
      R = ZZ/32003[x,y,z]
      A = koszulComplexDGA(R)
      apply(numgens R+1, i -> numgens prune homology(i,A))
///

doc ///
  Key
    setDiff
    InitializeComplex
    [setDiff,InitializeComplex]
    InitializeDegreeZeroHomology
    [setDiff,InitializeDegreeZeroHomology]
  Headline
    Set the differential of a DG object manually.
///

doc ///
  Key
    (setDiff,DGAlgebra,List)
  Headline
    Sets the differential of a DGAlgebra manually.
  Usage
    d = setDiff(A,diffList)
  Inputs
    A:DGAlgebra
    diffList:List 
  Outputs
    A:DGAlgebra
      The DGAlgebra with the differential now set.
  Description
    Example
      R = ZZ/101[x,y,z]
      A = freeDGAlgebra(R,{{1},{1},{1},{3}})
      setDiff(A,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
      Add = chainComplex A
      Add.dd
    Text
      There are two options that are available for this function, and both are designed to bypass certain initializations
      that take place by default.
    Text
      The option InitializeComplex specifies whether or not to compute all differentials of
      the complex(up to the sum of the degrees of the odd degree generators) before returning from setDiff.  This is useful if
      your DGAlgebra has a large number of generators in odd degrees, and you are only interested in computing the homology
      in low degrees.  The default value of this option is true.
    Text
      The option InitializeDegreeZeroHomology specifies whether or not to define the quotient ring H_0(A).  This is used when
      computing HH(A) as a DGAlgebra.  This involves computing a Grobner basis of the image of the first differential of A,
      and as such, may want to be avoided if there are a large number of DGAlgebra generators in degree 1.  The default value of
      this options is true.
///

doc ///
  Key
    (setDiff,DGModule,Matrix)
--    InitializeComplex
--    [setDiff,InitializeComplex]
--    InitializeDegreeZeroHomology
--    [setDiff,InitializeDegreeZeroHomology]
  Headline
    Sets the differential of a DG Module manually.
  Usage
    V = setDiff(U,M)
  Inputs
    U:DGModule
    M:Matrix 
  Outputs
    V:DGModule
      the DG module with the differential now set.
  Description
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(Q/I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
    Text
      We note that the DG module has no differential, and manually 
      set it using @TO (setDiff,DGModule,Matrix)@.
    Example
      U.diff
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
      U.diff
///

doc ///
  Key
    (isHomogeneous, DGAlgebra)
  Headline
    Determine if the DGAlgebra respects the gradings of the ring it is defined over.
  Usage
    isHom = isHomogeneous(A)
  Inputs
    A:DGAlgebra
  Outputs
    isHom:Boolean
      Whether or not the DGA respects the grading
  Description
    Example
      R = ZZ/101[x,y,z]
      A = freeDGAlgebra(R,{{1},{1},{1},{3}})
      setDiff(A,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
      isHomogeneous A
      B = freeDGAlgebra(R,{{1,1},{1,1},{1,1},{3,3}})
      setDiff(B,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
      isHomogeneous B
///

doc ///
  Key
    natural
  Headline
    The underlying algebra of a DGAlgebra.
  Usage
    Anat = A.natural
  Description
    Example
      R = ZZ/101[a,b,c,d]
      A = koszulComplexDGA(R)
      A.natural
///

doc ///
  Key
    cycles
  Headline
    Cycles chosen when computing the homology algebra of a DGAlgebra
  Usage
    A.cycles
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^4,c^5,d^6}
      A = koszulComplexDGA(R)
      apply(maxDegree A + 1, i -> numgens prune homology(i,A))
      HA = homologyAlgebra(A)
      numgens HA
      HA.cache.cycles
    Text
///

doc ///
  Key
    getBasis
    (getBasis,ZZ,DGAlgebra)
  Headline
    Get a basis for a particular homological degree of a DG algebra.
  Usage
    M = getBasis(n,A)
  Inputs
    n:ZZ
    A:DGAlgebra
  Outputs
    M:Matrix
      The basis of the desired homological degree of the DG Algebra.
  Description
    Text
      This function is to allow for the retrieval of a basis of a particular homological degree of a @ TO DGAlgebra @
      when the underlying algebra A.natural is multigraded.  In the code, the homological grading is always the first
      integer in the degree tuple, and so this function returns a matrix consisting of all monomials in homological
      degree n.  
    Example
      R = ZZ/101[a..d, Degrees=>{1,1,1,2}]
      A =  koszulComplexDGA(R)
      getBasis(3,A)
///

doc ///
  Key
    (getBasis,ZZ,Ring)
  Headline
    Get a basis for a degree of a ring.
  Usage
    M = getBasis(n,R)
  Inputs
    n:ZZ
    R:Ring
  Outputs
    M:Matrix
      The basis of the desired degree
  Description
    Text
      This function was not meant for general use, but it fixes the first degree in the degree tuple
      of the ring R, and finds a basis of that 'slice' of the ring.  It does this by using a cached
      version of the ring that forgets all other degrees.  A Ring object in Macaulay2 will not have this
      cached ring by default, but the rings used internally in the DGAlgebras package will.
///

doc ///
  Key
    (chainComplex,DGAlgebra)
  Headline
    Converts a DGAlgebra to a ChainComplex
  Usage
    C = chainComplex A or C = chainComplex(A,LengthLimit=>n)
  Inputs
    A:DGAlgebra
  Outputs
    C:ChainComplex
      The DG algebra A as a ChainComplex
  Description
    Example
      R = ZZ/101[x_1..x_10]
      A = koszulComplexDGA(R)
      C = chainComplex A
    Text
      Warning:  The term order that the internal command koszul uses to order the monomials is not GRevLex, and so the differentials
      used in koszul and koszulComplexDGA will not match up exactly.  Also, this command will only execute if all of the variables
      of the @ TO DGAlgebra @ A are of odd homological degree.  Otherwise, you need to use the function @ TO [(chainComplex, DGAlgebra), LengthLimit] @.
///

doc ///
  Key
    [(chainComplex,DGAlgebra),LengthLimit]
  Headline
    Converts a DGAlgebra to a ChainComplex
  Usage
    C = chainComplex A or C = chainComplex(A,LengthLimit=>n)
  Inputs
    A:DGAlgebra
    LengthLimit:ZZ
  Outputs
    C:ChainComplex
      The DG algebra A as a ChainComplex
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
      A = acyclicClosure(R,EndDegree=>3)
    Text
      The above will be a resolution of the residue field over R, since R is a complete intersection.
    Example
      C = chainComplex(A, LengthLimit=>10)
      apply(10, i -> prune HH_i(C))
///

doc ///
  Key
    acyclicClosure
    (acyclicClosure,DGAlgebra)
  Headline
    Compute theae acyclic closure of a DGAlgebra.
  Usage
    B = acyclicClosure(A)
  Inputs
    A:DGAlgebra
  Outputs
    B:DGAlgebra
      The acyclic closure of the DG Algebra A up to homological degree provided in the EndDegree option (default value is 3).
  Description
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      A = koszulComplexDGA(R);
      B = acyclicClosure(A,EndDegree=>3)
      chainComplex(B,LengthLimit=>8)
      B.diff
  SeeAlso
    (acyclicClosure,Ring)
///

doc ///
  Key
    (acyclicClosure,Ring)
  Headline
    Compute the acyclic closure of the residue field of a ring up to a certain degree
  Usage
    A = acyclicClosure(R)
  Inputs
    R:Ring
  Outputs
    A:DGAlgebra
      The acyclic closure of the ring R up to homological degree provided in the EndDegree option (default value is 3).
  Description
    Text
      This package always chooses the Koszul complex on a generating set for the maximal ideal as a starting
      point, and then computes from there, using the function @ TO (acyclicClosure,DGAlgebra) @.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^4-d^3}
      A = acyclicClosure(R,EndDegree=>3)
      A.diff
///

doc ///
  Key
    (symbol **, DGAlgebra, Ring)
  Headline
    Tensor product of a DGAlgebra and another ring.
  Usage
    B = A ** S
  Inputs
    A:DGAlgebra
    R:Ring
  Outputs
    B:DGAlgebra
  Description
    Text
      Tensor product of a DGAlgebra and another ring (typically a quotient of A.ring).
    Example
      R = ZZ/101[a,b,c,d]
      A = koszulComplexDGA(R)
      S = R/ideal{a^3,a*b*c}
      B = A ** S
      Bdd = chainComplex B
      Bdd.dd
///

doc ///
  Key
    (symbol **, DGAlgebra, DGAlgebra)
  Headline
    Tensor product of a DGAlgebra and another ring.
  Usage
    C = A ** B
  Inputs
    A:DGAlgebra
    B:DGAlgebra
  Outputs
    C:DGAlgebra
  Description
    Text
      Tensor product of a pair of DGAlgebras.
    Example
      R = ZZ/101[a,b,c,d]
      A = koszulComplexDGA({a,b})
      B = koszulComplexDGA({c,d})
      C = A ** B
      Cdd = chainComplex C
      Cdd.dd
  Caveat
    Currently, the tensor product function does not create a block order on the variables from A and B.
///

doc ///
  Key
    (symbol *, DGModuleMap, DGModuleMap)
  Headline
    The composition of two DGModule maps.
  Usage
    h = g * f
  Inputs
    f:DGModuleMap
    g:DGModuleMap
  Outputs
    h:DGModuleMap
  Description
    Text
      text
///

doc ///
  Key
    (symbol *, DGAlgebraMap, DGAlgebraMap)
  Headline
     The composition of two DGAlgebra maps.
  Usage
    h = g * f
  Inputs
     f: DGAlgebraMap
     g: DGAlgebraMap
  Outputs
     h: DGAlgebraMap

///

doc ///
  Key
    (symbol ++, DGModule, DGModule)
  Headline
     The direct sum of two DGModules
  Usage
    W = U ++ V
  Inputs
       U: DGModule
       V: DGModule
  Outputs
     W: DGModule
///

doc ///
  Key
    killCycles
    (killCycles,DGAlgebra)
  Headline
    Adjoins variables to make non-bounding cycles boundaries in the lowest positive degree with nontrivial homology.
  Usage
    B = killCycles(A)
  Inputs
    A:DGAlgebra
  Outputs
    B:DGAlgebra
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3-d^4}
      A = koszulComplexDGA(R)
      A.diff
      B = killCycles(A)
      B.diff
///

doc ///
  Key
    adjoinVariables
    (adjoinVariables,DGAlgebra,List)
  Headline
    Adjoins variables to make the specified cycles boundaries.
  Usage
    B = adjoinVariables(A,cycleList)
  Inputs
    A:DGAlgebra
    cycleList:List
  Outputs
    B:DGAlgebra
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3-d^4}
      A = koszulComplexDGA(R)
      A.diff
      prune homology(1,A)
      B = adjoinVariables(A,{a^2*T_1})
      B.diff
      prune homology(1,B)
///

doc ///
  Key
    homologyAlgebra
    (homologyAlgebra,DGAlgebra)
  Headline
    Compute the homology algebra of a DGAlgebra.
  Usage
    HA = homologyAlgebra(A)
  Inputs
    A:DGAlgebra
  Outputs
    HA:Ring
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      A = koszulComplexDGA(R)
      apply(maxDegree A + 1, i -> numgens prune homology(i,A))
      HA = homologyAlgebra(A)
    Text
      Note that HA is a graded commutative polynomial ring (i.e. an exterior algebra) since R is a complete intersection.
    Example  
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4,a^3*b^3*c^3*d^3}
      A = koszulComplexDGA(R)
      apply(maxDegree A + 1, i -> numgens prune homology(i,A))
      HA = homologyAlgebra(A)
      numgens HA
      HA.cache.cycles
    Example
      Q = ZZ/101[x,y,z]
      I = ideal{y^3,z*x^2,y*(z^2+y*x),z^3+2*x*y*z,x*(z^2+y*x),z*y^2,x^3,z*(z^2+2*x*y)}
      R = Q/I
      A = koszulComplexDGA(R)
      apply(maxDegree A + 1, i -> numgens prune homology(i,A))
      HA = homologyAlgebra(A)
    Text
      One can check that HA has Poincare duality since R is Gorenstein.
    Text
      If your DGAlgebra has generators in even degrees, then one must specify the options GenDegreeLimit and RelDegreeLimit.
    Example
      R = ZZ/101[a,b,c,d]
      S = R/ideal{a^4,b^4,c^4,d^4}
      A = acyclicClosure(R,EndDegree=>3)
      B = A ** S
      HB = homologyAlgebra(B,GenDegreeLimit=>7,RelDegreeLimit=>14)
///

doc ///
  Key
    (homology,DGAlgebra)
  Headline
    Compute the homology algebra of a DGAlgebra.
  Usage
    HA = homology(A)
  Inputs
    A:DGAlgebra
  Outputs
    HA:Ring
  SeeAlso
    (homologyAlgebra,DGAlgebra)
///

doc ///
  Key
    torAlgebra
    (torAlgebra,Ring)
  Headline
    Computes the Tor algebra of a ring
  Usage
    torR = torAlgebra(R)
  Inputs
    R:Ring
  Outputs
    torR:Ring
  Description
    Example
      R = ZZ/101[a,b,c,d]
      TorR = torAlgebra(R)
      S = R/ideal{a^3,b^3,c^3,d^5}
      TorS = torAlgebra(S)
    Text
      The above example calculates the Tor algebra of R and S up to degree 3, by default.  One can also specify the maximum degree
      to compute generators of the Tor algebra by specifying the GenDegreeLimit option.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3,a^2*b^2*c^3*d^2}
      TorR = torAlgebra(R,GenDegreeLimit=>5)
///

doc ///
  Key
    (torAlgebra,Ring,Ring)
  Headline
    Computes Tor_R(S,k) up to a specified generating and relating degree.
  Usage
    TorRS = torAlgebra(R,S,GenDegreeLimit=>m,RelDegreeLimit=>n)
  Inputs
    R:Ring
    S:Ring
  Outputs
    TorRS:Ring
  Description
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      M = coker matrix {{a^3*b^3*c^3*d^3}};
      S = R/ideal{a^3*b^3*c^3*d^3}
      HB = torAlgebra(R,S,GenDegreeLimit=>4,RelDegreeLimit=>8)
      numgens HB
      apply(5,i -> #(flatten entries getBasis(i,HB)))      
      Mres = res(M, LengthLimit=>8)
    Text
      Note that in this example, $Tor_*^R(S,k)$ has trivial multiplication, since the
      map from R to S is a Golod homomorphism by a theorem of Levin and Avramov.
///

doc ///
  Key
    maxDegree
    (maxDegree,DGAlgebra)
  Headline
    Computes the maximum homological degree of a DGAlgebra
  Usage
    mDegree = maxDegree(A)
  Inputs
    A:DGAlgebra
  Outputs
    mDegree:ZZ
      The maximum degree of the DGAlgebra A (this can be infinite).
  Description
    Text
      Note that if the DGAlgebra A has any generators of even degree, then maxDegree returns infinity.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
      A = koszulComplexDGA(R)
      B = acyclicClosure(A,EndDegree=>3)
      maxDegree(A)
      maxDegree(B)
///

doc ///
  Key
    isHomologyAlgebraTrivial
    (isHomologyAlgebraTrivial,DGAlgebra)
  Headline
    Determines if the homology algebra of a DGAlgebra is trivial
  Usage
    isTriv = isHomologyAlgebraTrivial(A) 
  Inputs
    A:DGAlgebra
  Outputs
    isTriv:Boolean
  Description
    Text
      This function computes the homology algebra of the DGAlgebra A and determines if the multiplication on H(A) is trivial.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      S = R/ideal{a^3*b^3*c^3*d^3}
      A = acyclicClosure(R,EndDegree=>3)
      B = A ** S
      isHomologyAlgebraTrivial(B,GenDegreeLimit=>6)
    Text
      The command returns true since R --> S is Golod.  Notice we also used the option GenDegreeLimit here.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      A = koszulComplexDGA(R)
      isHomologyAlgebraTrivial(A)
    Text
      The command returns false, since R is Gorenstein, and so HA has Poincare Duality, hence the multiplication
      is far from trivial.
///

doc ///
  Key
    isAcyclic
    (isAcyclic,DGAlgebra)
  Headline
    Determines if a DGAlgebra is acyclic.
  Usage
    isAcyc = isAcyclic(A)
  Inputs
    A:DGAlgebra
  Outputs
    isAcyc:Boolean
  Description
    Text
      This function determines if the DGAlgebra is acyclic.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4+b^4+c^4+d^4}
      isAcyclic(koszulComplexDGA R)
    Example
      Q = ZZ/101[a,b,c,d]
      I = ideal {a^4,b^4,c^4,d^4}
      isAcyclic(koszulComplexDGA I)
///

doc ///
  Key
    isGolod
    (isGolod,Ring)
  Headline
    Determines if a ring is Golod
  Usage
    isGol = isGolod(R)
  Inputs
    R:Ring
  Outputs
    isGol:Boolean
  Description
    Text
      This function determines if the Koszul complex of a ring R admits a trivial Massey operation.  If one exists, then R is Golod.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4+b^4+c^4+d^4}
      isGolod(R)
    Text
      Hypersurfaces are Golod, but
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      isGolod(R)
    Text
      complete intersections of higher codimension are not.  Here is another example:
    Example
      Q = ZZ/101[a,b,c,d]
      R = Q/(ideal vars Q)^2
      isGolod(R)
    Text
      The above is a (CM) ring minimal of minimal multiplicity, hence Golod.
    Text
      Note that since the Koszul complex is zero in homological degree beyond the embedding dimension, there are only finitely
      many Massey products that one needs to check to verify that a ring is Golod.
///

doc ///
  Key
    isGolodHomomorphism
    (isGolodHomomorphism,QuotientRing)
  Headline
    Determines if the canonical map from the ambient ring is Golod
  Usage
    isGol = isGolodHomomorphism(R)
  Inputs
    R:QuotientRing
  Outputs
    isGol:Boolean
  Description
    Text
      This function determines if the canonical map from ambient R --> R is Golod.  It does this by computing an acyclic closure of
      ambient R (which is a @ TO DGAlgebra @), then tensors this with R, and determines if this DG Algebra has a trivial Massey operation
      up to a certain homological degree provided by the option GenDegreeLimit.
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^4+b^4+c^4+d^4}
      isGolodHomomorphism(R,GenDegreeLimit=>5)
    Text
      If R is a Golod ring, then ambient R $\rightarrow$ R is a Golod homomorphism. 
    Example
      Q = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
      R = Q/ideal (a^3*b^3*c^3*d^3)
      isGolodHomomorphism(R,GenDegreeLimit=>5,TMOLimit=>3)
    Text
      The map from Q to R is Golod by a result of Avramov and Levin; we can only find the trivial Massey operations out to a given degree.
///

doc ///
  Key
    getGenerators
    (getGenerators,DGAlgebra)
  Headline
    Returns a list of cycles whose images generate HH(A) as an algebra
  Usage
    cycleList = getGenerators(A)
  Inputs
    A:DGAlgebra
  Outputs
    cycleList:List
  Description
    Text
      This version of the function should only be used if all algebra generators of A are in odd homological degree,
      provided in the EndDegree option.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3,a^2*b^2*c^2}
      A = koszulComplexDGA(R)
      netList getGenerators(A)
///

doc ///
  Key
    deviations
    (deviations,Ring)
    (deviations,ChainComplex)
    (deviations,RingElement,List)
  Headline
    Computes the deviations of the input ring, complex, or power series.
  Usage
    devTally = deviations(R)
  Inputs
    R:Ring
  Outputs
    devTally:Tally
  Description
    Text
      This command computes the deviations of a @ TO Ring @, a @ TO ChainComplex @, or a power series in the form of a @ TO RingElement @.
      The deviations are the same as the degrees of the generators of the acyclic closure of R, or the degrees of the generators of the
      Tor algebra of R.  This function takes an option called Limit (default value 3) that specifies the largest deviation to compute.
    Example
      R = ZZ/101[a,b,c,d]/ideal {a^3,b^3,c^3,d^3}
      deviations(R)
      deviations(R,DegreeLimit=>4)
      S = R/ideal{a^2*b^2*c^2*d^2}
      deviations(S,DegreeLimit=>4)
      T = ZZ/101[a,b]/ideal {a^2-b^3}
      deviations(T,DegreeLimit=>4)
    Text
      Note that the deviations of T are not graded, since T is not graded.  When calling deviations on a ChainComplex, the
      zeroth free module must be cyclic, and this is checked.  The same goes for the case
      of a RingElement.
    Example
      R = ZZ/101[a,b,c,d]/ideal {a^3,b^3,c^3,d^3}
      A = degreesRing R
      kRes = res coker vars R
      pSeries = poincareN kRes
      devA = deviations(R,DegreeLimit=>5)
      devB = deviations(kRes,DegreeLimit=>5)
      devC = deviations(pSeries,degrees R, DegreeLimit=>5)
      devA === devB and devB === devC
///

doc ///
  Key
    deviationsToPoincare
    (deviationsToPoincare,HashTable)
    [deviationsToPoincare,DegreeLimit]
  Headline
    Computes the power series corresponding to a set of deviations.
  Usage
    pSeries = deviationsToPoincare(devHash)
  Inputs
    devHash:HashTable
      HashTable of the same form as the output from @ TO deviations @
  Outputs
    pSeries:RingElement
  Description
    Text
      This command takes a HashTable of the same form output from @ TO deviations @ and produces the Poincare series corresponding to it.
      The (key,value) pairs must be of the form homologicalDegree=>number or (homologicalDegree,internalDegree)=>number.
      Because 
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      RDevs = deviations(R,DegreeLimit=>6)
      devPSeries = deviationsToPoincare(RDevs,DegreeLimit=>6)
      pSeries = poincareN (res(coker vars R, LengthLimit=>6))
      substitute(devPSeries,ring pSeries) == pSeries
///

doc ///
  Key
    findTrivialMasseyOperation
    findNaryTrivialMasseyOperation
    (findTrivialMasseyOperation,DGAlgebra)
    (findNaryTrivialMasseyOperation,DGAlgebra,List,HashTable,ZZ)
  Headline
    Finds a trivial Massey operation on a set of generators of H(A)
  Usage
    tmo = findTrivialMasseyOperation(A)
  Inputs
    A:DGAlgebra
  Outputs
    tmo:HashTable
      A hash table with keys given by monomials in a generating set of the positive degree homology of A and values the element that bounds the Massey
      product corresponding to that monomial.
  Description
    Text
      This function the element that bounds all potentially nonzero Massey products (before taking homology class).
      The maximum degree of a generating cycle is specified in the option GenDegreeLimit, if needed.
    Text
      Golod rings are defined by being those rings whose Koszul complex K^R has a trivial Massey operation.
      Also, the existence of a trivial Massey operation on a DG algebra A forces the multiplication on H(A)
      to be trivial.  An example of a ring R such that H(K^R) has trivial multiplication, yet K^R does not admit
      a trivial Massey operation is unknown.  Such an example cannot be monomially defined, by a result of
      Jollenbeck and Berglund. 
    Text
      This is an example of a Golod ring.  It is Golod since it is the Stanley-Reisner ideal of a flag complex
      whose 1-skeleton is chordal [Jollenbeck-Berglund].
    Example
      Q = ZZ/101[x_1..x_6]
      I = ideal (x_3*x_5,x_4*x_5,x_1*x_6,x_3*x_6,x_4*x_6)
      R = Q/I
      A = koszulComplexDGA(R)
      isHomologyAlgebraTrivial(A,GenDegreeLimit=>3)
      cycleList = getGenerators(A)
      tmo = findTrivialMasseyOperation(A)
      assert(tmo =!= null)
    Text
      Below is an example of a Teter ring (Artinian Gorenstein ring modulo its socle), and the computation in Avramov and Levin's
      paper shows that H(A) does not have trivial multiplication, hence no trivial Massey operation can exist.
    Example
      Q = ZZ/101[x,y,z]
      I = ideal (x^3,y^3,z^3,x^2*y^2*z^2)
      R = Q/I
      A = koszulComplexDGA(R)
      isHomologyAlgebraTrivial(A)
      cycleList = getGenerators(A)
      assert(findTrivialMasseyOperation(A) === null)
    Text
      Below is an example of a complete intersection of codimension 2.
    Example
      restart
      loadPackage ("DGAlgebras", Reload=>true)
      Q = ZZ/101[a..f]
      I = ideal (a^2+b^2+c^2,d^2+e^2+f^2)
      R = Q/I
      A = koszulComplexDGA(R)
      findTrivialMasseyOperation(A)
    Text
      The related function @ TO findNaryTrivialMasseyOperation @ find only the nth order trivial Massey operations.
///

doc ///
  Key
    expandGeomSeries
    (expandGeomSeries,List,ZZ)
    (expandGeomSeries,RingElement,ZZ)
  Headline
    Expand a geometric series to a specified degree.
  Usage
    pSeries = expandGeomSeries(f,n)
  Inputs
    f:RingElement
      Ratio of the geometric series to be expanded.
    n:ZZ
      Degree which to expand the geometric series.
  Outputs
    pSeries:RingElement
      Power series representation of the geometric series.
  Description
    Text
      If the user supplies a list instead of a RingElement as the first argument, the return
      value is the product of all the each of the geometric series expanded to degree n obtained
      by calling expandGeomSeries on each element of the list.
    Example
      A = ZZ[S,T_0,T_1]
      f = expandGeomSeries(S^2*T_0^8,10)
      g = expandGeomSeries(S^4*T_1^15,10)
      h = expandGeomSeries({S^2*T_0^8,S^4*T_1^15},10)
      B = A/(first gens A)^11
      substitute(f*g,B) == h
///

doc ///
  Key
    torMap
    (torMap,RingMap)
    [torMap,GenDegreeLimit]
  Headline
    Compute the map of Tor algebras associated to a RingMap.
  Usage
    torPhi = torMap(phi)
  Inputs
    phi:RingMap
  Outputs
    torPhi:RingMap
  Description
    Text
      The functor Tor_R(M,N) is also functorial in the ring argument.  Therefore, a ring map phi from A to B induces an algebra map
      from the Tor algebra of A to the Tor algebra of B.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3,a^2*b^2*c^2}
      S = R/ideal{a*b^2*c^2,a^2*b*c^2,a^2*b^2*c}
      f = map(S,R)
      fTor = torMap(f,GenDegreeLimit=>3)
      matrix fTor
    Text
      In the following example, the map on Tor is surjective, which means that the ring homomorphism is large (Dress-Kramer).
    Example
      R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3,a*c,a*d,b*c,b*d}
      S = ZZ/101[a,b]/ideal{a^3,b^3}
      f = map(S,R,matrix{{a,b,0,0}})
      fTor = torMap(f,GenDegreeLimit=>4)
      matrix fTor      
///

doc ///
  Key
    ringMap
  Headline
    RingMap of a DGAlgebraMap in degree zero.
  Usage
    phi = phiLift.ringMap
  Inputs
    phiLift:DGAlgebraMap
  Outputs
    phi:RingMap
///

doc ///
  Key
    zerothHomology
    (zerothHomology,DGAlgebra)
  Headline
    Compute the zeroth homology of the DGAlgebra A as a ring.
  Usage
    HA0 = zerothHomology A
  Inputs
    A:DGAlgebra
  Outputs
    HA0:Ring
      HH_0(A) as a ring.
///

doc ///
  Key
    getDegNModule
    (getDegNModule,ZZ,Ring,Ring)
  Headline
    Compute a presentation of M_i as an R-module
  Usage
    M' = getDegNModule(N,R,M)
    M' = getDegNModule(N,R,A)
  Inputs
    N:ZZ
    R:Ring
    M:Module
      M is a Module over a ring A, and A must be a graded R-algebra with A_0 = R
    A:Ring
      A must be a graded R-algebra, and A_0 = R
  Outputs
    M':Module
      M_N as an R = A_0-module
///

doc ///
  Key
    DGAlgebraMap
  Headline
    The class of all DG Algebra maps
  Description
    Text
      A common way to create a DGAlgebraMap is via @ TO liftToDGMap @.
///
doc ///
  Key
    DGModuleMap
  Headline
    The class of all DG Module maps
--  Description
--    Text
--      A common way to create a DGAlgebraMap is via @ TO liftToDGMap @.
///

doc ///
  Key
    dgAlgebraMap
    (isWellDefined,DGAlgebraMap)
    (dgAlgebraMap,DGAlgebra,DGAlgebra,Matrix)
  Headline
    Define a DG algebra map between DG algebras.
  Usage
    phi = dgAlgebraMap(B,A,M)
  Inputs
    A:DGAlgebra
       Source
    B:DGAlgebra
       Target
    M:Matrix
       A matrix representing where the generators of A should be mapped to (akin to ringMap)
  Outputs
    phi:DGAlgebraMap
  Description
    Example
      R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
      K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
      K2 = koszulComplexDGA(ideal {b,c},Variable=>"T")
      g = dgAlgebraMap(K1,K2,matrix{{Y_2,Y_3}})
      isWellDefined g
    Text
      The function does not check that the DG algebra map is well defined, however.
    Example
      f = dgAlgebraMap(K2,K1,matrix{{0,T_1,T_2}})
      isWellDefined f
///

doc ///
  Key
    dgModuleMap
    (dgModuleMap,DGModule,DGModule,Matrix)
    (isWellDefined,DGModuleMap)
  Headline
    Define a DG module map between DG modules.
  Usage
    phi = dgModuleMap(B,A,M)
  Inputs
    A:DGModule
       Source
    B:DGModule
       Target
    M:Matrix
       A matrix representing where the generators of A should be mapped to (akin to ringMap)
  Outputs
    phi:DGModuleMap
  Description
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(Q/I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
      V = semifreeDGModule(K,{{0,0},{1,1},{2,3}})
      setDiff(V,sub(matrix{{0,x,-T_1},{0,0,x^2},{0,0,0}}, K.natural))
      f = dgModuleMap(V,U,sub(matrix{{1,0,0},{0,x,0},{0,0,1}},K.natural))
    Text
      We may also check that the DG module map is well defined.
    Example
      isWellDefined f
///

doc ///
  Key
    shift
  Headline
    Construct shift of a DG Module or DG Module map.
///

doc ///
  Key
    (shift, DGModule)
  Headline
    Construct a degree 1 shift of a DG Module.
  Usage
    V = shift U
  Inputs
    U:DGModule
  Outputs
    V:DGModule
  Description
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(Q/I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
    Text
      We compute the shifted module, noting that the differential has been adjusted appropriately. 
    Example
      V = shift U
      V.diff
    Text
      Along with the shifted DG Module V, we also obtain the bijection from U to V and its inverse:
    Example
     A  = V.cache.shiftMap
     B  = V.cache.inverseShiftMap
///

doc ///
  Key
    (shift,DGModuleMap)
  Headline
    Construct a degree 1 shift of a DG Module map.
  Usage
    g = shift f
  Inputs
    f:DGModuleMap
  Outputs
    g:DGModuleMap
  Description
    Text
      Given a DG Module map f from U to V, we obtain the induced map from shift U to shift V.
///
      
doc ///
  Key
    (cone,DGModuleMap)
  Headline
    Compute the mapping cone of a DG Module map.
  Usage
    C = cone f
  Inputs
    f: DGModuleMap
  Outputs
    C: DGModule
  Description
    Example
      Q = QQ[x]
      I = ideal(x^3)
      K = koszulComplexDGA(Q/I)
      U = semifreeDGModule(K,{{0,0},{1,2},{2,3}})
      setDiff(U,sub(matrix{{0,x^2,-T_1},{0,0,x},{0,0,0}}, K.natural))
--      V = semifreeDGModule(K,{{0,0},{1,1},{2,3}})
--      setDiff(V,sub(matrix{{0,x,-T_1},{0,0,x^2},{0,0,0}}, K.natural))
      f = dgModuleMap(U, U, id_(U.natural))
      C = cone f
      complexC = chainComplex C
      complexC.dd
      prune (HH complexC)
///      



doc ///
  Key
    toComplexMap
    (toComplexMap,DGAlgebraMap)
    (toComplexMap,DGAlgebraMap,ZZ)
    [toComplexMap,AssertWellDefined]
    [toComplexMap,EndDegree]
  Headline
    Construct the ChainComplexMap associated to a DGAlgebraMap
  Usage
    psi = toComplexMap phi
  Inputs
    phi:DGAlgebraMap
  Outputs
    psi:ChainComplexMap
  Description
    Example
       R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
       K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
       K2 = koszulComplexDGA(ideal {b,c},Variable=>"T")
       g = dgAlgebraMap(K1,K2,matrix{{Y_2,Y_3}})
       g' = toComplexMap g
    Text
      The option @ TO EndDegree @ must be specified if the source of phi has any algebra generators of even degree.  The option @ TO AssertWellDefined @
      is used if one wishes to assert that the result of this computation is indeed a chain map.  One can construct just the nth map in the
      chain map by providing the second @ TO ZZ @ parameter.
    Text
      This function also works when working over different rings, such as the case when the @ TO DGAlgebraMap @ is produced via
      @ TO liftToDGMap @ and in the next example.  In this case, the target module is produced via @ TO pushForward @.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      S = R/ideal{a^2*b^2*c^2}
      f = map(S,R)
      A = acyclicClosure(R,EndDegree=>3)
      B = acyclicClosure(S,EndDegree=>3)
      phi = liftToDGMap(B,A,f)
      toComplexMap(phi,EndDegree=>3)
///

doc ///
  Key
    liftToDGMap
    (liftToDGMap,DGAlgebra,DGAlgebra,RingMap)
    [liftToDGMap,EndDegree]
  Headline
    Lift a ring homomorphism in degree zero to a DG algebra morphism
  Usage
    phiTilde = liftToDGMap(B,A,phi)
  Inputs
    B:DGAlgebra
      Target
    A:DGAlgebra
      Source
    phi:RingMap
      Map from A in degree zero to B in degree zero
  Outputs
    phiTilde:DGAlgebraMap
      DGAlgebraMap lifting phi to a map of DGAlgebras.
  Description
    Text
      In order for phiTilde to be defined, phi of the image of the differential of A in degree 1 must lie in the image of the
      differential of B in degree 1.  At present, this condition is not checked.
    Example
      R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
      S = R/ideal{a^2*b^2*c^2}
      f = map(S,R)
      A = acyclicClosure(R,EndDegree=>3)
      B = acyclicClosure(S,EndDegree=>3)
      phi = liftToDGMap(B,A,f)
      toComplexMap(phi,EndDegree=>3)
///

doc ///
  Key
    (homology,DGAlgebraMap)
    (homology,DGAlgebraMap,ZZ)
  Headline
    Computes the homomorphism in homology associated to a DGAlgebraMap.
  Usage
    homologyPhi = homology(phi,n)
  Inputs
    phi:DGAlgebraMap
  Outputs
    homologyPhi:RingMap
      The map on homology defined by phi.
  Description
    Example
      R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
      K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
      K2 = koszulComplexDGA(ideal {b,c},Variable=>"T")
      f = dgAlgebraMap(K2,K1,matrix{{0,T_1,T_2}})
      g = dgAlgebraMap(K1,K2,matrix{{Y_2,Y_3}})
      toComplexMap g
      HHg = HH g
    Text
      One can also supply the second argument (a ZZ) in order to obtain the map on homology in a specified degree.
      (This is currently not available).
///

doc ///
  Key
    (source,DGAlgebraMap)
  Headline
    Outputs the source of a DGAlgebraMap
  Usage
    source phi
  Inputs
    phi:DGAlgebraMap
///

doc ///
  Key
    (target,DGAlgebraMap)
  Headline
    Outputs the target of a DGAlgebraMap
  Usage
    target phi
  Inputs
    phi:DGAlgebraMap
///

doc ///
  Key
    AssertWellDefined
  Headline
    Option to check whether the lifted map on DGAlgebras is well defined.
  Usage
    liftToDGMap(...,AssertWellDefined=>true)
///

doc ///
  Key
    StartDegree
  Headline
    Option to specify the degree to start computing the acyclic closure and killing cycles
  Usage
    acyclicClosure(...,StartDegree=>n)
///

doc ///
  Key
    EndDegree
  Headline
    Option to specify the degree to stop computing killing cycles and acyclic closure 
  Usage
    killCycles(...,StartDegree=>n)
///

doc ///
  Key
    GenDegreeLimit
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    homologyAlgebra(...,GenDegreeLimit=>n)
///

doc ///
  Key
    RelDegreeLimit
  Headline
    Option to specify the maximum degree to look for relations
  Usage
    homologyAlgebra(...,RelDegreeLimit=>n)
///

doc ///
  Key
    TMOLimit
  Headline
    Option to specify the maximum arity of the trivial Massey operation
  Usage
    findTrivialMasseyOperation(...,TMOLimit=>n)
///

doc ///
  Key
    [isAcyclic,EndDegree]
  Headline
    Option to specify the degree to finish checking acyclicity
  Usage
    isAcyclic(...,EndDegree=>n)
///

doc ///
  Key
    [acyclicClosure,StartDegree]
  Headline
    Option to specify the degree to start computing the acyclic closure
  Usage
    acyclicClosure(...,StartDegree=>n)
///

doc ///
  Key
    [acyclicClosure,EndDegree]
  Headline
    Option to specify the degree to stop computing the acyclic closure
  Usage
    acyclicClosure(...,EndDegree=>n)
///

doc ///
  Key
    [getGenerators,StartDegree]
  Headline
    Option to specify the degree to start finding generators of HH(DGAlgebra)
  Usage
    getGenerators(...,StartDegree=>n)
///

doc ///
  Key
    [getGenerators,DegreeLimit]
  Headline
    Option to specify the degree to stop finding generators of HH(DGAlgebra)
  Usage
    getGenerators(...,DegreeLimit=>n)
///

doc ///
  Key
    [killCycles,StartDegree]
  Headline
    Option to specify the degree to start looking for cycles
  Usage
    killCycles(...,StartDegree=>n)
///

doc ///
  Key
    [killCycles,EndDegree]
  Headline
    Option to specify the degree to stop looking for cycles
  Usage
    killCycles(...,EndDegree=>n)
///

doc ///
  Key
    [getBasis,Limit]
  Headline
    Option to specify the maximum number of basis elements to return
  Usage
    getBasis(...,Limit=>n)
///

doc ///
  Key
    [homologyAlgebra,GenDegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    homologyAlgebra(...,GenDegreeLimit=>n)
///

doc ///
  Key
    [homologyAlgebra,RelDegreeLimit]
  Headline
    Option to specify the maximum degree to look for relations
  Usage
    homologyAlgebra(...,RelDegreeLimit=>n)
///

doc ///
  Key
    [torAlgebra,GenDegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    torAlgebra(...,GenDegreeLimit=>n)
///

doc ///
  Key
    [torAlgebra,RelDegreeLimit]
  Headline
    Option to specify the maximum degree to look for relations
  Usage
    torAlgebra(...,RelDegreeLimit=>n)
///

doc ///
  Key
    [findTrivialMasseyOperation,GenDegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    findTrivialMasseyOperation(...,GenDegreeLimit=>n)
///

doc ///
  Key
    [findTrivialMasseyOperation,TMOLimit]
  Headline
    Option to specify the maximum arity of a trivial Massey operation, if one exists.
  Usage
    findTrivialMasseyOperation(...,TMOLimit=>n)
///

doc ///
  Key
    [isHomologyAlgebraTrivial,GenDegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    isHomologyAlgebraTrivial(...,GenDegreeLimit=>n)
///

doc ///
  Key
    [isGolodHomomorphism,GenDegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators
  Usage
    isGolodHomomorphism(...,GenDegreeLimit=>n)
///

doc ///
  Key
    [deviations,DegreeLimit]
  Headline
    Option to specify the maximum degree to look for generators when computing the deviations
  Usage
    deviations(...,DegreeLimit=>n)
///

doc ///
  Key
    [isGolodHomomorphism,TMOLimit]
  Headline
    Option to specify the maximum degree to look for generators when computing the deviations
  Usage
    isGolodHomomorphism(...,DegreeLimit=>n)
///

doc ///
  Key
    [homologyAlgebra,Verbosity]
  Headline
    Option to specify the maximum degree to look for generators when computing the deviations
  Usage
    homologyAlgebra(...,DegreeLimit=>n)
///

doc ///
  Key
    [getGenerators,Verbosity]
  Headline
    Option to specify the maximum degree to look for generators when computing the deviations
  Usage
    getGenerators(...,Verbosity=>n)
///

doc ///
  Key
    (net,DGAlgebra)
  Headline
    Outputs the pertinent information about a DGAlgebra
  Usage
    net A
  Inputs
    A:DGAlgebra
///

doc ///
  Key
    (net,DGAlgebraMap)
  Headline
    Outputs the pertinent information about a DGAlgebraMap
  Usage
    net phi
  Inputs
    phi:DGAlgebraMap
///

-------------------------------
--          Testing          --
-------------------------------

TEST ///
-- test 0 : isHomogeneous, chainComplex, maxDegree
R = ZZ/101[x,y,z]
A1 = freeDGAlgebra(R,{{1},{1},{1},{3}})
setDiff(A1,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
assert(not A1.isHomogeneous)
A1dd = chainComplex A1
A1dd.dd

A2 = freeDGAlgebra(R,{{1,1},{1,1},{1,1},{3,3}})
setDiff(A2,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
assert(A2.isHomogeneous)
A2dd = chainComplex A2
A2dd.dd

B1 = koszulComplexDGA(R)
assert(B1.isHomogeneous)
B1dd = chainComplex B1
B1dd.dd

R = ZZ/101[x,y,z]
R2 = R/ideal {x^2-z^3}
B2 = koszulComplexDGA(R2)
assert(not B2.isHomogeneous)
B2dd = chainComplex B2
B2dd.dd

R = QQ[x,y,z]
B = koszulComplexDGA(R)
chainComplex B
degrees B.natural
A = freeDGAlgebra(R,{{1},{1},{1},{3}})
setDiff(A,{x,y,z,x*T_2*T_3-y*T_1*T_3+z*T_1*T_2})
Add = chainComplex A
assert(apply(maxDegree(A)+1, i -> prune HH_i(Add)) == {coker vars R,0,0,coker vars R,0,0,0})
///

TEST ///
-- test 1 : differential tests
R = ZZ/101[x,y,z, Degrees => {2,2,3}]
kRes = res coker vars R
kRes.dd_3
A = koszulComplexDGA(R)
d3 = A.dd_3
d2 = A.dd_2
d1 = A.dd_1
assert(source d1 == target d2)
assert(source d2 == target d3)
assert(d1*d2 == 0)
assert(d2*d3 == 0)
S1 = R/ideal (x^3-z^2)
B1 = koszulComplexDGA(S1)
d3 = B1.dd_3
d2 = B1.dd_2
d1 = B1.dd_1
assert(source d1 == target d2)
assert(source d2 == target d3)
assert(d1*d2 == 0)
assert(d2*d3 == 0)
use R
S2 = R/ideal (x^4-z^2)
B2 = koszulComplexDGA(S2)
d3 = B2.dd_3
d2 = B2.dd_2
d1 = B2.dd_1
assert(source d1 == target d2)
assert(source d2 == target d3)
assert(d1*d2 == 0)
assert(d2*d3 == 0)
///

TEST ///
--- test 2 : homology, homologyAlgebra, HH_ZZ, HH
R = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
koszulR = koszul vars R
time apply(5,i -> numgens prune HH_i(koszulR))
A = koszulComplexDGA(R)
HH_2(A)
HH(A)
hh2 = prune HH_2(koszulR)
hh2' = prune HH_2(A)
assert(hh2 == hh2')
///

TEST ///
-- test 3 : torAlgebra, deviations
R1 = QQ[x,y,z]/ideal{x^3,y^4,z^5}
TorR1 = torAlgebra(R1,GenDegreeLimit=>4)
devR1 = deviations(R1,DegreeLimit=>4)
use R1
M = coker matrix {{x^2*y^3*z^4}}
Mres = res(M, LengthLimit => 7)
R2 = QQ[x,y,z]/ideal{x^3,y^4,z^5,x^2*y^3*z^4}
time TorR1R2 = torAlgebra(R1,R2,GenDegreeLimit=>5,RelDegreeLimit=>10)
-- the multiplication is trivial, since the map R3 --> R4 is Golod
numgens TorR1R2
numgens ideal TorR1R2
apply(21, i -> #(flatten entries getBasis
s(i,TorR1R2)))
assert(sum oo - 1 == numgens TorR1R2)
///

TEST ///
-- test 4 : findEasyRelations
debug DGAlgebras
R1 = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
R2 = ZZ/32003[a,b,x,y,Degrees=>{1,1,2,2}]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
A1 = koszulComplexDGA(R1)
A2 = koszulComplexDGA(R2)
cycleList1 = getGenerators(A1,DegreeLimit=>4)
cycleList2 = getGenerators(A2,DegreeLimit=>4)
HAEasy1 = findEasyRelations(A1,cycleList1)
HAEasy2 = findEasyRelations(A2,cycleList2)
tally ((flatten entries basis HAEasy1) / degree)
pairs (tally ((flatten entries basis HAEasy1) / degree))
myList1 = {({4,8},1),({3,4},1),({3,5},6),({3,6},6),({3,7},4),({2,3},4),({2,4},11),({2,5},8),({2,6},4),({1,2},4),({1,3},4),({1,4},1),({0,0},1)}
myList2 = {({0},1),({1},9),({2},27),({3},17),({4},1)}
tally ((flatten entries basis HAEasy1) / degree)
tally myList1
assert(pairs tally((flatten entries basis HAEasy1) / degree) == myList1)
assert(pairs tally((flatten entries basis HAEasy2) / degree) == myList2)
///

TEST ///
-- test 5 : homology of a DGA whose H_0 is not a field
R = ZZ/32003[a,b]
I = ideal{a^6,b^6}
A = koszulComplexDGA(I)
HA = HH A
describe HA
use R
J = I + ideal {a^4*b^5,a^5*b^4}
B = koszulComplexDGA(J)
getGenerators(B)
apply(5, i -> numgens prune homology(i,B))
apply(5, i -> prune homology(i,B))
HB = HH B
HB2 = zerothHomology B
HB.cache.cycles
ideal HB
-- looks right...
getDegNModule(0,HB2,HB)
getDegNModule(1,HB2,HB)
getDegNModule(2,HB2,HB)
getDegNModule(3,HB2,HB)
getDegNModule(4,HB2,HB)

R = ZZ/32003[a,b,c]
I = (ideal vars R)^2
A = koszulComplexDGA(I)
apply(10, i -> prune homology(i,A))
time HA = HH A
HA2 = zerothHomology A
tally ((ideal HA)_* / degree / first)
select ((ideal HA)_*, f -> first degree f == 2)
-- looks right...
getDegNModule(0,HA2,HA)
getDegNModule(1,HA2,HA)
getDegNModule(2,HA2,HA)
getDegNModule(3,HA2,HA)
-- need to add asserts
///

TEST ///
-- test 6 : homologyAlgebra
R = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
koszulR = koszul vars R
time apply(5,i -> numgens prune HH_i(koszulR))
A = koszulComplexDGA(R)
time apply(5,i -> numgens prune homology(i,A))
-- ~2.15 seconds on mbp, with graded differentials
time HA = HH A
assert(numgens HA == 34)
assert(numgens ideal HA == 576)
assert(#(first degrees HA) == 2)

-- same example, but not graded because of the degree change.  The homologyAlgebra function
-- will then only return a graded algebra
R2 = ZZ/32003[a,b,x,y,Degrees=>{1,1,2,2}]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
koszulR2 = koszul vars R2
time apply(5,i -> numgens prune HH_i(koszulR2))
A2 = koszulComplexDGA(R2)
time apply(5,i -> numgens prune homology(i,A2))
-- ~2.85 seconds on mbp, with ungraded differentials
time HA2 = homologyAlgebra A2
assert(numgens HA2 == 34)
assert(numgens ideal HA2 == 576)
-- should only be singly graded
assert(#(first degrees HA2) == 1)
///

TEST ///
-- test 7 : acyclicClosure, isHomologyAlgebraTrivial, isGolod, isGolodHomomorphism
R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
M = coker matrix {{a^3*b^3*c^3*d^3}};
S = R/ideal{a^3*b^3*c^3*d^3}
time A = acyclicClosure(R,EndDegree=>6)
B = A ** S
assert(isHomologyAlgebraTrivial(B,GenDegreeLimit=>6))
assert(isGolodHomomorphism(S,GenDegreeLimit=>6,TMOLimit=>3))
-- returns true since R --> S is Golod
R = ZZ/101[a,b,c,d]/ideal{a^4,b^4,c^4,d^4}
A = koszulComplexDGA(R)
assert(not isHomologyAlgebraTrivial(A))
assert(not isGolod R)
-- false, since R is Gorenstein, and so HA has Poincare Duality
///

TEST ///
-- test 8 : DGAlgebra ** DGAlgebra - need to add in an assert
R = ZZ/101[a,b,c,d]
I = ideal(a,b)
J = ideal(c,d)
A = koszulComplexDGA(I)
B = koszulComplexDGA(J)
Cdd = chainComplex (A ** B)
Cdd.dd
///

TEST ///
-- test 9 : isHomologyAlgebraTrivial, getGenerators, findTrivialMasseyOperation
Q = ZZ/101[x_1..x_6]
I = ideal (x_3*x_5,x_4*x_5,x_1*x_6,x_3*x_6,x_4*x_6)
R = Q/I
A = koszulComplexDGA(R)
isHomologyAlgebraTrivial(A,GenDegreeLimit=>3)
cycleList = getGenerators(A)
assert(findTrivialMasseyOperation(A) =!= null)

-- this is a Teter ring, and the computation in Avramov and Levin's paper shows
-- H(A) does not have trivial multiplication.
Q = ZZ/101[x,y,z]
I = ideal (x^3,y^3,z^3,x^2*y^2*z^2)
R = Q/I
A = koszulComplexDGA(R)
assert(not isHomologyAlgebraTrivial(A,GenDegreeLimit=>3))
cycleList = getGenerators(A)
prodList = apply(subsets(cycleList,2), l -> (first degree l#0 + first degree l#1,l#0*l#1));
assert(findTrivialMasseyOperation(A) === null)
///

TEST ///
-- test 10 : isAcyclic
R = ZZ/101[a,b,c,d]
A = koszulComplexDGA(R)
B = koszulComplexDGA({a^4,b^4,c^4,d^4})
C = koszulComplexDGA((ideal vars R)^2)
assert(isAcyclic A)
assert(isAcyclic B)
assert(not isAcyclic C)
///

TEST ///
-- test 11 : Need to add new tests
///

end

-- Below, we provide some of the examples used in development, unsupported and undocumented for the user.

-- Bug from the Macaulay2 Google Group
restart
needsPackage "DGAlgebras"
R = ZZ/32003[t, Inverses=>true, MonomialOrder=>RevLex]
I = ideal t^2
A = koszulComplexDGA(I)
skewList = select(toList(0..(#degList-1)), i -> odd first degList#i)
(A.ring)[varsList, Degrees=>{{1}}, Join => false, SkewCommutative => skewList]
(A.ring)[varsList]
-- so the DGAlgebras package does not work over local rings?

-- How to install the package
uninstallPackage "DGAlgebras"
restart
installPackage "DGAlgebras"
check "DGAlgebras"
loadPackage "DGAlgebras"
viewHelp DGAlgebras

-- Demo
-- 'Finite' DGAlgebras: the Koszul Complex
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
KR = koszulComplexDGA(R)
chainComplex KR
KR.dd
HKR = HH KR
describe HKR
peek HKR.cache

S = R/ideal{a^2*b^2*c^2*d^2}
KS = koszulComplexDGA(S)
HKS = HH KS;
numgens HKS
numgens ideal HKS
(ideal HKS)_*
peek HKS.cache

-- (potentially) infinite partial DGAlgebras : acyclic closures
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
XR = acyclicClosure(R)
apply(gens XR.natural, x -> XR.diff(x))

S = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3,a^2*b^2*c^2*d^2}
XS = acyclicClosure(S)
netList apply(gens XS.natural, x -> XS.diff(x))

-- homotopy fiber of projection R --> S
homotopyFiber = XR ** S
homologyHomotopyFiber = HH homotopyFiber
homologyHomotopyFiber = homologyAlgebra( homotopyFiber, GenDegreeLimit=>4, RelDegreeLimit=>8)
numgens homologyHomotopyFiber
numgens ideal homologyHomotopyFiber
peek homologyHomotopyFiber.cache

-- maps on Tor algebras of rings
phi = map(S,R)
torPhi = torMap phi
matrix torPhi
-- Note: need to add ker for ring maps from skew rings :)
ker torPhi

-- lifting ring maps to DG maps
phiTilde = liftToDGMap(XS,XR,phi)
apply(gens XR.natural, x -> phiTilde.natural x)

-- deviations
restart
loadPackage "DGAlgebras"
R1 = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3}
R2 = ZZ/101[a,b,c,d]/ideal{a^3,b^3,c^3,d^3,a^2*b^2*c^2*d^2}
devR1 = deviations R1
devR2 = deviations R2
poincR2 = deviationsToPoincare devR2
coefficients(poincR2, Variables=>{first gens ring poincR2})
res coker vars R2
R3 = ZZ/101[a,b,c,d,Degrees=>entries id_(ZZ^4)]/ideal{a^3,b^3,c^3,d^3,a^2*b^2*c^2*d^2}
degrees R3
devR3 = deviations R3
-- bug here!
deviationsToPoincare devR3

-- Golod DG Algebras and trivial Massey operations
restart
loadPackage "DGAlgebras"
Q = ZZ/101[x_1..x_6]
I = ideal (x_3*x_5,x_4*x_5,x_1*x_6,x_3*x_6,x_4*x_6)
R = Q/I
A = koszulComplexDGA(R)
isHomologyAlgebraTrivial A
cycleList = getGenerators(A)
tmo = findTrivialMasseyOperation(A)

-- stub function documentation node
doc ///
  Key
    myStub
    (myStub,DGAlgebra)
  Headline
    Stub headline
  Usage
    tmo = myStub(A)
  Inputs
    A:DGAlgebra
  Outputs
    tmo:List
      Stub Output
  Description
    Text
      This is a stub.
    Example
      Q = ZZ/101[x_1..x_6]
      I = ideal (x_3*x_5,x_4*x_5,x_1*x_6,x_3*x_6,x_4*x_6)
    Text
      More stub.
///

--stub option node

doc ///
  Key
    StubOption
  Headline
    Stub Option Headline
  Usage
    homologyAlgebra(...,StubOption=>n)
///

-- JSAG examples
restart
needsPackage "DGAlgebras";
R = ZZ/101[a,b,c]/ideal{a^3,b^3,a^2*b^2};
KR = koszulComplexDGA R
HKR = HH KR;
gens HKR
ideal HKR

-- trying to make pushForward functorial
restart
loadPackage "DGAlgebras"
R = ZZ/101[x,y,z]
S = R[w]/ideal{w^3,x*w^2}
f = map(S,R)
M = matrix {{x + x*w + w^2,w},{0,w^2}}
A = source M
B = target M
Mpush = pushForward(f,M)
-- test functoriality of pushForward
kSRes = res(coker matrix {{x,y,z,w}}, LengthLimit=>5)
kSRes1push = pushForward(f,kSRes.dd_1)
kSRes2push = pushForward(f,kSRes.dd_2)
kSRes3push = pushForward(f,kSRes.dd_3)
kSRes1push*kSRes2push
kSRes2push*kSRes3push
prune homology(kSRes1push,kSRes2push)
prune homology(kSRes2push,kSRes3push)
-- pushforward the ChainComplex
kSResPush = pushForward(f,kSRes)
prune HH kSResPush

-- lifting functions
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c]/ideal{a^3,b^3,c^3}
S = R/ideal{a^2*b^2*c^2}
f = map(S,R)
A = acyclicClosure(R,EndDegree=>3)
time(B = acyclicClosure(S,EndDegree=>3))
phi = liftToDGMap(B,A,f)
-- can't do the following yet, since M2 can't handle maps between chain complexes
-- over different rings. (Should pushforward the target and then try?)
toComplexMap(phi,EndDegree=>3)

-- torMap
restart
loadPackage "DGAlgebras"
printWidth=74
R = ZZ/101[a,b]/ideal{a^3,b^3,a^2*b^2}
S = R/ideal{a*b^2,a^2*b}
f = map(S,R)
Torf = torMap(f,GenDegreeLimit=>3);
TorR = source Torf
TorS = target Torf
Torf

-- below is a good test, since the target is less complicated than the source
-- which is backwards than the usual behavior
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c]/ideal{a^2,b^2,c^2,d^2,a*c,a*d,b*c,b*d}
S = ZZ/101[a,b]/ideal{a^2,b^2}
f = map(S,R,matrix{{a,b,0,0}})
Torf = torMap(f,GenDegreeLimit=>4);
TorR = source Torf;
TorS = target Torf;
-- note the homomorphism is large
matrix Torf

-- DGAlgebraMap Testing
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
K2 = koszulComplexDGA(ideal {b,c},Variable=>"T")
f = dgAlgebraMap(K2,K1,matrix{{0,T_1,T_2}})
f last gens (source f.natural)
isWellDefined f
g = dgAlgebraMap(K1,K2,matrix{{Y_2,Y_3}})
isWellDefined g
source g
target g
toComplexMap g
HHg = HH g

restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c]/ideal{a^3+b^3+c^3,a*b*c}
K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
K2 = koszulComplexDGA(ideal vars R,Variable=>"Z")
g = dgAlgebraMap(K2,K1,matrix{{Z_1,Z_2,Z_3}})
isWellDefined g
HH g

-- change of rings DGAlgebraMap currently does not work yet, since M2 expects
-- matrices to be defined between free modules over the same ring.  Need to use
-- pushForward (for ChainComplex; not yet written) for this to work.
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b,c]/ideal{a^2+b^2+c^2}
K1 = koszulComplexDGA(ideal vars R,Variable=>"Y")
S = ZZ/101[a,b]/ideal{a^2+b^2}
K2 = koszulComplexDGA(ideal vars S,Variable=>"T")
f = dgAlgebraMap(K2,K1,matrix{{T_1,T_2,0}})
isWellDefined f
toComplexMap f

-- Some examples and things that will eventually make it into the program and documentation.
------------------
--- Taylor's resolution code
restart
loadPackage "DGAlgebras"
R = ZZ/101[a,b]
I = monomialIdeal (a^2,a*b,b^2)
degList = reverse {{1,2,0},{1,1,1},{1,0,2},{2,2,1},{2,2,2},{2,1,2},{3,2,2}}
skewList = toList select(0..#degList-1, i -> odd first degList#i)
A = R[t123,t23,t13,t12,t3,t2,t1,MonomialOrder=>{4,3},SkewCommutative=>skewList, Degrees=>degList]/ideal(a*t12-t1*t2, t13-t1*t3, b*t23-t2*t3, a*t123-t1*t23, a*b*t123+t2*t13, b*t123-t12*t3,t12^2,t23^2,t12*t1,t12*t2,t23*t2,t23*t3,t123*t1,t123*t2,t123*t3,t123*t12,t123*t13,t123*t23,t12*t23)
-- above is how to represent the algebra in M2; not really a better way to do it.
basis(A)
I = sub(ideal (a^4,b^4),A)
B = A/I
basis(B)
-- note that the command basis(A) does not return the desired answer.  There are two problems.
-- first of all, it thinks that the module is not finite over the base (R), even though it is.
-- secondly, if we add in a^n and b^n to make it finite over ZZ/101, the answer given is not a basis -
--   the basis should be 1,t1,t2,t3,t12,t13,t23,t123 (should not have t1*t2, t1*t3, etc)
-- Note that A is a free R-module, with basis t1,t2,t3,t12,t13,t23,t123.
-- How can we get this basis in general, at least in the case that A is a free R-module?
--------------

--Tutorial (Include in a separate file?)
-- Koszul Complex and homology algebras
restart
loadPackage "DGAlgebras"
debug DGAlgebras
R1 = ZZ/32003[x,y,z]
A1 = koszulComplexDGA(R1)
A1Complex = chainComplex A1
A1Complex.dd
HA1 = homologyAlgebra(A1)
HA1 = HH A
describe HA1
R2 = R1/ideal{x^3,y^4,z^5}
A2 = koszulComplexDGA(R2)
time HA2 = homologyAlgebra(A2)
describe HA2
reduceHilbert hilbertSeries HA2
use R1
R3 = R1/ideal{x^3,y^4,z^5,x^2*y^3*z^4}
A3 = koszulComplexDGA(R3)
time HA3 = homologyAlgebra(A3)
describe HA3
reduceHilbert hilbertSeries HA3

restart
loadPackage "DGAlgebras"
Q = QQ[x,y,z]
I = ideal{y^3,z*x^2,y*(z^2+y*x),z^3+2*x*y*z,x*(z^2+y*x),z*y^2,x^3,z*(z^2+2*x*y)}
R = Q/I
ann ideal vars R
A = koszulComplexDGA(R)
time HA = homologyAlgebra(A)
reduceHilbert hilbertSeries HA
ann ideal vars HA

-- the following example baffles me.  The 'same' ideal is Gorenstein in characteristic 2, and Golod in characteristic 32003 (probably)
Q2 = ZZ/2[x,y,z]
f_1 = x^3*y + x^3*z + x*z^3+y*z^3
f_2 = x*y^3+y^3*z+x*z^3+y*z^3
f_3 = x*y^2*z+x*y*z^2+x*y^3+x^3*y+x*z^3+x^3*z
f_4 = x^2*y*z+x*y^2*z+x^3*z+x*z^3+y^3*z+y*z^3
f_5 = x^4+y^4+z^4+x^2*y^2+x^2*z^2+y^2*z^2+x^2*y*z+x*y^2*z+x*y*z^2+x^3*y+x^3*z
I2 = ideal{f_1,f_2,f_3,f_4,f_5}
R2 = Q2/I2
ann ideal vars R2
A2 = koszulComplexDGA(R2)
time HA2 = homologyAlgebra(A2)
reduceHilbert hilbertSeries HA2
ann ideal vars HA2

Q = ZZ/32003[x,y,z]
f_1 = x^3*y + x^3*z + x*z^3+y*z^3
f_2 = x*y^3+y^3*z+x*z^3+y*z^3
f_3 = x*y^2*z+x*y*z^2+x*y^3+x^3*y+x*z^3+x^3*z
f_4 = x^2*y*z+x*y^2*z+x^3*z+x*z^3+y^3*z+y*z^3
f_5 = x^4+y^4+z^4+x^2*y^2+x^2*z^2+y^2*z^2+x^2*y*z+x*y^2*z+x*y*z^2+x^3*y+x^3*z
I = ideal{f_1,f_2,f_3,f_4,f_5}
R = Q/I
ann ideal vars R
A = koszulComplexDGA(R)
time HA = homologyAlgebra(A)
-- should check HA by hand since the homology algebra is still monomial.
reduceHilbert hilbertSeries HA
isHomologyAlgebraTrivial(A)
ann ideal vars HA

-- fiber product example
restart
loadPackage "DGAlgebras"
R = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^4,a*x,a*y,b*x,b*y}
apply((numgens R) + 1, i -> numgens prune HH_i(koszul vars R))
A = koszulComplexDGA(R)
-- 1.17 seconds on mbp
time HA = homologyAlgebra(A)
HA.cache.cycles
socHAgens = (ann ideal vars HA)_*
-- kill all elements of the socle of the 'wrong degree'
-- the generators we are killing are elements in W from the theorem,
-- and are zero b/c they are part of a trivial extension.  The
-- others are actual problem elements that are actually zero in the
-- connected sum.
HB = HA / ideal (select(socHAgens, i -> first degree i < 4))
-- identify the generators of the right degree
HB = HB / ideal (X_7*X_25-X_5*X_24)
-- now have a PD algebra.
mingens ann ideal vars HB
-- now we trivially extend by a graded vector space, as well as its dual to get a new PD algebra, the
-- Koszul homology algebra of a connected sum (computed below)
reduceHilbert hilbertSeries HA
reduceHilbert hilbertSeries HB
peek HA.cache

-- ungraded connected sum example
restart
loadPackage "DGAlgebras"
R = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^4,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^3}
koszulR = koszul vars R
time apply(5,i -> numgens prune HH_i(koszulR))
A = koszulComplexDGA(R)
-- 3.8 seconds on mbp 
-- error here now - not sure why
time HA = homologyAlgebra(A)
socHA = ideal getBasis(4,HA)
HA.cache.cycles
reduceHilbert hilbertSeries HA
socHA = ideal getBasis(4,HA)
ann ideal vars HA
peek HA.cache

-- connected sum example
restart
loadPackage "DGAlgebras"
R = ZZ/32003[a,b,x,y]/ideal{a^3,b^3,x^3,y^3,a*x,a*y,b*x,b*y,a^2*b^2-x^2*y^2}
koszulR = koszul vars R
time apply(5,i -> numgens prune HH_i(koszulR))
A = koszulComplexDGA(R)
-- 2.7 seconds on mbp, with graded differentials
time HA = homologyAlgebra(A)
reduceHilbert hilbertSeries HA

-- connected sum example
-- goal: get this example to run quickly
restart
loadPackage "DGAlgebras"
R2 = ZZ/32003[a,b,x,y,z]/ideal{a^4,b^4,x^3,y^3,z^3,a*x,a*y,a*z,b*x,b*y,b*z,a^3*b^3-x^2*y^2*z^2}
A2 = koszulComplexDGA(R2)
time apply(6, i -> numgens prune homology(i,A2))
koszulR2 = koszul vars R2
time apply(6,i -> numgens prune HH_i(koszulR2))
-- 56 seconds on mbp
time HA2 = homologyAlgebra(A2)
numgens HA2
numgens ideal HA2
tally ((flatten entries basis HA2) / degree)
tally (((flatten entries basis HA2) / degree) / first)

-- This toric algebra is CM and not Koszul or Golod.  Is its homology algebra trivial?
restart
loadPackage "DGAlgebras"
R = QQ[x_1..x_6]/ideal(x_2^2-x_1*x_4,x_3^2-x_2*x_5,x_3*x_4-x_1*x_6,x_4^2-x_3*x_5,x_5^2-x_2*x_6)
A = koszulComplexDGA(R)
HA = HH A
isHomologyAlgebraTrivial(A)
-- no.

-- This algebra is not Golod, since its Poincare series is irrational.  But is its homology algebra trivial?
restart
loadPackage "DGAlgebras"
Q = QQ[a,b,c,d,e,f,g,h,i]
I = ideal (h^2-a*i,g^2-c*h,f^2-e*g,e*f-b*h,e^2-d*g,d*e-a*h,d^2-c*e,c*g-a*h,c*d-b*f,c^2-a*g,b*d-a*f,b^2-a*c)
res coker gens I
oo.dd
R = Q/I
A = koszulComplexDGA(R)
isHomologyAlgebraTrivial(A)
-- no.

-- connected sum example
-- goal: get this example to run quicker?
restart
loadPackage "DGAlgebras"
gbTrace = 2
R2 = ZZ/32003[a,b,c,x,y,z]/ideal{a^3,b^3,c^3,x^3,y^3,z^3,a*x,a*y,a*z,b*x,b*y,b*z,c*x,c*y,c*z,a^2*b^2*c^2-x^2*y^2*z^2}
A2 = koszulComplexDGA(R2)
time apply(7, i -> numgens prune homology(i,A2))
koszulR2 = koszul vars R2
time apply(7,i -> numgens prune HH_i(koszulR2))
time HA2 = homologyAlgebra(A2)
tally ((flatten entries basis HA2) / degree)
tally (((flatten entries basis HA2) / degree) / first)
-- 146 generators and 10662 relations (at least; didn't forceGB properly when I ran it before)

-- Tate resolution, chainComplex
restart
loadPackage "DGAlgebras"
debug DGAlgebras
R = QQ[x,y,z,w]/ideal{x^3,y^4,z^5}
A = acyclicClosure(R,EndDegree=>1)
time Add = chainComplex(A,LengthLimit => 20);
time kRes = res(coker vars R, LengthLimit => 20)

-- Homology
restart
loadPackage "DGAlgebras"
R3 = QQ[x,y,z]/ideal{x^3,y^4,z^5}
A3 = acyclicClosure(R3,EndDegree=>1)
time apply(7, i -> time numgens prune homology(i,A3))
time kRes = res(coker vars R3, LengthLimit=> 18)
time apply(17, i -> time HH_i(kRes));

-- Tor algebras
restart
loadPackage "DGAlgebras"
R3 = QQ[x,y,z]/ideal{x^3,y^4,z^5}
time TorR3 = torAlgebra(R3)
apply(16, i -> hilbertFunction(i,TorR3))
time res(coker vars R3, LengthLimit => 15)
R4 = QQ[x,y,z]/ideal{x^3,y^4,z^5,x^2*y^3*z^4}
TorR4 = torAlgebra(R4,GenDegreeLimit=>8)
apply(10, i -> hilbertFunction(i,TorR4))
res(coker vars R4, LengthLimit => 9)
TorR3R4 = torAlgebra(R3,R4,GenDegreeLimit=>4,RelDegreeLimit=>10)
reduceHilbert hilbertSeries TorR3R4
use R3
R4mod = coker matrix {{x^2*y^3*z^4}}
res(R4mod, LengthLimit => 6)

-- Acyclic closures
restart
loadPackage "DGAlgebras"
R3 = ZZ/32003[x,y]/ideal{x^3,y^4,x^2*y^3}
time A3 = acyclicClosure(R3,EndDegree=>5)
time HA3 = homologyAlgebra(A3,GenDegreeLimit=>6,RelDegreeLimit=>12)
time apply(12, i -> #(flatten entries getBasis(i,HA3)))
-- need to check the mult structure from Lucho's book.

-- The examples below are related to work in progress by Berest-Khatchatryan-Ramadoss on derived representation varieties
-- CC[x,y]; n = 2
restart
loadPackage "DGAlgebras"
debug DGAlgebras
R = QQ[x_11,x_12,x_21,x_22,y_11,y_12,y_21,y_22]
A = freeDGAlgebra(R,{{1,2},{1,2},{1,2}})
setDiff(A,{x_12*y_21 - x_21*y_12,
	   x_21*y_11+x_22*y_21-x_11*y_21-x_21*y_22,
	   x_11*y_12+x_12*y_22-x_12*y_11-x_22*y_12})
homList = apply(5,i -> numgens prune homology(i,A))
HA = homologyAlgebra(A)
HA2 = zerothHomology A
describe HA
describe HA2
degrees HA
degrees HA2
M1 = getDegNModule(0,HA2,HA)
reduceHilbert hilbertSeries M1
dim M1
M2 = getDegNModule(1,HA2,HA)
reduceHilbert hilbertSeries M2
dim M2
K = koszul vars HA2
-- is HA2 CM?
prune HH(K)
-- is M CM?
prune HH(K ** M)
getDegNModule(2,HA2,HA)

-- U(sl_2) example
restart
loadPackage "DGAlgebras"
debug DGAlgebras
x = symbol x; y = symbol y; z = symbol z; T = symbol T;
n = 2
pairsList = toList (set(1..n)**set(1..n))
symbolList = var -> apply(pairsList, i -> var_i)
R = QQ[a,b,symbolList x, symbolList y, symbolList z, Degrees=>{0,0}|toList (3*n^2:1)]
A = freeDGAlgebra(R,toList (((n^2*3):{1,2}) | (n^2:{2,3})))
tDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> x_(p#0,i)*T_(p#1+2*(i-1)) - T_(2*(p#0-1)+i)*x_(i,p#1) +
	                                                        y_(p#0,i)*T_(n^2+p#1+2*(i-1)) - T_(n^2+2*(p#0-1)+i)*y_(i,p#1) +
	                                                        z_(p#0,i)*T_(2*n^2+p#1+2*(i-1)) - T_(2*n^2+2*(p#0-1)+i)*z_(i,p#1)))
netList tDiffList
xDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> a*y_(p#0,i)*z_(i,p#1) + b*z_(p#0,i)*y_(i,p#1) + (1-a-b)*x_(p#0,i)*x_(i,p#1)))
netList xDiffList
yDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> a*z_(p#0,i)*x_(i,p#1) + b*x_(p#0,i)*z_(i,p#1) + (1-a-b)*y_(p#0,i)*y_(i,p#1)))
netList yDiffList
zDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> a*x_(p#0,i)*y_(i,p#1) + b*y_(p#0,i)*x_(i,p#1) + (1-a-b)*z_(p#0,i)*z_(i,p#1)))
netList zDiffList
allDiffs = xDiffList | yDiffList | zDiffList | tDiffList
netList allDiffs
#allDiffs
setDiff(A, allDiffs, InitializeDegreeZeroHomology => false)
complexA = chainComplex(A,LengthLimit=>5)
-- will not finish
numgens HH_0(complexA)
numgens HH_1(complexA)
numgens HH_2(complexA)
numgens HH_3(complexA)
numgens HH_4(complexA)

-- CC[x,y,z] n=2 example
restart
loadPackage "DGAlgebras"
debug DGAlgebras
x = symbol x; y = symbol y; z = symbol z; T = symbol T;
n = 2
pairsList = toList (set(1..n)**set(1..n))
symbolList = var -> apply(pairsList, i -> var_i)
R = QQ[symbolList x, symbolList y, symbolList z, Degrees=>toList (3*n^2:1)]
A = freeDGAlgebra(R,toList (((n^2*3):{1,2}) | (n^2:{2,3})))
tDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> x_(p#0,i)*T_(p#1+2*(i-1)) - T_(2*(p#0-1)+i)*x_(i,p#1) +
	                                                        y_(p#0,i)*T_(n^2+p#1+2*(i-1)) - T_(n^2+2*(p#0-1)+i)*y_(i,p#1) +
	                                                        z_(p#0,i)*T_(2*n^2+p#1+2*(i-1)) - T_(2*n^2+2*(p#0-1)+i)*z_(i,p#1)))
netList tDiffList
xDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> y_(p#0,i)*z_(i,p#1) - z_(p#0,i)*y_(i,p#1)))
netList xDiffList
yDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> z_(p#0,i)*x_(i,p#1) - x_(p#0,i)*z_(i,p#1)))
netList yDiffList
zDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> x_(p#0,i)*y_(i,p#1) - y_(p#0,i)*x_(i,p#1)))
netList zDiffList
allDiffs = xDiffList | yDiffList | zDiffList | tDiffList
netList allDiffs
-- I checked carefully that the code above generates the proper differentials.
setDiff(A, allDiffs, InitializeComplex => false)
H0Ring = zerothHomology A
dim H0Ring
K = koszul vars H0Ring
-- is H0Ring CM?
prune HH(K)
-- is M CM?
H1 = prune HH_1(A); numgens H1
H2 = prune HH_2(A); numgens H2
H3 = prune HH_3(A); numgens H3
H4 = prune HH_4(A); numgens H4
H5 = prune HH_5(A); numgens H5
-- compute the homology algebra?
-- degree zero is not a field, so the GB trick no longer works.  Think about a better way of doing this?
HA = homologyAlgebra(A, GenDegreeLimit=>2, RelDegreeLimit=>4);
netList select(flatten entries gens ideal HA, f -> first degree f == 2)
tally apply(degrees ideal HA, i -> first i)
tally apply(degrees HA, i -> first i)
M = getDegNModule(1,H0Ring,HA)
prune HH(K ** M)
genList = getGenerators(A,DegreeLimit=>5);

-- CC[x,y] n = 3 example
restart
loadPackage "DGAlgebras"
debug DGAlgebras
x = symbol x; y = symbol y; T = symbol T;
n = 3
pairsList = toList (set(1..n)**set(1..n))
symbolList = var -> apply(pairsList, i -> var_i)
R = QQ[symbolList x, symbolList y, Degrees=>toList (2*n^2:1)]
A = freeDGAlgebra(R,toList ((n^2):{1,2}))
tDiffList = apply(pairsList, p -> sum apply(toList (1..n), i -> x_(p#0,i)*y_(i,p#1) - y_(p#0,i)*x_(i,p#1)))
netList tDiffList
setDiff(A, tDiffList, InitializeComplex => false)
homologyList = apply(5,i -> numgens prune homology(i,A))
H0 = HH_0(A); numgens H0
H1 = prune HH_1(A); numgens H1
H2 = prune HH_2(A); numgens H2
H3 = prune HH_3(A); numgens H3
H4 = prune HH_4(A); numgens H4
H5 = prune HH_5(A); numgens H5
H6 = prune HH_6(A); numgens H6
H7 = prune HH_7(A); numgens H7
H8 = prune HH_8(A); numgens H8
H9 = prune HH_9(A); numgens H9
genList = getGenerators(A, DegreeLimit=>3)
HA = homologyAlgebra(A)

-- CC[x]/x^2 n=2
restart
loadPackage "DGAlgebras"
debug DGAlgebras
x = symbol x; T = symbol T;
n = 2
pairsList = toList (set(1..n)**set(1..n))
symbolList = var -> apply(pairsList, i -> var_i)
R = QQ[symbolList x, Degrees=>toList (n^2:1)]
A = freeDGAlgebra(R,toList ((n^2):{1,2}))
tDiffList = apply(pairsList, p -> x_(p#0,1)*x_(1,p#1) + x_(p#0,2)*x_(2,p#1))
netList tDiffList
setDiff(A, tDiffList, InitializeComplex => false)
HA = HH(A)
homologyList = apply(5,i -> numgens prune homology(i,A))
H0 = HH_0(A); numgens H0
H1 = prune HH_1(A); numgens H1
H2 = prune HH_2(A); numgens H2
H3 = prune HH_3(A); numgens H3
H4 = prune HH_4(A); numgens H4
H5 = prune HH_5(A); numgens H5
H6 = prune HH_6(A); numgens H6
H7 = prune HH_7(A); numgens H7

-- CC[x]/x^2 n=3
restart
loadPackage "DGAlgebras"
debug DGAlgebras
x = symbol x; T = symbol T;
n = 3
pairsList = toList (set(1..n)**set(1..n))
symbolList = var -> apply(pairsList, i -> var_i)
R = QQ[symbolList x, Degrees=>toList (n^2:1)]
A = freeDGAlgebra(R,toList ((n^2):{1,2}))
tDiffList = apply(pairsList, p -> x_(p#0,1)*x_(1,p#1) + x_(p#0,2)*x_(2,p#1)+ x_(p#0,3)*x_(3,p#1))
netList tDiffList
setDiff(A, tDiffList, InitializeComplex => false)
HA = HH(A)
homologyList = apply(5,i -> numgens prune homology(i,A))
H0 = HH_0(A); numgens H0
H1 = prune HH_1(A); numgens H1
H2 = prune HH_2(A); numgens H2
H3 = prune HH_3(A); numgens H3
H4 = prune HH_4(A); numgens H4
H5 = prune HH_5(A); numgens H5
H6 = prune HH_6(A); numgens H6
H7 = prune HH_7(A); numgens H7

R = QQ[x, SkewCommutative=>{0}]
M = coker vars R
res(M, LengthLimit=>10)
