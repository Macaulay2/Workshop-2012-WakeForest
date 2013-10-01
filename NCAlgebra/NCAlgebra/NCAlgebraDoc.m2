undocumented {(net,NCGroebnerBasis),
              (net,NCIdeal),
	      (net,NCLeftIdeal),
	      (net,NCRightIdeal),
	      (net,NCRing),
	      (net,NCRingElement),
	      (net,NCMatrix),
	      (net,NCRingMap),
	      (expression, NCMatrix),
	      (net,NCQuotientRing),
	      functionHash,
	      (NewFromMethod,NCPolynomialRing,List),
	      (NewFromMethod,NCQuotientRing,List)}

beginDocumentation()

-------------------------
----- Types
-------------------------
    
doc ///
  Key
    NCAlgebra
  Description
    Text
      This package is used to define and manipulate noncommutative algebras.  Many of the
      commands contain calls to the existing noncommutative algebra package Bergman.
  Subnodes
    "Basic operations on noncommutative algebras"
    "Using the Bergman interface"
///

doc ///
   Key
      NCRing
   Headline
      Type of a noncommutative ring.
   Description
      Text
         All noncommutative rings have this as an ancestor type.  It is the parent of the
	 types @ TO NCPolynomialRing @ and @ TO NCQuotientRing @. 
      Text
         In addition to defining a ring as a quotient of a @ TO NCPolynomialRing @, some common ways to create
	 NCRings include @ TO skewPolynomialRing @, @ TO endomorphismRing @, and @ TO oreExtension @.      
      
         Let's consider a three dimensional Sklyanin algebra.  We first define the tensor algebra:
      Example
         A = QQ{x,y,z}
      Text
         Then input the defining relations, and put them in an ideal:
      Example
	 f = y*z + z*y - x^2
	 g = x*z + z*x - y^2
	 h = z^2 - x*y - y*x
     	 I=ncIdeal{f,g,h}
      Text
         Next, define the quotient ring (as well as try a few functions on this new ring).  Note that
	 when the quotient ring is defined, a call is made to Bergman to compute the Groebner basis
	 of I (out to a certain degree, should the Groebner basis be infinite).
      Example
	 B=A/I
	 generators B
	 numgens B
	 isCommutative B
	 coefficientRing B
      Text
	 As we can see, x is an element of B.
      Example
         x
      Text
         If we define a new ring containing x, x is now part of that new ring
      Example
      	 C = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w}) 
         x
      Text
         We can 'go back' to B using the command @ TO (use, NCRing) @.
      Example
	 use B
	 x
	 use C
      Text
         We can also create an Ore extension.  First define a @ TO NCRingMap @ with @ TO ncMap @.
      Example
	 sigma = ncMap(C,C,{y,z,w,x})
      Text
         Then call the command @ TO oreExtension @.
      Example
	 D = oreExtension(C,sigma,a)
	 generators D
	 numgens D
   SeeAlso
      "Basic operations on noncommutative algebras"
///

doc ///
  Key
    (generators, NCRing)
  Headline
    The list of algebra generators of an NCRing
  Usage
    gensA = generators A
  Inputs
    A : NCRing
  Outputs
    gensA : List
  Description
    Text
       This function returns the generators of an NCRing as a list.  As usual,
       gens is a synonym for generators.
    Example
       A = QQ{x,y,z}
       generators A
       gens A
///

doc ///
  Key
    (numgens, NCRing)
  Headline
    The number of algebra generators of an NCRing
  Usage
    numgensA = numgens A
  Inputs
    A : NCRing
  Outputs
    numgensA : ZZ
  Description
    Text
       This function returns the number of generators of an NCRing.
    Example
       A = QQ{x,y,z}
       numgens A
///

doc ///
  Key
    (isCommutative, NCRing)
  Headline
    Returns whether an NCRing is commutative
  Usage
    isComm = isCommutative A
  Inputs
    A : NCRing
  Outputs
    isComm : Boolean
  Description
    Text
       This function returns whether an NCRing is commutative
    Example
       A = QQ{x,y,z}
       isCommutative A
       B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
       isCommutative B
       C = skewPolynomialRing(QQ,1_QQ,{x,y,z})
       isCommutative C
///

doc ///
  Key
    (coefficientRing, NCRing)
  Headline
    Returns the base ring of an NCRing
  Usage
    k = coefficientRing NCRing
  Inputs
    A : NCRing
  Outputs
    k : Ring
  Description
    Text
       This function returns the base ring of an NCRing
    Example
       A = QQ{x,y,z}
       coefficientRing A
       R = ZZ/101[a,b,c,d]/(ideal(a^2-b^2))
       B = R{x,y,z}
       coefficientRing B
///

doc ///
  Key
     (use, NCRing)
  Headline
     Brings the variables of a particular NCRing in scope
  Usage
    use A
  Inputs
    A : NCRing
  Description
    Text
       This function brings the variables of a particular NCRing in scope.
       For an illustration:
    Example
       A = QQ{x,y,z}
       coefficientRing A
       B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
       x
    Text
       As you can see, at this point the interpreter treats x,y and z as elements of B.  To go back to
       A, we run the command use A:
    Example
       use A
       x
///

doc ///
   Key
      NCPolynomialRing
   Headline
      Type of a noncommutative polynomial ring.
   Usage
      A = QQ{x,y}
   Description
      Text
         This is the type of a noncommutative polynomial ring over a commutative
	 ring R (i.e. a tensor algebra over R).  It has parent type @ TO NCRing @.
      Example
         A = QQ{x,y}
///

doc ///
   Key
      (ideal, NCPolynomialRing)
   Headline
      The defining ideal of an NCPolynomialRing
   Usage
      I = ideal A
   Inputs
      A : NCPolynomialRing
--   Outputs
--      I : NCIdeal
   Description
      Text
         This returns the defining ideal of an NCPolynomialRing, which 
	 will be the zero ideal in the noncommutative polynomial ring.
      Example
         A = QQ{x,y}
	 ideal A
///

doc ///
   Key
      NCQuotientRing
   Headline
      Type of a noncommutative ring.
   Description
      Text
         This is the type of a quotient of a tensor algebra by a two-sided ideal.
    
         At this point, one cannot define quotients of quotients.
///

doc ///
   Key
     (symbol /, NCPolynomialRing, NCIdeal)
   Headline
     Construct a NCQuotientRing
   Usage
     B = A/I
   Inputs
     A : NCPolynomialRing
     I : NCIdeal
   Outputs
     B : NCQuotientRing
   Description
      Text
         This is one way to create a quotient of the tensor algebra modulo some relations.
    
         At this point, one cannot define quotients of quotients.
	 
	 If the base ring is QQ or a finite field of order p, then Bergman is called to compute a
	 Groebner basis.
	 
	 If not, then one has a couple of options.  The first is to take the defining ideal of the algebra, and provide a
	 Groebner Basis by calling @ TO ncGroebnerBasis @ with the InstallGB flag set to true.  Of course, if this generating
	 set is not a Groebner basis, then you will get incorrect results upon calls to functions like @ TO (basis, ZZ, NCRing) @.
	 
	 The alternative is to use the built in commands @ TO skewPolynomialRing @ and @ TO oreExtension @ which
	 has the same effect as above occuring behind the scenes.  Just be careful using these commands to create your
	 ring if your base ring is not a field Bergman can work with, as the generating sets created may not be a Groebner
	 basis for the defining ideal (this is more often a problem for @ TO oreExtension @ than @ TO skewPolynomialRing @).
      Example
         A = QQ{x,y,z}
         f = y*z + z*y - x^2
	 g = x*z + z*x - y^2
	 h = z^2 - x*y - y*x
     	 I=ncIdeal{f,g,h}
    	 B = A/I
         z^2
	 R = toField(QQ[a]/ideal(a^4+a^3+a^2+a+1))
	 C = skewPolynomialRing(R,a,{x,y,z})
	 y*x
///

doc ///
   Key
     (ambient, NCQuotientRing)
   Headline
     Ambient ring of an NCQuotientRing
   Usage
     A = ambient B 
   Inputs
     B : NCQuotientRing
   Outputs
     A : NCPolynomialRing
   Description
      Text
         Returns the ambient ring of an @ TO NCQuotientRing @.  
	 
	 As quotients of NCQuotientRings are added, this will return the top-level ambient ring.
	 
      Example
         B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
	 A = ambient B
///

doc ///
   Key
     (ideal, NCQuotientRing)
   Headline
     Defining ideal of an NCQuotientRing in its ambient ring
   Usage
     I = ideal B
   Inputs
     B : NCQuotientRing
--   Outputs
--     I : NCIdeal
   Description
      Text
         This returns the defining ideal of an NCQuotientRing in its ambient ring.  As of now,
	 this is always an ideal in an NCPolynomialRing, but when quotients of @ TO NCQuotientRing @s
	 are added, this will no longer be the case.
      Example
         B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
	 A = ambient B
	 I = ideal B
	 ring I === A
///

doc ///
   Key
      NCMatrix
   Headline
      Type of a matrix over a noncommutative ring.
   Description
      Text
         This is the type of a matrix over a noncommutative ring.  These represent homomorphisms between two free modules in
	 chosen bases (whether you think of it as a map of left or right modules is up you).  Modules themselves are not
	 implemented yet in the @ TO NCAlgebra @ package, but are slated for a later release.
      Text
         Common ways to make (and use) a matrix include
      Code
         UL {TO (ncMatrix, List),
	     TO (basis, ZZ, NCRing),
	     TO (rightKernel, NCMatrix, ZZ),
	     TO (rightKernelBergman, NCMatrix)}
      Text
         Common ways to get information about matrices
      Code
         UL {TO (ring, NCMatrix),
	     TO (entries, NCMatrix)}
      Text
         Common operations on matrices:
      Code
         UL {TO (symbol +, NCMatrix,NCMatrix),
	     TO (symbol -, NCMatrix,NCMatrix),
	     TO (symbol %, NCMatrix,NCGroebnerBasis),
             TO (symbol *, NCMatrix,NCMatrix),
	     TO (symbol *, NCMatrix,NCRingElement),
	     TO (symbol *, NCMatrix,RingElement),
	     TO (symbol //, NCMatrix,NCMatrix),
	     TO (symbol _, NCMatrix,List),
	     TO (symbol ==, NCMatrix, NCMatrix),
	     TO (symbol |, NCMatrix,NCMatrix),
	     TO (symbol ||, NCMatrix,NCMatrix),
	     TO (symbol ^, NCMatrix,List),
	     TO (symbol ^, NCMatrix,ZZ),
	     }
      Text
         This is the type of a matrix with entries in an NCRing.  Many of the basic operations
	 one can perform on a @ TO Matrix @ are also allowed with an @ TO NCMatrix @.  Some
	 examples of creating and using them are given below.
      Example
         A = QQ{a,b,c,d}
	 M = ncMatrix {{a,b,c,d}}
	 N = ncMatrix {{M,2*M,3*M},{4*M,5*M,6*M}}

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
	 X = NB + 3*NB
	 Y = NB | 2*NB
	 Z = X || NB

///

doc ///
   Key
      ncMatrix
      (ncMatrix,List)
      (symbol -, NCMatrix)
      (symbol %, NCMatrix, NCGroebnerBasis)
      (symbol *, NCMatrix, Matrix)
      (symbol *, Matrix, NCMatrix)
      (symbol *, NCMatrix, NCMatrix)
      (symbol *, NCMatrix, NCRingElement)
      (symbol *, NCRingElement, NCMatrix)
      (symbol *, NCMatrix, RingElement)
      (symbol *, NCMatrix, QQ)
      (symbol *, NCMatrix, ZZ)
      (symbol *, RingElement, NCMatrix)
      (symbol *, QQ, NCMatrix)
      (symbol *, ZZ, NCMatrix)
      (symbol +, NCMatrix, NCMatrix)
      (symbol -, NCMatrix, NCMatrix)
      (symbol |, NCMatrix, NCMatrix)
      (symbol ||, NCMatrix, NCMatrix)
      (symbol //, NCMatrix, NCMatrix)
      (symbol ==, NCMatrix, NCMatrix)
      (symbol ==, NCMatrix, ZZ)
      (symbol ==, ZZ, NCMatrix)
      (symbol ^, NCMatrix, List)
      (symbol _, NCMatrix, List)
      (symbol ^, NCMatrix, ZZ)
      (transpose, NCMatrix)
      (lift, NCMatrix)
      (ring, NCMatrix)
      (entries, NCMatrix)
   Headline
      This command does...
   Description
      Text
         This command does...
      Example
         A = QQ{a,b,c,d}
	 M = ncMatrix {{a,b,c,d}}
	 N = ncMatrix {{M,2*M,3*M},{4*M,5*M,6*M}}

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
	 X = NB + 3*NB
	 Y = NB | 2*NB
	 Z = X || NB
///

doc ///
   Key
      NCRingElement
      (degree, NCRingElement)
      (ring, NCRingElement)
      (terms, NCRingElement)
      (size, NCRingElement)
      (support, NCRingElement)
      (monomials, NCRingElement)
      (leadMonomial,NCRingElement)
      (leadCoefficient, NCRingElement)
      (leadTerm, NCRingElement)
      (isConstant, NCRingElement)
      (toString, NCRingElement)
      (symbol *, NCRingElement, List)
      (symbol *, List, NCRingElement)
      (baseName, NCRingElement)
   Headline
      Type of an element in a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
        This is the type of an element in a noncommutative graded ring.
///

doc ///
   Key
      NCGroebnerBasis
      maxNCGBDegree
      minNCGBDegree
      ncGroebnerBasis
      (ncGroebnerBasis,List)
      (ncGroebnerBasis,NCIdeal)
      (symbol %, NCRingElement, NCGroebnerBasis)
      (symbol %, QQ, NCGroebnerBasis)
      (symbol %, ZZ, NCGroebnerBasis)
      (generators, NCGroebnerBasis)
      gbFromOutputFile
      (gbFromOutputFile,NCPolynomialRing,String)
      twoSidedNCGroebnerBasisBergman
      (twoSidedNCGroebnerBasisBergman,List)
      (twoSidedNCGroebnerBasisBergman,NCIdeal)
      NumModuleVars
      [twoSidedNCGroebnerBasisBergman,NumModuleVars]
      CacheBergmanGB
      ClearDenominators
      InstallGB
      ReturnIdeal
   Headline
      Type of a Groebner basis for an ideal in a noncommutative ring
   --Usage
   --Inputs
   --Outputs
   Description
     Example
       R = QQ[a,b,c,d]/ideal{a*b+c*d}
       A = R {x,y,z}
       I = ncIdeal {a*x*y,b*z^2}
       Igb = ncGroebnerBasis(I, InstallGB=>true)
       c*z^2 % Igb 
       b*z^2 % Igb

       A = QQ{x,y,z}
       p = y*z + z*y - x^2
       q = x*z + z*x - y^2
       r = z^2 - x*y - y*x
       I = ncIdeal {p,q,r}
       Igb = ncGroebnerBasis I
       normalFormBergman(z^17,Igb)

	{*
        --- This doesn't work in help generator because it can't find the file.
	A=QQ{a, b, c, d, e, f, g, h}
	I = gbFromOutputFile(A,"NCAlgebra/UghABCgb6.txt", ReturnIdeal=>true);
	B=A/I
	F = a^7+b^7+c^7+d^7+e^7+f^7+g^7+h^7;
	bas=basis(2,B);
	X = flatten entries (F*bas);
	XA = apply(X, x -> promote(x,A));
	use A
	XA_{0,1,2,3,4}
	*}

     Text
       stuff
///

doc ///
   Key
      NCLeftIdeal
      ncLeftIdeal
      NCRightIdeal
      (ring, NCRightIdeal)
      (ring, NCLeftIdeal)
      (ncLeftIdeal,List)
      (ncLeftIdeal,NCRingElement)
      ncRightIdeal
      (ncRightIdeal,List)
      (ncRightIdeal,NCRingElement)
      (generators, NCRightIdeal)
      (generators, NCLeftIdeal)
      (symbol +, NCRightIdeal, NCRightIdeal)
      (symbol +, NCLeftIdeal, NCLeftIdeal)
   Headline
      Type of an ideal in a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
        This is the type of an ideal in a noncommutative graded ring.
///

doc ///
   Key
      NCIdeal
      ncIdeal
      (ncIdeal,List)
      (ncIdeal,NCRingElement)
      (symbol +, NCIdeal, NCIdeal)
      (ring, NCIdeal)
      (generators, NCIdeal)
   Headline
      Creates an ideal in a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
      -- need to finish unit tests
      Text
        stuff
///


doc ///
   Key
      (basis, ZZ, NCIdeal)
      (basis, ZZ, NCRightIdeal)
      (basis, ZZ, NCLeftIdeal)
      (basis, ZZ, NCRing)
   Headline
      Determines whether the input defines a homogeneous object.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
      -- need to finish unit tests
      Text
        stuff
///

doc ///
   Key
      (isHomogeneous, NCIdeal)
      (isHomogeneous, NCRightIdeal)
      (isHomogeneous, NCLeftIdeal)
      (isHomogeneous, NCRing)
      (isHomogeneous, NCMatrix)
      (isHomogeneous, NCRingElement)
   Headline
      Determines whether the input defines a homogeneous object.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
      -- need to finish unit tests
      Text
        stuff
///

doc ///
   Key
      "Basic operations on noncommutative algebras"
   Description
      Example
         A = QQ{x,y,z}
	 f = y*z + z*y - x^2
	 g = x*z + z*x - y^2
	 h = z^2 - x*y - y*x
	 f*g
	 f^2
	 f-g 
         3*g
         f+g
	 B = A/ncIdeal{f,g,h}
	 j = -y^3-x*y*z+y*x*z+x^3
	 k = x^2 + y^2 + z^2
	 j*k
	 k^3
      Text
         Here will go an extended example
///

doc ///
   Key
      "Using the Bergman interface"
   Description
      Text
         Here will go an extended example
///

doc ///
   Key
      rightKernelBergman
      (rightKernelBergman,NCMatrix)
      assignDegrees
      (assignDegrees,NCMatrix)
      (assignDegrees,NCMatrix,List,List)
      [rightKernelBergman,DegreeLimit]
   Headline
      Methods for computing kernels of matrices over noncommutative rings using Bergman
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         A = QQ{x,y,z}
         f1 = y*z + z*y - x^2
         f2 = x*z + z*x - y^2
         f3 = z^2 - x*y - y*x
         g = -y^3-x*y*z+y*x*z+x^3
         I = ncIdeal {f1,f2,f3,g}
         B = A/I
         M3 = ncMatrix {{x,y,z,0}, {-y*z-2*x^2,-y*x,z*x-x*z,x},{x*y-2*y*x,x*z,-x^2,y}, {-y^2-z*x,x^2,-x*y,z}}
         assignDegrees(M3,{1,0,0,0},{2,2,2,1})
         ker1M3 = rightKernelBergman(M3)
         M3*ker1M3 == 0
         ker2M3 = rightKernelBergman(ker1M3)
         ker1M3*ker2M3 == 0
         ker3M3 = rightKernelBergman(ker2M3)
         ker2M3*ker3M3 == 0
      Text
         stuff
///

doc ///
   Key
      isLeftRegular
      (isLeftRegular,NCRingElement,ZZ)
      isRightRegular
      (isRightRegular,NCRingElement,ZZ)
   Headline
      Determines if a given (homogeneous) element is regular in a given degree.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      isCentral
      (isCentral,NCRingElement)
      (isCentral,NCRingElement,NCGroebnerBasis)
      centralElements
      (centralElements, NCRing, ZZ)
   Headline
      Methods for finding/checking central elements.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
        A = QQ{x,y,z}
        I = ncIdeal { y*z + z*y - x^2,x*z + z*x - y^2,z^2 - x*y - y*x}
        B = A/I
        g = -y^3-x*y*z+y*x*z+x^3
        h = x^2 + y^2 + z^2
        isCentral h
        isCentral g
        centralElements(B,2)
        centralElements(B,3)

      Text
         We have not yet implemented the check in a fixed degree.
///




doc ///
   Key
      normalElements
 --     (normalElements, NCRingMap, ZZ) -- does this key exist?
      (normalElements, NCQuotientRing, ZZ, Symbol, Symbol)
      (normalElements, NCRingMap, ZZ)
      (isNormal, NCRingElement)
   Headline
      Computes normal monomials and components of the variety of normal elements in a given degree.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///


doc ///
   Key
      normalAutomorphism
      (normalAutomorphism,NCRingElement)
   Headline
      Computes the automorphism determined by a normal homogeneous element.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
        This is the type of a matrix over a noncommutative graded ring.
///

doc ///
   Key
      leftMultiplicationMap
      (leftMultiplicationMap,NCRingElement,ZZ)
      (leftMultiplicationMap,NCRingElement,List,List)
      rightMultiplicationMap
      (rightMultiplicationMap,NCRingElement,ZZ)
      (rightMultiplicationMap,NCRingElement,List,List)
   Headline
      Computes a matrix for left or right multiplication by a homogeneous element.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      rightKernel
      (rightKernel,NCMatrix,ZZ)
      NumberOfBins
      [rightKernel,NumberOfBins]
      [rightKernel,Verbosity]
   Headline
      Method for computing kernels of matrices over noncommutative rings in a given degree without using Bergman
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///


doc ///
   Key
      quadraticClosure
      (quadraticClosure,NCIdeal)
      (quadraticClosure,NCQuotientRing)
   Headline
      Creates the subideal generated by quadratic elements of a given ideal.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      homogDual
      (homogDual,NCIdeal)
      (homogDual,NCQuotientRing)
   Headline
      Computes the dual of a pure homogeneous ideal.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      sparseCoeffs
      (sparseCoeffs,List)
      (sparseCoeffs,NCRingElement)
      [sparseCoeffs,Monomials]
   Headline
      Converts ring elements into vectors over the coefficient ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         A=QQ{a, b, c, d, e, f, g, h}
	 F = a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2;
	 bas = flatten entries basis(2,A);
	 #bas
	 sparseCoeffs(F,Monomials=>bas)
	 sparseCoeffs(toList (10:F),Monomials=>bas)
      Text
         stuff
///


doc ///
   Key
      NCRingMap
      ncMap
      (ncMap,NCRing,NCRing,List)
      (ncMap,Ring,NCRing,List)
      (ambient, NCRingMap)
      (isHomogeneous, NCRingMap)
      (isWellDefined, NCRingMap)
      (symbol /, List, NCRingMap)
      (matrix, NCRingMap)
      (symbol @@, NCRingMap, NCRingMap)
      (symbol SPACE, NCRingMap, NCRingElement)
      (symbol SPACE, NCRingMap, NCMatrix)
      (symbol _, NCRingMap, ZZ)
      (source, NCRingMap)
      (target, NCRingMap)
   Headline
      Creates a map from a non-commutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      oreExtension
      (oreExtension,NCRing,NCRingMap,NCRingMap,NCRingElement)
      (oreExtension,NCRing,NCRingMap,NCRingMap,Symbol)
      (oreExtension,NCRing,NCRingMap,NCRingElement)
      (oreExtension,NCRing,NCRingMap,Symbol)
   Headline
      Creates an Ore extension of a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w})
	 sigma = ncMap(B,B,{y,z,w,x})
	 C = oreExtension(B,sigma,a)
      Text
         stuff
///

doc ///
   Key
      oreIdeal
      (oreIdeal,NCRing,NCRingMap,NCRingMap,NCRingElement)
      (oreIdeal,NCRing,NCRingMap,NCRingMap,Symbol)
      (oreIdeal,NCRing,NCRingMap,NCRingElement)
      (oreIdeal,NCRing,NCRingMap,Symbol)
   Headline
      Creates the defining ideal of an Ore extension of a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         B = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w})
	 sigma = ncMap(B,B,{y,z,w,x})
	 C = oreIdeal(B,sigma,a)
      Text
         stuff
///

doc ///
   Key
      endomorphismRing
      (endomorphismRing,Module,Symbol)
      endomorphismRingGens
       minimizeRelations
      (minimizeRelations,List)
   Headline
      Methods for creating endomorphism rings of modules over a commutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         Q = QQ[a,b,c]
         R = Q/ideal{a*b-c^2}
         kRes = res(coker vars R, LengthLimit=>7);
         M = coker kRes.dd_5
         B = endomorphismRing(M,X);
         gensI = gens ideal B;
         gensIMin = minimizeRelations(gensI);

         Q = QQ[a,b,c,d]
         R = Q/ideal{a*b+c*d}
         kRes = res(coker vars R, LengthLimit=>7);
         M = coker kRes.dd_5
         B = endomorphismRing(M,Y);
         gensI = gens ideal B;
         gensIMin = minimizeRelations(gensI);

      Text
         stuff
///



doc ///
   Key
      skewPolynomialRing
      (skewPolynomialRing,Ring,Matrix,List)
      (skewPolynomialRing,Ring,QQ,List)
      (skewPolynomialRing,Ring,RingElement,List)
      (skewPolynomialRing,Ring,ZZ,List)
      abelianization
      (abelianization,NCRing)
      skewAbelianization
      (skewAbelianization,NCRing)
   Headline
      Methods for working with skew polynomial rings.
   --Usage
   --Inputs
   --Outputs
   Description
      Example
         R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
         B = skewPolynomialRing(R,q,{x,y,z,w})
         x*y == q*y*x
         C = skewPolynomialRing(QQ,1_QQ, {x,y,z,w})
         isCommutative C
         isCommutative B
         abC = abelianization C
         abC' = abelianization ambient C
         ideal abC == 0
         ideal abC' == 0
         Bop = oppositeRing B
         y*x == q*x*y

      Text
         Link to oppositeRing.
///


doc ///
   Key
      oppositeRing
      (oppositeRing,NCRing)
   Headline
      Creates the opposite ring of a noncommutative ring.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
        stuff
///

doc ///
   Key
      normalFormBergman
      (normalFormBergman,List,NCGroebnerBasis)
      (normalFormBergman,NCRingElement,NCGroebnerBasis)
      [normalFormBergman,CacheBergmanGB]
      [normalFormBergman,ClearDenominators]
      [normalFormBergman,NumModuleVars]
      [normalFormBergman,DegreeLimit]
   Headline
      Calls Bergman for a normal form calculation.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

doc ///
   Key
      isReduced
   Headline
      Determines if a given element is in normal form with respect to a groebner basis.
   --Usage
   --   isReduced
   --Inputs
   --Outputs
   Description
      Text
         stuff
///


doc ///
   Key
      hilbertBergman
      (hilbertBergman, NCQuotientRing)
      [hilbertBergman,DegreeLimit]
      DegreeVariable
   Headline
      Calls Bergman for a Hilbert series calculation.
   --Usage
   --Inputs
   --Outputs
   Description
      Text
         stuff
///

