beginDocumentation()



-------------------------
----- Types
-------------------------
    
doc ///
  Key
    NCAlgebra
  Headline
    Data types and basic functions for noncommutative algebras.
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
         In addition to defining a ring as a quotient of a @ TO NCPolynomialRing @, some common ways to create NCRings include @ TO SkewPolynomialRing @, @ TO endomorphismRing @, and @ TO oreExtension @.
      
      Example
         A = QQ{x,y,z}
	 f = y*z + z*y - x^2
	 g = x*z + z*x - y^2
	 h = z^2 - x*y - y*x
     	 I=ncIdeal{f,g,h}
	 B=A/I
	 
	 C = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z,w}) 
	 sigma = ncMap(C,C,{y,z,w,x})
	 D = oreExtension(C,sigma,a)

     SeeAlso
       "Basic operations on noncommutative algebras"
///

doc ///
   Key
      NCPolynomialRing
   Headline
      Type of a noncommutative polynomial ring.
   Description
      Text
         This is the type of a noncommutative polynomial ring over a commutative
	 ring R (i.e. a tensor algebra over R)
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
      NCMatrix
      ncMatrix
      (ncMatrix,List)
   Headline
      Type of a matrix over a noncommutative ring.
   Description
      Text
         This is the type of a matrix over a noncommutative ring. 
      Text
         Common ways to make a matrix include
      Text
         Common ways to get information about matrices

         ring NCMatrix
	 entries NCMatrix

      Text
         Common operations on matrices:
	 
	 NCMatrix + NCMatrix
	 NCMatrix - NCMatrix 
	 NCMatrix * NCMatrix
	 NCMatrix * Matrix
	 NCMatrix % NCGroebnerBasis
	 NCMatrix ^ ZZ 
	 NCMatrix | NCMatrix
	 NCMatrix || NCMatrix
	 NCMatrix * NCRingElement
	 lift NCMatrix
	 transpose NCMatrix

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
   Headline
      Type of an element in a noncommutative ring.
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
      gbFromOutputFile
      (gbFromOutputFile,NCPolynomialRing,String)
      twoSidedNCGroebnerBasisBergman
      (twoSidedNCGroebnerBasisBergman,List)
      (twoSidedNCGroebnerBasisBergman,NCIdeal)
      CacheBergmanGB
      ClearDenominators
      InstallGB
      ReturnIdeal
   Headline
      Type of a groebner basis for an ideal in a noncommutative ring
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

        A=QQ{a, b, c, d, e, f, g, h}
	I = gbFromOutputFile(A,"UghABCgb6.txt", ReturnIdeal=>true);
	B=A/I
	F = a^7+b^7+c^7+d^7+e^7+f^7+g^7+h^7;
	bas=basis(2,B);
	X = flatten entries (F*bas);
	XA = apply(X, x -> promote(x,A));
	use A
	XA_{0,1,2,3,4}


      Text
        stuff
///

doc ///
   Key
      NCIdeal
      NCLeftIdeal
      NCRightIdeal
   Headline
      Type of an ideal in a noncommutative ring.
   Description
      Text
        This is the type of an ideal in a noncommutative graded ring.
///

doc ///
   Key
      ncIdeal
      (ncIdeal,List)
      (ncIdeal,NCRingElement)
      ncLeftIdeal
      (ncLeftIdeal,List)
      (ncLeftIdeal,NCRingElement)
      ncRightIdeal
      (ncRightIdeal,List)
      (ncRightIdeal,NCRingElement)

   Headline
      Creates an ideal in a noncommutative ring.
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
   Headline
      Methods for computing kernels of matrices over noncommutative rings using Bergman
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
   Headline
      Computes normal monomials and components of the variety of normal elements in a given degree.
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
   Description
      Text
         stuff
///

doc ///
   Key
      rightKernel
      (rightKernel,NCMatrix,ZZ)
      NumberOfBins
   Headline
      Method for computing kernels of matrices over noncommutative rings in a given degree without using Bergman
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
   Description
      Text
         stuff
///

doc ///
   Key
      sparseCoeffs
      (sparseCoeffs,List)
      (sparseCoeffs,NCRingElement)
   Headline
      Converts ring elements into vectors over the coefficient ring.
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
      ncMap
      (ncMap,NCRing,NCRing,List)
      (ncMap,Ring,NCRing,List)
      functionHash
   Headline
      Creates a map of noncommutative rings.
   Description
      Text
         stuff
///

doc ///
   Key
      oreExtension
      oreIdeal
   Headline
      Creates an Ore extension of a noncommutative ring.
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
      endomorphismRing
      (endomorphismRing,Module,Symbol)
      endomorphismRingGens
       minimizeRelations
      (minimizeRelations,List)
      checkHomRelations
      (checkHomRelations,List,List)
   Headline
      Methods for creating endomorphism rings of modules over a commutative ring.
   Description
      Example
         Q = QQ[a,b,c]
         R = Q/ideal{a*b-c^2}
         kRes = res(coker vars R, LengthLimit=>7);
         M = coker kRes.dd_5
         B = endomorphismRing(M,X);
         gensI = gens ideal B;
         gensIMin = minimizeRelations(gensI);
         checkHomRelations(gensIMin,B.cache.endomorphismRingGens)

         Q = QQ[a,b,c,d]
         R = Q/ideal{a*b+c*d}
         kRes = res(coker vars R, LengthLimit=>7);
         M = coker kRes.dd_5
         B = endomorphismRing(M,Y);
         gensI = gens ideal B;
         gensIMin = minimizeRelations(gensI);
         checkHomRelations(gensIMin,B.cache.endomorphismRingGens);

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
   Headline
      Methods for working with skew polynomial rings.
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
   Description
      Text
        stuff
///

doc ///
   Key
      normalFormBergman
      (normalFormBergman,List,NCGroebnerBasis)
      (normalFormBergman,NCRingElement,NCGroebnerBasis)
   Headline
      Calls Bergman for a normal form calculation.
   Description
      Text
         stuff
///

doc ///
   Key
      isReduced
   Headline
      Determines if a given element is in normal form with respect to a groebner basis.
   Description
      Text
         stuff
///


doc ///
   Key
      hilbertBergman
      (hilbertBergman, NCQuotientRing)
      DegreeVariable
   Headline
      Calls Bergman for a Hilbert series calculation.
   Description
      Text
         stuff
///

