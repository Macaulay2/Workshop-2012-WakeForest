beginDocumentation()

undocumented { generatorSymbols, weights, -- can I get away with not exporting these somehow?
         NCRingElement, isReduced,
         NCGroebnerBasis, ncGroebnerBasis, maxNCGBDegree, minNCGBDegree,
         NCIdeal, NCLeftIdeal, NCRightIdeal,
         ncIdeal, ncLeftIdeal, ncRightIdeal,
         twoSidedNCGroebnerBasisBergman,
         gbFromOutputFile,
	 ComputeNCGB,
         UsePreviousGBOutput,
         CacheBergmanGB,
         ClearDenominators,
         InstallGB,
         ReturnIdeal,
         NumberOfBins,
         CheckPrefixOnly,
         normalFormBergman,
         hilbertBergman, DegreeVariable,
         rightKernelBergman,
	 isLeftRegular,
         isRightRegular,
         centralElements,
         normalElements,
	 assignDegrees,
         normalAutomorphism,
         leftMultiplicationMap,
         rightMultiplicationMap,
         rightHomogKernel,
         rightKernel,
         getLeftProductRows,
         NCMatrix, ncMatrix,
         NCMonomial,monList,
         isCentral,
         ncMap,functionHash,
         oreExtension,oreIdeal,
         endomorphismRing,endomorphismRingGens,
         minimizeRelations,checkHomRelations,
         skewPolynomialRing,
	 abelianization,
	 oppositeRing,
         quadraticClosure,
	 homogDual,
	 sparseCoeffs,
	 wallTiming
}

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
    "Basic operations on noncommutative algebras."
    "Using the Bergman interface"
///


-------------------------
----- Types
-------------------------
    
doc ///
   Key
      NCRing
   Headline
      Type of a noncommutative ring.
   Description
      Text
         All noncommutative rings have this as an ancestor type.  It is the parent of the
	 types @ TO NCPolynomialRing @ and @ TO NCQuotientRing @.
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
      Caveat
         At this point, one cannot define quotients of quotients.
///