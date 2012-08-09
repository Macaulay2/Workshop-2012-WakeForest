beginDocumentation()

undocumented { (describe,SpectralSequence),
     	       (expression,SpectralSequence),
	       (net, FilteredComplex),
	       (net, SpectralSequence)}

doc ///
     Key 
     	  SpectralSequences
     Headline
     	  A package for working with spectral sequences
     Description
     	  Text
	       "SpectralSequences" is a package to work with spectral sequences
	       associated to a filtered complex.
	       
    ///

-------------------------
-----Types
-------------------------
    
doc ///
     Key
     	  FilteredComplex
     Headline
     	  The type of all FilteredComplexes
     Description
     	  Text
     	      A filtered complex is
	      
    ///
    
doc ///
     Key
     	  SpectralSequence
     Headline
     	  The type of all spectral sequences
     Description
     	  Text
	       A spectral sequence
	       
     ///
     
doc ///
     Key
     	  SpectralSequenceSheet
     Headline
     	  The type of all spectral sequence sheets
     Description
     	  Text
	       A spectral sequence sheet (or page) is the 
	       
     ///	       
     
-------------------------
-----Functions
-------------------------

doc ///
     Key
     	  filteredComplex
     Headline
     	  Construct a filtered complex
     Usage
     	  K = filteredComplex L
     Inputs
     	  L:List
	       A list of ChainComplexes or SimplicialComplexes
     Outputs
     	  K:FilteredComplex
	       A filtered complex with a descending filtration.
     Description
     	  Text 
	       Blah

     ///
     
     
 doc ///
     Key
     	  spectralSequence
     Headline
     	  Construct a spectralSequence from a filtered complex
     Usage
     	  E = spectralSequence K
     Inputs
     	  K:FilteredComplex
	       A filtered complex
     Outputs
     	  E:SpectralSequence
     Description
     	  Text 
	       Blah
     ///
     
-------------------------
-----Methods
-------------------------
  doc ///
     Key
     	   (filteredComplex, ChainComplex)
     Headline
     	  The filtered complex of the truncated chain complex
     Usage
     	  K = filteredComplex(C)
     Inputs
     	  C:ChainComplex
     Outputs
     	  K:FilteredComplex
     Description
     	  Text 
  ///	 

  doc ///
     Key
     	   (filteredComplex, List)
     Headline
     	  A constructor for filtered complexes
     Usage
     	  K = filteredComplex(L)
     Inputs
     	  L:List
     Outputs
     	  K:FilteredComplex
     Description
     	  Text 
  ///	 

 doc ///
     Key
     	   (filteredComplex, SpectralSequence)
     Headline
     	  The underlying filteredComplex of a Spectral Sequence
     Usage
     	  K = filteredComplex(E)
     Inputs
     	  E:SpectralSequence
     Outputs
     	  f:FilteredComplex
     Description
     	  Text 
	       Blah
    ///

 doc ///
     Key
     	  (max, FilteredComplex)
     Headline
     	  The maximum filtered piece of a filtered complex
     Usage
     	  m = max(K)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
     Outputs
     	  m:ZZ
     Description
     	  Text 
	      Returns the smallest filtered piece
     ///
     
 doc ///
     Key
     	  (min, FilteredComplex)
     Headline
     	  The largest filtered piece of a filtered complex
     Usage
     	  m = min(K)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
     Outputs
     	  m:ZZ
     Description
     	  Text 
	      Returns the largest filtered piece
     ///     

 doc ///
     Key
     	  (symbol _, SpectralSequence, ZZ)
     Headline
     	  The kth sheet of a spectral sequence
     Usage
     	  P = E_k
     Inputs
     	  E:SpectralSequence
	  k:ZZ
     Outputs
     	  P: SpectralSequenceSheet
     Description
     	  Text 
	      Returns the kth page of the spectral sequence
     ///

 doc ///
     Key
     	  (spectralSequence, FilteredComplex)
     Headline
     	  Construct a spectralSequence from a filtered complex
     Usage
     	  E = spectralSequence K
     Inputs
     	  K:FilteredComplex
	       A filtered complex
     Outputs
     	  E:SpectralSequence
     Description
     	  Text 
	       Blah
    ///
 
  doc ///
     Key
     	  (symbol ^, SpectralSequenceSheet, List)
     Headline
     	  The module in the i,j position on the sheet
     Usage
     	  M = P^L
     Inputs
     	  P:SpectralSequenceSheet
	  L:List
	       A list L = \{i,j\} of integers
     Outputs
     	  M:Module
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
     	  (inducedMap, FilteredComplex, ZZ)
     Headline
     	  The ith inclusion map in a filtered complex
     Usage
     	  f = inducedMap(K,i)
     Inputs
     	  K:FilteredComplex
	  i:ZZ
     Outputs
     	  f:ChainComplexMap
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
     	   (Hom, FilteredComplex, ChainComplex)
	   (Hom, ChainComplex, FilteredComplex)
     Headline
     	  The ith inclusion map in a filtered complex
     Usage
     	  f = Hom(K,C)
     Inputs
     	  K:FilteredComplex
	  C:ChainComplex
     Outputs
     	  f:FilteredComplex
     Description
     	  Text 
	       Blah
    ///
     
 


  doc ///
     Key
  	  (chainComplex, FilteredComplex)
     Headline
     	  The biggest complex in a filtered complex
     Usage
     	  C = chainComplex K
     Inputs
     	  K:FilteredComplex
     Outputs
     	  C:ChainComplex
     Description
     	  Text 
	       Blah
    ///
    
      doc ///
     Key
     	   (chainComplex, SpectralSequence)
     Headline
     	  The underlying chain complex of a Spectral Sequence
     Usage
     	  K = chainComplex E
     Inputs
     	  E:SpectralSequence
     Outputs
     	  K:ChainComplex
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
     	   (symbol **, ChainComplex, FilteredComplex)
	   (symbol **, FilteredComplex, ChainComplex)
     Headline
     	  filtered Tensor product of complexes
     Usage
     	  KK = C ** K
     Inputs
     	  C:ChainComplex
	  K:FilteredComplex
     Outputs
     	  KK:FilteredComplex
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
     	   (symbol == , FilteredComplex, FilteredComplex)
     Headline
     	  Equality of filtered complexes
     Usage
     	  a = K == L
     Inputs
     	  K:FilteredComplex
	  L:FilteredComplex
     Outputs
     	  a:Boolean
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
          (symbol ^, FilteredComplex, ZZ)
	  (symbol ^, FilteredComplex, InfiniteNumber)
     Headline
     	  The filtered pieces
     Usage
     	  C = K^j
     Inputs
     	  K:FilteredComplex
	  j:ZZ 
	       an integer, infinity, or -infinity
     Outputs
     	  C:ChainComplex
     Description
     	  Text 
	       Blah
    ///

  doc ///
     Key
     	   (see, FilteredComplex)
	   (see)
     Headline
     	  Displays the components of a filtered complex
     Usage
          a = see K     	  
     Inputs
     	  K:FilteredComplex
     Outputs
     	  a:Net
     Description
     	  Text 
	       Blah
    ///

     end
     
     
