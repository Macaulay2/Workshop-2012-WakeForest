beginDocumentation()
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

     end
     
     
