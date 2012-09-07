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
	       
	       Here are some examples illustrating the use of this package.
	      
     
      	       
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
     	      A filtered complex is a nested family of chain complexes K = $\dots \supseteq $ K_n $\supseteq$ K_{n-1} $ \supseteq \dots$ such that the following holds:
	      
	      1.  There exists M such that K_N=K_M for all N \geq M.
	      
	      2.  There exists an m such that K_n =0 for all n \leq m.
    ///
    
doc ///
     Key
     	  SpectralSequence
     Headline
     	  The type of all spectral sequences
     Description
     	  Text
	       A spectral sequence consists of the following:
	       
	       1. A sequence of modules \{E^r_{p,q}\}_{p,q \in \ZZ, r \geq 0},
	       
	       2. A collection of homomorphisms \{d^r_{p,q}: E^r_{p,q} $\rightarrow$ E^r_{p-r,q+r-1}}_{p,q \in ZZ, r \geq 0} such that
	       d^r_{p,q} d^r_{p+r,q-r+1} =0, 
	       
	       3. A collection of imorphisms E^{r+1}_{p,q}  $\rightarrow$ ker d^r_{p,q} / image d^r_{p+r,q-r+1}.
	       
	       In Macaulay 2, a spectral sequence is represented by a sequence of spectral sequence pages.
	       
	       
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
     
doc ///
     Key
     	  SpectralSequencePage
     Headline
     	  The type of all spectral sequence pages
     Description
     	  Text
	       A spectral sequence page (or sheet) is the 
	       
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
	       A filtered complex with a filtration of the form
	       K=F_nK > F_(n-1)K > ... > F_0K.
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
     
     
     doc ///
     Key
     	  spectralSequencePage
     Headline
     	  Construct a SpectralPage from a filtered complex
     Usage
     	  E = spectralSequencePage(K,r)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
	       r: an integer
     Outputs
     	  E:SpectralSequencePage
     Description
     	  Text 
	       Blah
     ///
 
 doc ///
     Key
     	  computeErModules
     Headline
     	  Construct all modules on the r th page of a spectral sequence
     Usage
     	 M= computeErModules(K,r)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
	       r: A non-negative integer
     Outputs
     	M:HashTable
     Description
     	  Text 
	       Blah
     ///
 
 doc ///
     Key
     	  computeErMaps
     Headline
     	  Construct all maps on the r th page of a spectral sequence
     Usage
     	  M=computeErMaps(K,r)
     Inputs
     	  K:FilteredComplex
	       A filtered complex
	       r: A non-negative integer
     Outputs
     	  M:HashTable
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
     	  (max, HashTable)
     Headline
     	  The largest integer valued key in the hash table 
     Usage
     	  m = max(K)
     Inputs
     	  K:HashTable
	       A hash table
     Outputs
     	  m:ZZ
     Description
     	  Text 
	      Returns the largest integer valued key in the hash table
     ///
     
 doc ///
     Key
     	  (min, HashTable)
     Headline
     	  The smallest integer valued key in the hash table 
     Usage
     	  m = min(K)
     Inputs
     	  K:HashTable
	       A hash table
     Outputs
     	  m:ZZ
     Description
     	  Text 
	      Returns the smallest integer valued key in the hash table
     ///     

 doc ///
     Key
     	  (symbol _, SpectralSequence, ZZ)
     Headline
     	  The kth page of a spectral sequence
     Usage
     	  P = E_k
     Inputs
     	  E:SpectralSequence
	  k:ZZ
     Outputs
     	  P: SpectralSequencePage
     Description
     	  Text 
	      Returns the kth page of the spectral sequence
     ///
     
doc ///
     Key
     	  (symbol ^, SpectralSequence, ZZ)
     Headline
     	  The kth page of a spectral sequence
     Usage
     	  P = E^k
     Inputs
     	  E:SpectralSequence
	  k:ZZ
     Outputs
     	  P: SpectralSequencePage
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
     	  (symbol ^, SpectralSequencePage, List)
     Headline
     	  The module in the i,j position on the page
     Usage
     	  M = P^L
     Inputs
     	  P:SpectralSequencePage
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
     	  (symbol _, SpectralSequencePage, List)
     Headline
     	  The module in the i,j position on the page
     Usage
     	  M = P_L
     Inputs
     	  P:SpectralSequencePage
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
          (symbol _, FilteredComplex, ZZ)
	  (symbol _, FilteredComplex, InfiniteNumber)
     Headline
     	  The filtered pieces
     Usage
     	  C = K_j
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
     
     
