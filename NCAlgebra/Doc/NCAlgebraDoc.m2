beginDocumentation()

undocumented { (describe,SpectralSequence),
     	       (expression,SpectralSequence),
	       (net, FilteredComplex),
	       (net, SpectralSequence)}

 document {
     Key => {SpectralSequences},
     Headline => "A package for working with spectral sequences",
    PARA { "SpectralSequences is a package to work with spectral sequences
	 associated to a filterd complex." },
     }

--doc ///
--     Key 
--     	  SpectralSequences
--     Headline
--     	  A package for working with spectral sequences
--     Description
--     	  Text 
--	      "SpectralSequences" is a package to work with spectral sequences
--	       associated to a filtered complex. 
	       
--	       Here are some examples illustrating the use of this package.
	      
     
      	       
  ---  ///

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
	      
	      1.  There exists an integer max such that K_n=K_{max} for all n \geq max.
	      
	      2.  There exists an integer min such that K_n =0 for all n \leq min.
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
	       
	       3. A collection of isomorphisms E^{r+1}_{p,q}  $\rightarrow$ ker d^r_{p,q} / image d^r_{p+r,q-r+1}.
	       
	       In Macaulay 2, a spectral sequence is represented by a sequence of spectral sequence pages.
	       
	       
     ///
     
--doc ///
--     Key
--     	  SpectralSequenceSheet
--     Headline
--     	  The type of all spectral sequence sheets
--     Description
--     	  Text
	     --  A spectral sequence sheet (or page) is the 
	       
  --   ///	       
     
doc ///
     Key
     	  SpectralSequencePage
     Headline
     	  The type of all spectral sequence pages
     Description
     	  Text
	       A spectral sequence page (or sheet) with page number r (for a 
		    fixed integer r $\geq$ 0) is 
	       collection E^r:=\{E^r_{p,q}, d^r_{p,q}\}_{p,q\in \ZZ} such that:
	       
	       1. E^r_{p,q} are
	       modules,
	       
	       2. d^r_{p,q}:E^r_{p,q}$\rightarrow$ E^r_{p-r,q+r-1} are homomorphisms,
	       
	       3. and d^r_{p,q} d^r_{p+r,q-r+1}=0.
	       
     ///	       

doc ///
     Key 
          (max,ChainComplex)
     Headline 
         compute maximum of the spots of a chain complex
     Usage 
        N = max C 
     Inputs 
	  C: ChainComplex
     Outputs
          N: ZZ
     Description	  
     	  Text
	     Produces the largest homological degree which
	     computer explicitly remembers.
	     
	  Example 
	    needsPackage "SpectralSequences"
	    A = QQ[x,y]
	    C = res ideal vars A
	    spots C
	    N = max C
     	    support C
	    D = truncate(C,-1)
	    spots D
	    max D
	    support D
     SeeAlso
      	  (spots, ChainComplex) 
	  (support, ChainComplex)
	  (min, ChainComplex)	    	  
    /// 
