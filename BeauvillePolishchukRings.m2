newPackage(
	"BeauvillePolishchukRings",
    	Version => "1.0",
    	Date => "August 5, 2012",
    	Authors => {{Name => "Maxim Arap", 
		  Email => "marap@math.jhu.edu", 
		  HomePage => "http://www.math.jhu.edu/~marap"},
                  {Name => "David Swinarski", 
		  Email => "dswinarski@fordham.edu ", 
		  HomePage => "http://www.math.uga.edu/~davids"}                   },
    	Headline => "Construction of tautological rings of cycles on Jacobian and Prym varieties and operators on them",
    	DebuggingMode => true
        )
   
-- Load package for documentation   
needsPackage"SimpleDoc"   

-------------------------------------------------------------------------------

{*
Copyright [2012] [Maxim Arap, David Swinarski]

This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation; either version 2 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with this program; if not, see <http://www.gnu.org/licenses/>
*}


{*

      Installation:

      Put the file TautRings.m2 somewhere into the path of Macaulay2      
      (usually into the directory .Macaulay2/code inside your home directory, type
      path in M2 to see the path) and do inside M2

      installPackage "TautRings"
   

*}



export{"modelRing","beauvillePolishchukRing","AbelianVarietyType"}



if version#"VERSION" < "1.4" then error "This package was written for Macaulay2 Version 1.4 or higher.";



----------------------------------------------------------------------------------
-- Public functions
----------------------------------------------------------------------------------
modelRing=method(TypicalValue => PolynomialRing, Options=>{AbelianVarietyType=>"Jacobian"})
modelRing ZZ := opts -> g -> (
       x:=getSymbol("x");
       variables:=toList (x_1..x_(g-1));
       degs:=apply(g-1,i->{i+1,i});
       S:=QQ[variables,Degrees=>degs];
       S#"AbelianVarietyType"=opts.AbelianVarietyType;
       return S
       )

TEST ///
debug TautRings
--R=QQ[x_1..x_9]
--assert(isContiguous {x_2,x_3,x_6,x_4,x_5,x_8,x_7})
--assert(not isContiguous {x_1,x_2,x_5,x_3})
///

beauvillePolishchukRing=method(TypicalValue=>Ring, Options=>{AbelianVarietyType=>"Jacobian"})
beauvillePolishchukRing ZZ := opts -> g -> (
       S:=modelRing(g);
       I:=ideal(S_0);
       R:=S/I;
       R#"AbelianVarietyType"=opts.AbelianVarietyType;
       return R
       )
  
  
----------------------------------------------------------------------------------
-- Private functions
----------------------------------------------------------------------------------

-- Converts a monomial in a polynomial ring to a list. 
-- The first variable in the ring (usually x_1) plays a special role. 
-- Examples: x_1*x_3->{1,3}; x_2*x_3^2 -> {0,2,3,3}; x_1^2*x_2^2*x_3^3 -> {2,2,2,3,3,3}
monomialToList = (m) -> (
e:=flatten exponents(m);
n:=e_0;
e=drop(e,{0,0});
ans:=flatten apply(#e, i ->apply(e_i,j-> i+2));
return prepend(n,ans)
)

-- Converts a list L to a monomial in the ring R. 
-- The first variable in the list plays a special role.
-- Examples: {1,3} -> x_1*x_3; {0,2,3,3} -> x_2*x_3^2; {2,2,2,3,3,3} -> x_1^2*x_2^2*x_3^3
listToMonomial = (L,R) -> (
if #L==0 then return 0;
v:=gens R;
ans:=(v_0)^(L_0);
L=drop(L,{0,0});
T:=pairs tally(L);
ai:=0;
bi:=0;
for i from 0 to #T-1 do (
ai=T_i_0;
bi=T_i_1;
ans=ans*(v_(ai-1))^(bi)
);
return ans
)

-- Polishchuk D operator for Jacobians for monomials only. 
-- Input: list L that represents the monomial and the dimension g of the Jacobian.
-- Output: list of lists, each of which consists of a list representing a monomial and an integer 
-- representing the coefficient in front of that monomial
-- Example: monomialD({1,2,3},5) returns {{{0, 2, 3}, 2}, {{1, 4}, 10}} 
-- which means: 2*x_2*x_3+10*x_1*x_4.
monomialD = (L,g) -> (
n:=L_0;
L=drop(L,{0,0});
k:=#L;
Lhat:={};
ans:={};
ni:=0;
nj:=0;
--first term
if n>0 then (
ans=append(ans,{prepend(n-1,L), n*(-g-1+n+k+sum L)}));
--second term
for i from 0 to #L-2 do (
for j from i+1 to #L-1 do (
ni=L_i;
nj=L_j;
Lhat=drop(drop(L,{j,j}),{i,i});
Lhat=sort append(Lhat,ni+nj-1);
Lhat=prepend(n,Lhat);
ans=append(ans, {Lhat,binomial(ni+nj,ni)})
));
return ans
)



----------------------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------------------

beginDocumentation()

doc ///
  Key
    BeauvillePolishchukRings
  Headline
    Construction of tautological rings of cycles on Jacobian and Prym varieties and operators on them
  Description
    Text
      This package implements the construction of model tautological rings of cycles on Jacobian and Prym varieties modulo 
      algebraic equivalence. Tautological rings of Jacobians and Pryms contain the classes of essentially all known 
      algebraic cycles on these varieties and are fundamental objects in the study of cycles on abelian varieties.  
      The model tautological ring of a Jacobian was constructed in [P05] and surjects onto the tautological ring of a Jacobian. 
      The surjection is conjecturally an isomorphism for the generic Jacobian. The analogous construction and the conjecture have 
      been carried out in [A11]. The Hilbert function of the model tautological ring of a Jacobian has a beautiful conjectural 
      description due to van der Geer and Kouvidakis, see [M09]. The van der Geer-Kouvidakis conjecture has a strong form that 
      gives a basis for the bi-graded pieces of the model tautological ring. Our package provides the tools for verifying these 
      conjectures.    
      
      The Chow group of algebraic 1-cycles modulo algebraic equivalence on a generic abelian 3-fold is known to be not 
      finite dimesional. FIXME
            
--      We provide a general command @TO modelTautologicalRing@ for the construction of the model tautological ring of a Jacobian 
      variety (and, with an optional argument, of a Prym variety). FIXME 
      
    
      {\bf References:}

      For tautological rings and model tautological rings see:

      [A11] {\it M. Arap, Tautological rings of Prym varieties, University of Georgia, PhD thesis (2011)}. 

      [A12] {\it M. Arap, Algebraic cycles on Prym varieties, Math. Ann. 353 (2012), 707-726}.

      [B04] {\it A. Beauville, Algebraic cycles on Jacobian varieties, Compositio Math. 140  (2004),  no. 3, 683-688}.

      [M09] {\it  B. Moonen, Relations between tautological cycles on Jacobians. Comment. Math. Helv. 84 (2009), no. 3, 471-502}. 

      [P05] {\it A. Polishchuk, Universal algebraic equivalences between tautological cycles on Jacobians of curves.  Math. Z. 251 (2005), 875-897}. 


      {\bf Examples:}

--      @TO "Jacobian 10-fold"@  -- Model tautological ring of a Jacobian 10-fold

--      @TO "Prym 9-fold"@  -- Model tautological ring of a Prym 9-fold


      
      {\bf Key user functions:}

      {\it The main function of the package is:}

--      @TO modelTautologicalRing@  -- The construction of the model tautological ring of a Jacobian or Prym 


      {\it An essentail tool for studying tautological cycles is the function that computes the:}

--      @TO FourierTransform@ -- Compute the Fourier Trasnform of a tautological cycle


      {\it Other essential functions used in the construction of tautological rings are:}

--      @TO PolishchukD@  --  Polishchuk differential operator used to generate relations in the tautological ring

--      @TO vdGKbasis@  -- van der Geer-Kouvidakis basis for the bi-graded piece of the tautological ring

///



doc ///
  Key
    (modelRing, ZZ)
    modelRing
  Headline
    Construct the bi-graded polynomial ring that is the ambient ring for the Beauville-Polishchuk ring.
  Usage
    modelRing(g)

  Inputs
    g:ZZ
        dimension of the abelian variety
  Outputs
    :PolynomialRing
  Description
   Text
    Construct the bi-graded polynomial ring that is the ambient ring for the Beauville-Polishchuk ring.
   Example
     modelRing(10)
     modelRing(9,AbelianVarietyType=>"Prym")
     
  SeeAlso
   beauvillePolishchukRing
///

doc ///
  Key
    (beauvillePolishchukRing, ZZ)
    beauvillePolishchukRing
  Headline
    Construct the Beauville-Polishchuk ring of an abelian variety (default: "Jacobian") of dimension g. 
  Usage
    beauvillePolishchukRing(g)
  Inputs
    g:ZZ
        dimension of the abelian variety
  Outputs
    :Ring
  Description
   Text
    Construct the Beauville-Polishchuk ring of an abelian variety (default: "Jacobian") of dimension g. 
   Example
     beauvillePolishchukRing(10)
     beauvillePolishchukRing(9, AbelianVarietyType=>"Prym")
     
  SeeAlso
   modelRing
///

doc ///
  Key
    AbelianVarietyType
  Headline
    Option to specify the type of abelian variety. 
  Description
    Text
      @TO Option@ to specify the type of abelian variety.

      It takes @TO String@ value "Jacobian" or "Prym" (default is "Jacobian").
///


doc ///
  Key
    [modelRing, AbelianVarietyType]
  Headline
    Option to specify the type of abelian variety whose modelRing will be created.
  Description
   Text
    @TO Option@ to specify the type of abelian variety whose modelRings will be created.

    It takes @TO String@ value "Jacobian" or "Prym" (default is "Jacobian").
///


doc ///
  Key
    [beauvillePolishchukRing, AbelianVarietyType]
  Headline
    Option to specify the type of abelian variety whose beauvillePolishchukRing will be created.
  Description
   Text
    @TO Option@ to specify the type of abelian variety whose beauvillePolishchukRing will be created.

    It takes @TO String@ value "Jacobian" or "Prym" (default is "Jacobian").
///