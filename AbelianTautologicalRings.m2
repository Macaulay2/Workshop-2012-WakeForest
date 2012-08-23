newPackage(
	"AbelianTautologicalRings",
    	Version => "1.0",
    	Date => "August 5, 2012",
    	Authors => {{Name => "Maxim Arap", 
		  Email => "marap@math.jhu.edu", 
		  HomePage => "http://www.math.jhu.edu/~marap"},
                  {Name => "David Swinarski", 
		  Email => "dswinarski@fordham.edu ", 
		  HomePage => "http://www.math.uga.edu/~davids"}                   },
    	Headline => "Construction of model tautological rings of cycles on Jacobian and Prym varieties and operators on them",
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

      Start M2 in the directory containing this file and type

           installPackage "AbelianTautologicalRings"

      Then the package will be usable when M2 is started in any directory, and this file can
      be moved or deleted.

*}



export{"modelRing","abelianTautologicalRing","polishchukD","polishchukDelta","AbelianVarietyType","IndexedVariableName"}
export{"monomialToList", "listToMonomial","monomialFourierTransform","fourierTransform","listDelta"}


if version#"VERSION" < "1.4" then error "This package was written for Macaulay2 Version 1.4 or higher.";



----------------------------------------------------------------------------------
-- Public functions
----------------------------------------------------------------------------------
modelRing=method(TypicalValue => PolynomialRing, Options=>{AbelianVarietyType=>"Jacobian",IndexedVariableName=>"x"})
modelRing ZZ := opts -> g -> (
       w:=null;
       if opts#?IndexedVariableName then w=getSymbol(opts.IndexedVariableName) else w=getSymbol("x");
       variables:=toList (w_1..w_(g-1));
       degs:=apply(g-1,i->{i+1,i});
       S:=QQ[variables,Degrees=>degs];
       S#"AbelianVarietyType"=opts.AbelianVarietyType;
       S#"Dim"=g;
       return S
       )

TEST ///
debug AbelianTautologicalRings
assert(modelRing(5) === QQ[x_1,x_2,x_3,x_4])
assert(modelRing(5,AbelianVarietyType=>"Prym") === QQ[x_1,x_2,x_3,x_4])
///

abelianTautologicalRing=method(TypicalValue=>Ring, Options=>{AbelianVarietyType=>"Jacobian",IndexedVariableName=>"x"})
abelianTautologicalRing ZZ := opts -> g -> (
if g < 0 then error "The dimension of the abelian variety must be positive.";     
S:=null;
if opts#?IndexedVariableName then S=modelRing(g,IndexedVariableName=>opts.IndexedVariableName) else S=modelRing(g);
if g < 2 then return S;
--generate Polishchuk relations       
trivialRels:={}; 
Rels:={}; 
allRels:={};
for j from 1 to g do (
     --get trivial relations of degree j
     trivialRels=flatten entries basis({g,j},S);
     for i from 0 to g do (
	  --generate Polishchuk relations of codimension i from trivial relations
	  Rels=apply(#trivialRels, t->polishchukD(trivialRels_t, i));
	  for k from 0 to #Rels-1 do (
	       if Rels_k != 0 then allRels=append(allRels, Rels_k)
	       )
	  )
);
I:=ideal(allRels);
R:=S/(sub(I,S));
R#"AbelianVarietyType"=opts.AbelianVarietyType;
R#"Dim"=g;
return R
)

--print part of Moonen diamond (unformatted):

--L=apply(S#"Dim"+1, j->apply(j+1, i->hilbertFunction({i+S#"Dim"-j,S#"Dim"-j}, S)))
{*
 pp := L -> (
     L1 = apply(L, s -> toString s);
     m = max apply(L1, s -> length s);
     for s in apply(L1, s -> concatenate { (m - length s)//2, s }) do print s
     )
*}
--for j from 0 to S#"Dim" do print for i from S#"Dim"-j to S#"Dim" list hilbertFunction({i,S#"Dim"-j}, S) 

polishchukD=method(TypicalValue=>RingElement)  
polishchukD RingElement := (f) -> (     
S:= ring f;
if f==0 then return 0_S;
g:=0;
mcpairs:={};
if S#?"Dim" then g=S#"Dim" else error "The ring of f is missing the Dim attribute";
M := flatten entries monomials(f);
mcpairs = apply(#M, i -> {M_i,coefficient(M_i,f)});     
ans:=0_S;
mi:=0;
Dmi:=0;
for i from 0 to #M-1 do (
mi=monomialToList(M_i);
Dmi=monomialD(mi,g);
for j from 0 to #Dmi-1 do ( 
ans = ans + (mcpairs_i_1)*(Dmi_j_1)*(listToMonomial(Dmi_j_0,S))     
     ));     
return ans     
     )  

polishchukD (RingElement,ZZ) := (f,n) -> (       
if n < 0 then error "The power of Polishchuk D operator must be a non-negative integer";
if n==0 then return f;
F:=f;
for i from 1 to n do F = polishchukD(F);     
return F
     )

polishchukDelta = method(TypicalValue=>RingElement)  
polishchukDelta RingElement := (f) -> (     
     L:={};
     L=polynomialToList(f);
     L=listDelta(L);
     return listToPolynomial(L, ring f)     
     )

polishchukDelta (RingElement,ZZ) := (f,n) -> (       
if n < 0 then error "The power of Polishchuk Delta operator must be a non-negative integer";
if n==0 then return f;
F:=f;
for i from 1 to n do F = polishchukDelta(F);     
return F
     )
     
     

  
----------------------------------------------------------------------------------
-- Private functions
----------------------------------------------------------------------------------

-- Converts a monomial to a list. 
-- The first variable in the ring (usually x_1) plays a special role. 
-- Examples: x_1*x_3->{1,3}; x_2*x_3^2 -> {0,2,3,3}; x_1^2*x_2^2*x_3^3 -> {2,2,2,3,3,3}
monomialToList = (m) -> (
e:=flatten exponents(m);
n:=e_0;
e=drop(e,{0,0});
ans:=flatten apply(#e, i ->apply(e_i,j-> i+2));
return prepend(n,ans)
)

-- Converts a polynomial ring to a list of lists: {list representing a monomial, coefficient}  
-- Example: 10*x_1*x_3+20*x_1^2*x_3-> {{{2, 3}, 20}, {{1, 3}, 10}}
polynomialToList = (f) -> (
M:={};
M=flatten entries monomials f;
ans:={};
for i from 0 to #M-1 do (
ans=append(ans, {monomialToList(M_i), coefficient(M_i,f)})     
);     
return ans        
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

-- Converts a list of lists: {list representing a monomial, coefficient} to a polynomial in the ring R. 
-- Examples: {{{2,3},10},{{0,2,3},20}}-> 10*x_1^2*x_3  + 20*x_2*x_3
listToPolynomial = (M,R) -> (
ans:=0;
for i from 0 to #M-1 do (
     ans=ans+M_i_1*listToMonomial(M_i_0,R)
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

--Computes Polishchuk's operator Delta for monomials in list form, [P05, p.883]
--Input: List representing a monomial, as described in listToMonomial
--Output: list of lists, each of which consists of a list representing a monomial and an integer 
--representing the coefficient in front of that monomial: {list representing a monomial, coefficient} 
monomialListDelta = L -> (
if L=={} then return {{{0},0}};
n:=L_0;
L=drop(L,{0,0});
k:=#L;
ans:={};
Lhat:={};
ni:=0;
nj:=0;
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


--Computes Polishchuk's operator Delta for polynomials in list form, [P05, p.883]
--Input: list of lists: {list representing a monomial, coefficient} 
--Output: list of lists: {list representing a monomial, coefficient} 
listDelta = method(TypicalValue=>List)
listDelta(List) := (M) -> (
ans:={};
for i from 0 to #M-1 do (
mi:=M_i_0;
Deltami:=monomialListDelta(mi);
for t from 0 to #Deltami-1 do (
ans=append(ans, {Deltami_t_0, (M_i_1)*(Deltami_t_1)})     
     ));     
return ans     
     )

--Computes n^{th} power of Polishchuk's operator Delta in list form, [P05, p.883]
--Input: list of lists, each of which consists of a list representing a monomial and an integer 
--representing the coefficient in front of that monomial: {list representing a monomial, coefficient} 
--Output: list of lists, each of which consists of a list representing a monomial and an integer 
--representing the coefficient in front of that monomial: {list representing a monomial, coefficient} 
listDelta(List,ZZ) := (L,n) -> (     
if n < 0 then error "The power of Polishchuk Delta operator must be a non-negative integer";
if n==0 then return L;
for i from 1 to n do L=listDelta(L);     
return L
)       


--input: monomial with no w_1 term, where w_1 stands for the first
--variable in the modelRing
monomialFourierTransformNoFirstVariable = (m) -> (
     S:=ring m;
     if S#?"Dim" then g:=S#"Dim" else error "The ring of the monomial is expected to have Dim attirbute.";
     L:=monomialToList(m);
     n:=L_0;
     if n != 0 then error "Input monomial should have no first variable of the ring.";
     k:=#L-1;
     sumni:= sum(L);
     ans:=0;
     jterm:={};
     for j from 0 to k-1 do (
	  if j+g-k-sumni >= 0 then (
	       jterm = listDelta({{L,1}},j);
	       print(L,jterm);
	       for t from 0 to #jterm-1 do (     
		    ans=ans + (jterm_t_1)*(S_0^(j+g-k-sumni))*(1/(j+g-k-sumni)!)*(1/j!)*(listToMonomial(jterm_t_0,S)) 
		    )
	       )
	  );
     return ans    
     )

monomialFourierTransform = (m) -> (
     S:=ring m;
     if S#?"Dim" then g:=S#"Dim" else error "The ring of the monomial is expected to have Dim attirbute.";
     E:=flatten exponents(m);
     n:=E_0;
     if n==0 then return monomialFourierTransformNoFirstVariable(m);
     if n>0 then m=lift(m/(S_0^n),S);
     return polishchukD(monomialFourierTransformNoFirstVariable(m),n)     
     )

{*
monomialListFourierTransform = (L,S) -> (
     m:=listToPolynomial(L,S);
     return monomialFourierTransform(m)     
     )
*}

fourierTransform = (f)-> (
     S:=ring f;
     mons:=flatten entries monomials f;
     ans:=0_S;
     for k from 0 to #mons-1 do (
	  ans=ans+coefficient(mons_k,f)*monomialFourierTransform(mons_k)
	  );
     return ans
     )
----------------------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------------------

beginDocumentation()

doc ///
  Key
    AbelianTautologicalRings
  Headline
    Construction of tautological rings of cycles on Jacobian and Prym varieties and operators on them
  Description
    Text
      This package implements the construction of model tautological rings of cycles on Jacobian and Prym varieties modulo 
      algebraic equivalence. Tautological rings of Jacobians and Pryms contain the classes of essentially all known 
      algebraic cycles on these varieties and are fundamental objects in the study of cycles on abelian varieties.  
      The model tautological ring of a Jacobian was constructed in [P05] and surjects onto the tautological ring of a Jacobian. 
      The surjection is conjecturally an isomorphism for the generic Jacobian. The analogous construction for Prym varieties  
      been carried out in [A11]. The Hilbert function of the model tautological ring of a Jacobian has a beautiful conjectural 
      description due to van der Geer and Kouvidakis, see [M09]. The van der Geer-Kouvidakis conjecture has a strong form that 
      gives a basis for the bi-graded pieces of the model tautological ring. Our package provides the tools for verifying these 
      conjectures experimentally.    
      
--      The Chow group of algebraic 1-cycles modulo algebraic equivalence on a generic abelian 3-fold is known to be not 
--      finite dimesional. FIXME
            
--      We provide a general command @TO modelTautologicalRing@ for the construction of the model tautological ring of a Jacobian 
--      variety (and, with an optional argument, of a Prym variety). FIXME 
      
    
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


      {\it An essential tool for studying tautological cycles is the function that computes the:}

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
        dimension of the abelian variety.
  Outputs
    :PolynomialRing
  Description
   Text
    Construct the bi-graded polynomial ring that is the ambient ring for the Beauville-Polishchuk ring. Use the option @TO IndexedVariableName@, if necessary, to specify the name of the 
    indexed variable for the model ring (default is "x") to avoid shadowing existing variables. 
   Example
     modelRing(8)
     modelRing(8,IndexedVariableName=>"u")
     modelRing(9,AbelianVarietyType=>"Prym",IndexedVariableName=>"w")
     
     
  SeeAlso
   abelianTautologicalRing
///

doc ///
  Key
    (abelianTautologicalRing, ZZ)
    abelianTautologicalRing
  Headline
    Construct the Beauville-Polishchuk ring. 
  Usage
    abelianTautologicalRing(g)
  Inputs
    g:ZZ
        dimension of the abelian variety
  Outputs
    :Ring
  Description
   Text
    Construct the Beauville-Polishchuk ring of an abelian variety (default: "Jacobian") of dimension g. Use the option @TO AbelianVarietyType@ to change the type of 
    abelian variety for which the Beauville-Polishchuk ring is to be constructed. Use the option @TO IndexedVariableName@, if necessary, to specify the name of the 
    indexed variable for the Beauville-Polishchuk ring (default is "x") to avoid shadowing existing variables. 
   Example
     abelianTautologicalRing(5)
     abelianTautologicalRing(5, AbelianVarietyType=>"Prym")
     abelianTautologicalRing(5, AbelianVarietyType=>"Prym",IndexedVariableName=>"u")
  SeeAlso
   modelRing
///

doc ///
  Key
    polishchukD
    (polishchukD, RingElement)
    (polishchukD, RingElement, ZZ)
  Headline
    Polishchuk D operator. 
  Usage
    polishchukD(f)
    polishchukD(f,n)
  Inputs
    f:RingElement
        an element of a ring returned by @TO modelRing @ or @TO abelianTautologicalRing@.
    n:ZZ
        an integer to specify the number of iterations of the Polishchuk operator to be applied
  Outputs
    :RingElement
  Description
   Text
    Apply the Polishchuk D operator to an element of a polynomial ring, which is the output of @TO modelRing@, see [P05] FIXME. 
   Example
     S=modelRing(5);
     polishchukD(x_1^2*x_2*x_3);
     polishchukD(x_1^2*x_2*x_3,2);
  SeeAlso 
     polishchukDelta
///

doc ///
  Key
    polishchukDelta
    (polishchukDelta, RingElement)
    (polishchukDelta, RingElement, ZZ)
  Headline
    Polishchuk Delta operator. 
  Usage
    polishchukDelta(f)
    polishchukDelta(f,n)
  Inputs
    f:RingElement
        an element of a ring returned by modelRing or abelianTautologicalRing FIXME hyperlink the functions  
    n:ZZ
        an integer to specify the number of iterations of the Polishchuk operator to be applied
  Outputs
    :RingElement
  Description
   Text
    Apply the Polishchuk Delta operator, see [P05] FIXME. 
   Example
     S=modelRing(5);
--     polishchukDelta(x_1^2*x_2*x_3);
--     polishchukDelta(x_1^2*x_2*x_3,2);
  SeeAlso 
     polishchukD
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
    [abelianTautologicalRing, AbelianVarietyType]
  Headline
    Option to specify the type of abelian variety whose abelianTautologicalRing will be created.
  Description
   Text
    @TO Option@ to specify the type of abelian variety whose abelianTautologicalRing will be created.

    It takes @TO String@ value "Jacobian" or "Prym" (default is "Jacobian").
///

doc ///
  Key
    IndexedVariableName
  Headline
    Option to specify the name of the indexed variable. 
  Description
    Text
      @TO Option@ to specify the name of the variable to be used in the output of @TO modelRing@ and @TO abelianTautologicalRing@.

      It takes @TO String@ value, e.g., "w" (default is "x").
///

doc ///
  Key
    [modelRing, IndexedVariableName]
  Headline
    Option to specify the name of the indexed variable. 
  Description
    Text
      @TO Option@ to specify the name of the variable to be used in the output of @TO modelRing@.

      It takes @TO String@ value, e.g., "w" (default is "x").
///

doc ///
  Key
    IndexedVariableName
    [abelianTautologicalRing, IndexedVariableName]
  Headline
    Option to specify the name of the indexed variable. 
  Description
    Text
      @TO Option@ to specify the name of the variable to be used in the output of @TO abelianTautologicalRing@.

      It takes @TO String@ value, e.g., "w" (default is "x").
///
