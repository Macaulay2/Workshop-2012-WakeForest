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



export{"modelRing","abelianTautologicalRing","polishchukD","polishchukDelta","fourierTransform","AbelianVarietyType","IndexedVariableName","moonenDiamond"}


if version#"VERSION" < "1.4" then error "This package was written for Macaulay2 Version 1.4 or higher.";



----------------------------------------------------------------------------------
-- Public functions
----------------------------------------------------------------------------------
modelRing=method(TypicalValue => PolynomialRing, Options=>{AbelianVarietyType=>"Jacobian",IndexedVariableName=>"x"})
modelRing ZZ := opts -> g -> (
       w:=null;
       n:=0;
       S:=null;
       variables:=null;
       degs:=null;
       w=getSymbol(opts.IndexedVariableName);
       if opts.AbelianVarietyType=="Prym" then (
	    if (g % 2)==0 then n=lift(g/2,ZZ) else n=lift((g-1)/2,ZZ);
	    variables=apply(n,i->w_(2*i+1));
	    degs=apply(n,i->{2*i+1,2*i});
	    S=QQ[variables,Degrees=>degs];
	    S#"AbelianVarietyType"=opts.AbelianVarietyType;
	    S#"Dim"=g;
	    return S
	    )
       else if opts.AbelianVarietyType=="Jacobian" then (
	    variables=toList (w_1..w_(g-1));
	    degs=apply(g-1,i->{i+1,i});
	    S=QQ[variables,Degrees=>degs];
	    S#"AbelianVarietyType"=opts.AbelianVarietyType;
	    S#"Dim"=g;
	    return S
	    )
       else error("AbelianVarietyType must be either Jacobian or Prym.")
       )

TEST ///
debug AbelianTautologicalRings
assert(modelRing(5) === QQ[x_1,x_2,x_3,x_4])
assert(modelRing(5,IndexedVariableName=>"y") === QQ[y_1,y_2,y_3,y_4])
assert(modelRing(5,AbelianVarietyType=>"Prym") === QQ[x_1,x_3])
///

abelianTautologicalRing=method(TypicalValue=>Ring, Options=>{AbelianVarietyType=>"Jacobian",IndexedVariableName=>"x"})
abelianTautologicalRing ZZ := opts -> g -> (
     if g < 0 then error "The dimension of the abelian variety must be positive.";     
     -- if AbelianVarietyType is not "Prym" or "Jacobian", modelRing will throw an error
     S:=modelRing(g,AbelianVarietyType=>opts.AbelianVarietyType,IndexedVariableName=>opts.IndexedVariableName);
     if g < 2 then return S;
     --generate Polishchuk relations       
     trivialRels:={}; 
     Rels:={}; 
     allRels:={};
     R:=null;
     I:=null;
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
     --monomial generators for relations that hold for codimension reasons
     T:= flatten entries gens truncate(g+1, S^1); 
     I=ideal(join(allRels,T));
     R=S/(sub(I,S));
     R#"AbelianVarietyType"=opts.AbelianVarietyType;
     R#"Dim"=g;
     return R	  
     )

moonenDiamond = S -> (
     if not S#?"Dim" then error "The ring is missing the Dim attribute.";
     L:=apply(S#"Dim"+1, j->apply(j+1, i->hilbertFunction({i+S#"Dim"-j,S#"Dim"-j}, S)));
     gSzPrint(L)
     )

polishchukD=method(TypicalValue=>RingElement)  
polishchukD RingElement := (f) -> (     
     S:= ring f;
     if not S#?"AbelianVarietyType" then error "The ring of f is missing the AbelianVarietyType attribute";
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
	  mi=monomialToList(M_i,AbelianVarietyType=>S#"AbelianVarietyType");
	  Dmi=monomialD(mi,g,AbelianVarietyType=>S#"AbelianVarietyType");
	  for j from 0 to #Dmi-1 do ( 
	       ans = ans + (mcpairs_i_1)*(Dmi_j_1)*(listToMonomial(Dmi_j_0,S,AbelianVarietyType=>S#"AbelianVarietyType"))
	       )
	  );     
     return ans     
     )  

polishchukD (RingElement,ZZ) := (f,n) -> (       
     if n < 0 then error "The power of Polishchuk D operator must be a non-negative integer";
     if n==0 then return f;
     F:=f;
     for i from 1 to n do F = polishchukD(F);     
     return F
     )

--polishchukDelta operator for Jacobians can be reused for Pryms
--see [A11, p.32] for the defition of polishchukDelta in the Prym case 
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
 
fourierTransform = f -> (
     S:=ring f;
     if not S#?"AbelianVarietyType" then error "The ring of f is missing the AbelianVarietyType attribute";

     mons:=flatten entries monomials f;
     ans:=0_S;
     for k from 0 to #mons-1 do (
	  ans=ans+coefficient(mons_k,f)*monomialFourierTransform(mons_k,AbelianVarietyType=>S#"AbelianVarietyType")
	  );
     return ans
     ) 
----------------------------------------------------------------------------------
-- Private functions
----------------------------------------------------------------------------------

-- Converts a monomial to a list. 
-- The first variable in the ring (usually x_1) plays a special role. 
-- Examples: x_1*x_3->{1,3}; x_2*x_3^2 -> {0,2,3,3}; x_1^2*x_2^2*x_3^3 -> {2,2,2,3,3,3}
monomialToList=method(TypicalValue=>List,Options=>{AbelianVarietyType=>"Jacobian"})
monomialToList RingElement := opts -> m -> (
     e:=flatten exponents(m);
     n:=e_0;
     e=drop(e,{0,0});
     ans:=null;
     if opts.AbelianVarietyType=="Prym" then ans=flatten apply(#e, i->apply(e_i,j->2*i+3))
     else if opts.AbelianVarietyType=="Jacobian" then ans=flatten apply(#e, i->apply(e_i,j->i+2));     
     return prepend(n,ans)
     )

-- Converts a polynomial ring to a list of lists: {list representing a monomial, coefficient}  
-- Example: 10*x_1*x_3+20*x_1^2*x_3-> {{{2, 3}, 20}, {{1, 3}, 10}}
polynomialToList=method(TypicalValue=>List,Options=>{AbelianVarietyType=>"Jacobian"})
polynomialToList RingElement := opts -> f -> (
     M:={};
     M=flatten entries monomials f;
     ans:={};
     for i from 0 to #M-1 do (
	  ans=append(ans, {monomialToList(M_i,AbelianVarietyType=>opts.AbelianVarietyType), coefficient(M_i,f)})     
	  );     
     return ans        
     )

-- Converts a list L to a monomial in the ring R. 
-- The first variable in the list plays a special role.
-- If the list contains an index that exceeds the number of generators of R, the method returns 0
-- Examples: {1,3} -> x_1*x_3; {0,2,3,3} -> x_2*x_3^2; {2,2,2,3,3,3} -> x_1^2*x_2^2*x_3^3
listToMonomial=method(TypicalValue=>RingElement,Options=>{AbelianVarietyType=>"Jacobian"})
listToMonomial (List, Ring) := opts -> (L,R) -> (
     if #L==0 then return 0;
     v:=gens R;
     ans:=(v_0)^(L_0);
     L=drop(L,{0,0});
     T:=pairs tally(L);
     ai:=0;
     bi:=0;
     for i from 0 to #T-1 do (
	  if opts.AbelianVarietyType=="Prym" then ai=lift((T_i_0+1)/2,ZZ)
	  else if opts.AbelianVarietyType=="Jacobian" then ai=T_i_0;
	  bi=T_i_1;
	  if ai-1 <= #v-1 then ans=ans*(v_(ai-1))^(bi) else ans=0_R
	  );
     return ans
     )

-- Converts a list of lists: {list representing a monomial, coefficient} to a polynomial in the ring R. 
-- Examples: {{{2,3},10},{{0,2,3},20}}-> 10*x_1^2*x_3  + 20*x_2*x_3
listToPolynomial=method(TypicalValue=>RingElement,Options=>{AbelianVarietyType=>"Jacobian"})
listToPolynomial (List,Ring) := opts -> (M,R) -> (
     ans:=0;
     for i from 0 to #M-1 do (
	  ans=ans+M_i_1*listToMonomial(M_i_0,R,AbelianVarietyType=>opts.AbelianVarietyType)
	  );
     return ans
     )


-- Polishchuk D operator for Jacobians for monomials only. 
-- Input: list L that represents the monomial and the dimension g of the Jacobian.
-- Output: list of lists, each of which consists of a list representing a monomial and an integer 
-- representing the coefficient in front of that monomial
-- Example: monomialD({1,2,3},5) returns {{{0, 2, 3}, 2}, {{1, 4}, 10}} 
-- which means: 2*x_2*x_3+10*x_1*x_4.
monomialD=method(TypicalValue=>List, Options=>{AbelianVarietyType=>"Jacobian"})
monomialD (List, ZZ) := opts -> (L,g) -> (
     n:=L_0;
     L=drop(L,{0,0});
     k:=#L;
     Lhat:={};
     ans:={};
     ni:=0;
     nj:=0;
     -- if AbelianVarietyType is "Prym" use the formula from [A11, Prop.3.3.4, p.31] 
     -- else if AbelianVarietyType is "Jacobian" use the formula from [Po05, Prop.2.6, p.883]
     if opts.AbelianVarietyType=="Prym" then (
	  --first term
	  if n>0 then (
	       ans=append(ans,{prepend(n-1,L), 2*n*(-g-1+n+k+sum L)})
	       );
	  --second term
	  for i from 0 to #L-2 do (
	       for j from i+1 to #L-1 do (
		    ni=L_i;
		    nj=L_j;
		    Lhat=drop(drop(L,{j,j}),{i,i});
		    Lhat=sort append(Lhat,ni+nj-1);
		    Lhat=prepend(n,Lhat);
		    ans=append(ans, {Lhat,2*binomial(ni+nj,ni)})
		    )
	       );
	  return ans
	  )
     else if opts.AbelianVarietyType=="Jacobian" then (
	  --first term
	  if n>0 then (
	       ans=append(ans,{prepend(n-1,L), n*(-g-1+n+k+sum L)})
	       );
	  --second term
	  for i from 0 to #L-2 do (
	       for j from i+1 to #L-1 do (
		    ni=L_i;
		    nj=L_j;
		    Lhat=drop(drop(L,{j,j}),{i,i});
		    Lhat=sort append(Lhat,ni+nj-1);
		    Lhat=prepend(n,Lhat);
		    ans=append(ans, {Lhat,binomial(ni+nj,ni)})
		    )
	       );
	  return ans
	  )
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
	       )
	  );
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
	       )
	  );     
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


--input: monomial with no x_1 term, where x_1 stands for the first
--variable in the modelRing
monomialFourierTransformNoFirstVariable=method(TypicalValue=>RingElement, Options=>{AbelianVarietyType=>"Jacobian"})
monomialFourierTransformNoFirstVariable RingElement := opts -> m -> (
     S:=ring m;
     if S#?"Dim" then g:=S#"Dim" else error "The ring of the monomial is expected to have Dim attirbute.";
     L:=monomialToList(m,AbelianVarietyType=>opts.AbelianVarietyType);
     n:=L_0;
     if n != 0 then error "Input monomial should have no first variable of the ring.";
     k:=#L-1;
     sumni:= sum(L);
     ans:=0;
     jterm:={};
     
     --note: the fourierTransform formula for Pryms has an additional multiplier of 2^j inside of the summation on j 
     if opts.AbelianVarietyType=="Prym" then (
	  for j from 0 to k-1 do (
	       if j+g-k-sumni >= 0 then (
		    jterm = listDelta({{L,1}},j);
		    for t from 0 to #jterm-1 do (     
			 ans=ans + 2^j*(jterm_t_1)*(S_0^(j+g-k-sumni))*(1/(j+g-k-sumni)!)*(1/j!)*(listToMonomial(jterm_t_0,S,AbelianVarietyType=>"Prym")) 
			 )
		    )
	       )
	  )
     else if opts.AbelianVarietyType=="Jacobian" then (
	  for j from 0 to k-1 do (
	       if j+g-k-sumni >= 0 then (
		    jterm = listDelta({{L,1}},j);
		    for t from 0 to #jterm-1 do (     
			 ans=ans + (jterm_t_1)*(S_0^(j+g-k-sumni))*(1/(j+g-k-sumni)!)*(1/j!)*(listToMonomial(jterm_t_0,S)) 
			 )
		    )
	       )
	  )
     else print("AbelianVarietyType option should be Jacobian or Prym.");
     return ans    
     )

monomialFourierTransform=method(TypicalValue=>RingElement, Options=>{AbelianVarietyType=>"Jacobian"})
monomialFourierTransform RingElement := opts -> m -> (
     S:=ring m;
     if S#?"Dim" then g:=S#"Dim" else error "The ring of the monomial is expected to have Dim attirbute.";
     E:=flatten exponents(m);
     n:=E_0;
     if n==0 then return monomialFourierTransformNoFirstVariable(m, AbelianVarietyType=>opts.AbelianVarietyType);
     if n>0 then m=lift(m/(S_0^n),S);
     return polishchukD(monomialFourierTransformNoFirstVariable(m,AbelianVarietyType=>opts.AbelianVarietyType),n)     
     )

-- Gabor's formatting function
gSzPrint = L -> (
     L1:=null;
     s1:=null;
     m:=0;
     L1 = apply(L, s -> (
	       s1 = "";
               for i in s do s1 = s1 | toString i | "   ";
               s1)
	  );
     m = max apply(L1, s -> length s);
     for s in apply(L1, s -> concatenate { (m - length s)//2, s }) do print s;
     )

----------------------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------------------

beginDocumentation()

doc ///
  Key
    AbelianTautologicalRings
  Headline
    Construction of model tautological rings of Jacobian and Prym varieties and operators on them.
  Description
    Text
      This package implements the construction of {\it model tautological rings} of Jacobian and Prym varieties and various operators on them. 
      The model tautological ring of a Jacobian was constructed in [P05] and it surjects onto the so-called 
      {\it tautological ring} of a Jacobian. The surjection is conjecturally an isomorphism for the generic Jacobian. The analogous 
      construction for Prym varieties has been carried out in [A11].
      
      Tautological rings of Jacobians and Pryms contain the classes (modulo algebraic equivalence) of essentially all known 
      algebraic cycles on these varieties and are fundamental objects in the study of cycles on abelian varieties.  
      
      The Hilbert function of the model tautological ring of a Jacobian has a beautiful conjectural 
      description due to van der Geer and Kouvidakis, see [M09]. The van der Geer-Kouvidakis conjecture has a strong form that 
      gives a basis for the bi-graded pieces of the model tautological ring. Our package provides the tools for verifying these 
      conjectures experimentally. There is an analogous conjectural formula for the Hilbert function and conjectural basis of the 
      model tautological ring of a Prym. Our package provides the tools for verifying these conjectures as well.  
                
    
      {\bf References:}

      For tautological rings and model tautological rings see:

      [A11] {\it M. Arap, Tautological rings of Prym varieties, University of Georgia, PhD thesis (2011)}. 

      [A12] {\it M. Arap, Algebraic cycles on Prym varieties, Math. Ann. 353 (2012), 707-726}.

      [B04] {\it A. Beauville, Algebraic cycles on Jacobian varieties, Compositio Math. 140  (2004),  no. 3, 683-688}.

      [M09] {\it  B. Moonen, Relations between tautological cycles on Jacobians. Comment. Math. Helv. 84 (2009), no. 3, 471-502}. 

      [P05] {\it A. Polishchuk, Universal algebraic equivalences between tautological cycles on Jacobians of curves.  Math. Z. 251 (2005), 875-897}. 


      
      {\bf Key user functions:} @TO abelianTautologicalRing@, @TO polishchukD@, @TO polishchukDelta@, @TO fourierTransform@.

      {\it The main function of the package is:}  @TO abelianTautologicalRing@. 

      {\it An essential tool for studying tautological cycles is the function that computes the} @TO fourierTransform@.

      {\it Other essential functions used in the construction of tautological rings are:} @TO polishchukD@, @TO polishchukDelta@.

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
    moonenDiamond
  Headline
    Print the Moonen diamond. 
  Usage
    moonenDiamond(S)
  Inputs
    S:Ring
        a ring that is the output of @TO abelianTautologicalRing@. 
  Description
   Text
    Print the Hilbert function of the Beauville-Polishchuk ring. The formatting is as in [M09]. 
   Example
     S=abelianTautologicalRing(5)
     moonenDiamond(S)
     R=abelianTautologicalRing(6, AbelianVarietyType=>"Prym")
     moonenDiamond(R)
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
        an element of a ring returned by @TO modelRing@ or @TO abelianTautologicalRing@.
    n:ZZ
        an integer to specify the number of iterations of the Polishchuk operator to be applied
  Outputs
    :RingElement
  Description
   Text
    Apply the Polishchuk Delta operator, see [P05,p.883]. 
   Example
     S=modelRing(5)
     polishchukDelta(x_1^2*x_2*x_3)
     polishchukDelta(x_1^2*x_2*x_3,2)
     
     S=modelRing(11,AbelianVarietyType=>"Prym")
     polishchukDelta(x_1^2*x_3*x_5)
     polishchukDelta(x_1^2*x_3*x_5,2)
  SeeAlso 
     polishchukD
///


doc ///
  Key
    fourierTransform
  Headline
    Compute the Fourier transform of an element in a tautological ring.
  Usage
    modelRing(g)
  Inputs
    f:RingElement        
  Outputs
    :RingElement
  Description
   Text
     Compute the Fourier transform of an element of the ring returned by @TO modelRing@ or @TO abelianTautologicalRing@.     
   Example
     S=modelRing(5)
     fourierTransform(x_1*x_2)
     
     S=abelianTautologicalRing(5)
     fourierTransform(x_1*x_2)
     
     S=modelRing(7,AbelianVarietyType=>"Prym")
     fourierTransform(x_1*x_3)
     
     S=abelianTautologicalRing(7,AbelianVarietyType=>"Prym")
     fourierTransform(x_1*x_3)
     
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
    Option to specify the name of an indexed variable. 
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
    [abelianTautologicalRing, IndexedVariableName]
  Headline
    Option to specify the name of the indexed variable. 
  Description
    Text
      @TO Option@ to specify the name of the variable to be used in the output of @TO abelianTautologicalRing@.

      It takes @TO String@ value, e.g., "w" (default is "x").
///
