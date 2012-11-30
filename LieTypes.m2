-- -*- coding: utf-8 -*-
-- licensed under GPL v2 or any later version
newPackage(
     "LieTypes",
     Version => "0.1",
     Date => "August 8, 2012",
     Headline => "Common types for Lie groups and Lie algebras",
     Authors => {
	  {Name => "Dave Swinarski", Email => "dswinarski@fordham.edu"}
	  },
     -- DebuggingMode should be true while developing a package, 
     --   but false after it is done
     DebuggingMode => true 
     )

export {
     --for the LieAlgebra type:
     "LieAlgebra",
     "simpleLieAlgebra",
     "dualCoxeterNumber", 
     "highestRoot",
     "starInvolution",
     "scaledKillingForm",
     "weylAlcove",
     --for the LieAlgebraModule type
     "LieAlgebraModule", 
     "irreducibleLieAlgebraModule",
     "isIsomorphic",
     "casimirScalar",
     "multiplicityOfWeightInLieAlgebraModule",
     "weightDiagram",
     "tensorCoefficient",
     "fusionProduct",
     "fusionCoefficient",
     "MaxWordLength"
     }


{*
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------
-- Summary, Version 0.1, August 2012
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------

We define two types that are used by the ConformalBlocks package:
LieAlgebra
LieAlgebraModule

Both are mutable hash tables.

LieAlgebras have three keys: RootSystemType, LieAlgebraRank, and isSimple
The functions available for LieAlgebras are:
simpleLieAlgebra
dualCoxeterNumber
highestRoot
starInvolution
scaledKillingForm
weylAlcove

LieAlgebraModules have three keys: LieAlgebra, HighestWeight, and isIrreducible
The functions available for LieAlgebraModules are:
dimension
weights
casimirScalar
tensor product decomposition
fusion coefficient

Most of the lines of code below are to implement Freudenthal's formula for the multiplicity
of a weight w in the irreducible g-module with highest weight v, and the Racah-Speiser algorithm
for computing tensor product decompositions.  Many of these functions are copied over from early versions
of Swinarski's ConformalBlocks package.  

*}



-----------------------------------------------------------------------
-- LieAlgebra= {
--   LieAlgebraRank => ZZ, dim of Cartan subalgebra
--   RootSystemType => String, type A through G
--   isSimple => Boolean
--   }

LieAlgebra = new Type of HashTable  

LieAlgebra == LieAlgebra := (V,W)-> (V===W)

net LieAlgebra := (g) -> (peek g)

simpleLieAlgebra = method(
     TypicalValue => LieAlgebra
     )
simpleLieAlgebra(String,ZZ) := (type,m) -> (
     if isSubset({type},{"A","B","C","D","E","F","G"})==false then error "The simple Lie algebras over the complex numbers have types A, B, C, D, E, F, or G";
     if type=="A" and m<= 0 then error "The rank for type A must be >= 1.";
     if type=="B" and m<= 1 then error "The rank for type B must be >= 2.";
     if type=="C" and m<= 2 then error "The rank for type C must be >= 3.";
     if type=="D" and m<= 3 then error "The rank for type D must be >= 4.";
     if type=="E" and isSubset({m},{6,7,8})==false then error "The rank for type E must be 6, 7, or 8.";
     if type=="F" and m!=4 then error "The rank for type F must be 4.";
     if type=="G" and m!=2 then error "The rank for type G must be 2.";                    
     return new LieAlgebra from {"LieAlgebraRank"=>m,"RootSystemType"=>type,"isSimple"=>true}
     )
simpleLieAlgebra(IndexedVariable) := (v) -> (
     v=toString(v);
     k:=value(substring(3,v));
     if instance(k,ZZ)==false then error "Input not understood; enter sl_k, sp_k, or so_k, or use the syntax simpleLieAlgebra(\"A\",1) instead";
     if substring(0,3,v)=="sl_" and k >= 2 then return simpleLieAlgebra("A",k-1);
     if substring(0,3,v)=="so_" and odd(k) and k>=5  then return simpleLieAlgebra("B",lift((k-1)/2,ZZ));
     if substring(0,3,v)=="sp_" and even(k) and k >= 4 then return simpleLieAlgebra("C",lift(k/2,ZZ));
     if substring(0,3,v)=="so_" and even(k) and k >= 8 then return simpleLieAlgebra("D",lift(k/2,ZZ));
     )

     
dualCoxeterNumber = method(
     TypicalValue => ZZ
     )     
dualCoxeterNumber(String,ZZ) := memoize((type,m) -> (--see Appendix 13.A, [DMS]
     if type == "A" then return m+1;
     if type == "B" then return 2*m-1;
     if type == "C" then return m+1;
     if type == "D" then return 2*m-2;
     if type == "E" and m==6 then return 12;
     if type == "E" and m==7 then return 18;
     if type == "E" and m==8 then return 30;
     if type == "F" then return 9;
     if type == "G" then return 4
     ));   
dualCoxeterNumber(LieAlgebra) := memoize((g) -> (--see Appendix 13.A, [DMS]
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";
     dualCoxeterNumber(type,m)	  
     )); 


highestRoot = method(
     TypicalValue => List
     )
highestRoot(String,ZZ) := memoize((type, m) -> (--see Appendix 13.A, [DMS]
     if type == "A" and m==1 then return {2};
     if type == "A" and m >= 2 then return flatten {{1}, apply(m-2,i->0),{1}};
     if type == "B" then return flatten {{0},{1}, apply(m-2,i->0)};
     if type == "C" then return flatten {{2}, apply(m-1,i->0)};
     if type == "D" then return flatten {{0},{1}, apply(m-2,i->0)};
     --July 2011: changed numbering to match WeylGroups
     if type == "E" and m==6 then return {0,1,0, 0,0,0};
     if type == "E" and m==7 then return {1,0,0,0, 0,0,0};
     if type == "E" and m==8 then return {0,0,0,0, 0,0,0,1};
     if type == "F" then return {1,0,0,0};
     if type == "G" then return {0,1}
));

highestRoot(LieAlgebra) := memoize((g) -> (--see Appendix 13.A, [DMS]
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";   
     return highestRoot(type,m)
));

starInvolution = method(
     TypicalValue => List
     )
starInvolution(String,ZZ,List) := memoize((type, m, w) ->  ( N:=#w;
     if type == "A" then return apply(N,i-> w_(N-i-1));
     if type == "B" or type == "C" or type == "F" or type == "G" then return w;
     if type == "E" and m!= 6 then return w;
     if type == "D" and even(m) == true then return w;
     if type == "D" and odd(m) == true then (x:=w;
     return append(drop(x,{#x-2,#x-2}),w_(#w-2)));
     if type == "E" and m== 6 then return {w_5,w_1,w_4,w_3,w_2,w_0};
     ));
starInvolution(List,LieAlgebra) := memoize((v,g) -> (
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";   
     return starInvolution(type,m,v)
));
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------
-- The LieAlgebraModule type
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------


-- LieAlgebraModule= {
--   LieAlgebra => 
--   isIrreducible => Boolean
--   highestWeight
--   }
--Functions: weights, dimension, **

LieAlgebraModule = new Type of HashTable 
 

net LieAlgebraModule := (M) -> (peek M)

isIsomorphic = method(
     TypicalValue => Boolean
     )
isIsomorphic(LieAlgebraModule,LieAlgebraModule) := (M,N) -> (
if M#"LieAlgebra" != N#"LieAlgebra" then return false;
return M#"DecompositionIntoIrreducibles"===N#"DecompositionIntoIrreducibles"
)

irreducibleLieAlgebraModule = method(
     TypicalValue => LieAlgebraModule
     )
irreducibleLieAlgebraModule(List,LieAlgebra) := (v,g) -> (
return new LieAlgebraModule from {"LieAlgebra"=>g,"highestWeight"=>v,"isIrreducible"=>true,"DecompositionIntoIrreducibles"=>(new HashTable from {v=>1})}
     )


{*-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------
-- Private functions for LieAlgebraModule
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------

We implement the Lie theoretic ingredients needed to compute the weights in an irreducible Lie algebra module and their multiplicities
We need: 
--a list of the positive roots
--the ability to compute casimirScalars
---->To get casimirScalars, we need the so-called quadratic form matrix, which can be looked up or computed from the Cartan matrix

Cartan matrices and the Killing form are also implemented in the WeylGroups package.  I am using my own 
implementations because I want the Cartan matrix over QQ (so I can invert it) and so that the Killing form is scaled to make 
(theta,theta) = 2, where theta is the highest root.  This is a popular convention in the conformal blocks literature that is not used in WeylGroups. 

To avoid shadowing, I have named my function cartanMatrixQQ
*}

cartanMatrixQQ = memoize((type, m) ->( M:={};
	  i:=0;
     if type=="A" then (
          for i from 0 to m-1 do M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -1 else 0));
          return matrix M
     );
     if type=="B" then (
          for i from 0 to m-3 do M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -1 else 0)); 
          i=m-2;
          M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -2 else 0)); 
          i=m-1;
          M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -1 else 0));
          return matrix M
     );
     if type=="C" then (
          for i from 0 to m-3 do M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1/1 else if j==i then 2 else if j==i+1 then -1 else 0)); 
          i=m-2;
          M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -2 else 0)); 
          i=m-1;
          M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -1 else 0));
          return transpose matrix M
     );
     if type=="D" then (
          for i from 0 to m-4 do M = append(M, (1/1)*apply(m, j -> if j==i-1 then -1/1 else if j==i then 2 else if j==i+1 then -1 else 0));
          i=m-3;
          M= append(M,(1/1)*apply(m, j -> if j==i-1 then -1 else if j==i then 2 else if j==i+1 then -1 else if j==i+2 then -1 else 0));
          i=m-2;
          M= append(M,(1/1)*apply(m, j -> if j==i then 2 else if j==i-1 then -1 else 0));
          i=m-1;
          M= append(M,(1/1)*apply(m, j -> if j==i then 2 else if j==i-2 then -1 else 0));
          return matrix M
     );
     if type=="E" and m==6 then (
	  return matrix {{2/1, 0, -1, 0, 0, 0}, {0, 2, 0, -1, 0, 0}, {-1, 0, 2, -1, 0, 0}, {0, -1, -1, 2, -1, 0}, {0, 0, 0, -1, 2, -1}, {0, 0, 0, 0, -1, 2}});  
     if type=="E" and m==7 then (
	  return matrix {{2/1, 0, -1, 0, 0, 0, 0}, {0, 2, 0, -1, 0, 0, 0}, {-1, 0, 2, -1, 0, 0, 0}, {0, -1, -1, 2, -1, 0, 0}, {0, 0, 0, -1, 2, -1, 0}, {0, 0, 0, 0, -1, 2, -1}, {0, 0, 0, 0, 0, -1, 2}});
     if type=="E" and m==8 then (
	  return matrix {{2/1, 0, -1, 0, 0, 0, 0, 0}, {0, 2, 0, -1, 0, 0, 0, 0}, {-1, 0, 2, -1, 0, 0, 0, 0}, {0, -1, -1, 2, -1, 0, 0, 0}, {0, 0, 0, -1, 2, -1, 0, 0}, {0, 0, 0, 0, -1, 2, -1, 0}, {0, 0, 0, 0, 0, -1, 2, -1}, {0, 0, 0, 0, 0, 0, -1, 2}});
     if type == "F" then return matrix({{2/1,-1,0,0},{-1,2,-2,0},{0,-1,2,-1},{0,0,-1,2}});
     if type == "G" then return matrix({{2/1,-1},{-3,2}});
     ));


--We code what Di Francesco, Mathieu, and Senechal call the quadratic form matrix
--For types A,D,E, it is the inverse of the Cartan matrix.  See paragraph 1, [DMS] p. 498 and (13.51), [DMS] p. 499 
--For the other types Appendix 13.A, [DMS]


quadraticFormMatrix = memoize((type, m) -> ( M:={};
     if type=="A" or type =="D" or type=="E" then return (cartanMatrixQQ(type,m))^-1;
     if type =="B" then (
	  for i from 0 to m-2 do  M= append(M,append(apply(m-1, j -> if j+1<=i+1 then 2*(j+1) else 2*(i+1 )),i+1));
	  M = append(M,append(apply(m-1,j->j+1),m/2));
	  return (1/2)*matrix(M) 
	  );
     if type =="C" then (
	  for i from 0 to m-1 do  M= append(M,apply(m, j -> if j+1<=i+1 then (j+1)/1 else (i+1 )));
	  return (1/2)*matrix(M)
	  );
     if type =="F" then return matrix {{2,3,2,1},{3,6,4,2},{2,4,3,3/2},{1,2,3/2,1}};
     if type =="G" then return matrix {{2/3,1},{1,2}}
	  ));	 
     


scaledKillingForm = method(
     TypicalValue => QQ
     )     
scaledKillingForm(String,ZZ,List,List) := memoize((type, m, v,w) ->   (
     (flatten entries (matrix({(1/1)*v})*(quadraticFormMatrix(type,m))*matrix(transpose({(1/1)*w}))) )_0
));
scaledKillingForm(LieAlgebra,List,List) := memoize((g, v,w) ->   (
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";	  
     (flatten entries (matrix({(1/1)*v})*(quadraticFormMatrix(type,m))*matrix(transpose({(1/1)*w}))) )_0
));

 
     
--This function returns the weights in the Weyl alcove
weylAlcove = method(
     TypicalValue => List
     )     
weylAlcove(String,ZZ,ZZ) := memoize((type, m, l) -> ( pl:={};
     if l==0 then return {apply(m, i -> 0)};
     if m==1 then return apply(l+1,i->{i});
     if type=="A" or type == "C" then (
          pl={{append(apply(m-1, i -> 0),l)}};
          for k from 0 to l-1 do (
               pk:=weylAlcove(type,m-1,l-k);
               pk=apply(#pk, q -> append(pk_q,k));
               pl=append(pl,pk));
          return sort flatten pl);
     if type != "A" and type != "C" then (
          pl=weylAlcove("A",m,l);    
	  ans:={};
	  Theta :=highestRoot(type,m);
	  for i from 0 to #pl-1 do (
	       if scaledKillingForm(type, m, pl_i, Theta) <= l then ans = append(ans, pl_i));
          return sort ans)
));  

weylAlcove(ZZ,LieAlgebra) := memoize( (l,g)-> (
    type:=g#"RootSystemType";
    m:=g#"LieAlgebraRank";
    return weylAlcove(type,m,l) 
))
     



--For definitions and formulas of Casimir scalars, see (13.127), [DMS] p. 512
--For the definition and formula for rho, see: (13.46), [DMS] p. 499
     
casimirScalar = method(
     TypicalValue => QQ
     )     
casimirScalar(String,ZZ,List) := memoize((type, m, w) -> (
     rho:=apply(m,h->1/1);
     scaledKillingForm(type,m,w,w) + 2*scaledKillingForm(type,m,w,rho)
));
casimirScalar(LieAlgebraModule) := memoize((M) -> (
     g:=M#"LieAlgebra";
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";
     v:=M#"highestWeight";
     return casimirScalar(type,m,v)	  
));
  
simpleRoots = (type,m) -> (
     C:=cartanMatrixQQ(type,m);     
     ans:=entries(C);
     ans=apply(#ans, i -> apply(#(ans_i),j-> lift(ans_i_j,ZZ)));     
     return ans          
)

--In Freudenthal's formula, we need to sum over the positive roots
positiveRoots = memoize((type,m) -> (
     simpleroots:=simpleRoots(type,m);
     ans:={};
     ans1:={};
     es:={};
     em:={};
     subs:={};
     eiplusej:={};
     if type=="A" then (
          for i from 0 to m-1 do (
               for j from i to m-1 do (
                    if j==i then ans=append(ans,simpleroots_i);
                    if j > i then ans = append(ans,sum apply(j-i+1, k -> simpleroots_(i+k)))
     )));
     if type=="B" then (
          ans1={};
          for i from 0 to m-2 do (
               for j from i to m-2 do (
                    if j==i then ans1=append(ans1,simpleroots_i);
                    if j > i then ans1 = append(ans1,sum apply(j-i+1, k -> simpleroots_(i+k)))
          ));
          es=apply(m, i -> sum apply(m-i, k -> simpleroots_(m-1-k)));
          subs=subsets(es,2);
          eiplusej=apply(#subs,h -> sum subs_h);
          ans=flatten {ans1,es,eiplusej}
      );
      if type=="C" then (
          ans1={};
          for i from 0 to m-2 do (
               for j from i to m-2 do (
                    if j==i then ans1=append(ans1,simpleroots_i);
                    if j > i then ans1 = append(ans1,sum apply(j-i+1, k -> simpleroots_(i+k)))
          ));
          twoes:=apply(m, i -> if i<m-1 then sum(apply(m-i-1, k -> 2*simpleroots_(m-2-k)))+ simpleroots_(m-1) else simpleroots_(m-1));
          subs=subsets(twoes,2);
          eiplusej=apply(#subs,h -> sum subs_h);
          eiplusej=apply(#eiplusej,h -> apply(m, t-> lift((1/2)*eiplusej_h_t,ZZ)));
          ans=flatten {ans1,twoes,eiplusej}
     );
     if type=="D" then (
          ans1={};
          for i from 0 to m-2 do (
               for j from i to m-2 do (
                    if j==i then ans1=append(ans1,simpleroots_i);
                    if j > i then ans1 = append(ans1,sum apply(j-i+1, k -> simpleroots_(i+k)))
          ));
          em=(1/2)*(simpleroots_(m-1)-simpleroots_(m-2));
          em=apply(#em,k-> lift(em_k,ZZ));
          es={em};
          for i from 0 to m-2 do (
               es = append(es,es_(#es-1)+simpleroots_(m-2-i))
          );
          subs=subsets(es,2);
          eiplusej=apply(#subs,h -> sum subs_h);
          ans=flatten {ans1,eiplusej}
     );
     if type=="E" and m==6 then (
	  return {{0, 0, 0, 0, -1, 2}, {0, 0, 0, -1, 1, 1}, {0, -1, -1, 1, 0, 1}, {-1, -1, 1, 0, 0, 1}, {1, -1, 0, 0, 0, 1}, {0, 1, -1, 0, 0, 1}, {-1, 1, 1, -1, 0, 1}, {1, 1, 0, -1, 0, 1}, {-1, 0, 0, 1, -1, 1}, {1, 0, -1, 1, -1, 1}, {-1, 0, 0, 0, 1, 0}, {1, 0, -1, 0, 1, 0}, {1, 0, -1, 1, 0, -1}, {0, 0, 1, 0, 0, -1}, {0, -1, -1, 2, -1, 0}, {-1, -1, 1, 1, -1, 0}, {0, 1, -1, 1, -1, 0}, {-1, 1, 1, 0, -1, 0}, {1, 0, 1, -1, 0, 0}, {0, 2, 0, -1, 0, 0}, {2, 0, -1, 0, 0, 0}, {-1, 0, 2, -1, 0, 0}, {1, 1, 0, 0, -1, 0}, {1, -1, 0, 1, -1, 0}, {-1, 0, 0, 1, 0, -1}, {1, 1, 0, -1, 1, -1}, {1, -1, 0, 0, 1, -1}, {-1, 1, 1, -1, 1, -1}, {-1, -1, 1, 0, 1, -1}, {0, 1, -1, 0, 1, -1}, {0, -1, -1, 1, 1, -1}, {0, 0, 0, -1, 2, -1}, {0, 1, 0, 0, 0, 0}, {0, -1, 0, 1, 0, 0}, {0, 0, 1, -1, 1, 0}, {0, 0, 1, 0, -1, 1}});
     if type=="E" and m==7 then (
	  return {{0, 0, 0, 0, 0, -1, 2}, {0, 0, 0, 0, -1, 1, 1}, {0, 0, 0, -1, 1, 0, 1}, {0, -1, -1, 1, 0, 0, 1}, {-1, -1, 1, 0, 0, 0, 1}, {0, 1, -1, 0, 0, 0, 1}, {-1, 1, 1, -1, 0, 0, 1}, {-1, 0, 0, 1, -1, 0, 1}, {-1, 0, 0, 0, 1, -1, 1}, {-1, 0, 0, 0, 0, 1, 0}, {1, -1, 0, 0, 0, 0, 1}, {1, 1, 0, -1, 0, 0, 1}, {1, 0, -1, 1, -1, 0, 1}, {1, 0, -1, 0, 1, -1, 1}, {1, 0, -1, 0, 0, 1, 0}, {0, 0, 1, 0, -1, 1, -1}, {0, 0, 1, -1, 1, 0, -1}, {0, -1, 0, 1, 0, 0, -1}, {0, 1, 0, 0, 0, 0, -1}, {0, 0, 0, -1, 2, -1, 0}, {0, -1, -1, 1, 1, -1, 0}, {0, 1, -1, 0, 1, -1, 0}, {-1, -1, 1, 0, 1, -1, 0}, {-1, 1, 1, -1, 1, -1, 0}, {1, -1, 0, 0, 1, -1, 0}, {1, 1, 0, -1, 1, -1, 0}, {-1, 0, 0, 1, 0, -1, 0}, {1, -1, 0, 1, -1, 0, 0}, {1, 1, 0, 0, -1, 0, 0}, {-1, 0, 2, -1, 0, 0, 0}, {2, 0, -1, 0, 0, 0, 0}, {0, 2, 0, -1, 0, 0, 0}, {1, 0, 1, -1, 0, 0, 0}, {-1, 1, 1, 0, -1, 0, 0}, {0, 1, -1, 1, -1, 0, 0}, {-1, -1, 1, 1, -1, 0, 0}, {0, -1, -1, 2, -1, 0, 0}, {0, 0, 1, 0, 0, -1, 0}, {1, 0, -1, 1, 0, -1, 0}, {1, 0, -1, 0, 1, 0, -1}, {-1, 0, 0, 0, 1, 0, -1}, {1, 0, -1, 1, -1, 1, -1}, {-1, 0, 0, 1, -1, 1, -1}, {1, 1, 0, -1, 0, 1, -1}, {-1, 1, 1, -1, 0, 1, -1}, {0, 1, -1, 0, 0, 1, -1}, {1, -1, 0, 0, 0, 1, -1}, {-1, -1, 1, 0, 0, 1, -1}, {0, -1, -1, 1, 0, 1, -1}, {0, 0, 0, -1, 1, 1, -1}, {0, 0, 0, 0, -1, 2, -1}, {1, 0, 0, 0, 0, 0, 0}, {-1, 0, 1, 0, 0, 0, 0}, {0, 0, -1, 1, 0, 0, 0}, {0, 1, 0, -1, 1, 0, 0}, {0, -1, 0, 0, 1, 0, 0}, {0, 1, 0, 0, -1, 1, 0}, {0, 1, 0, 0, 0, -1, 1}, {0, -1, 0, 1, -1, 1, 0}, {0, -1, 0, 1, 0, -1, 1}, {0, 0, 1, -1, 0, 1, 0}, {0, 0, 1, -1, 1, -1, 1}, {0, 0, 1, 0, -1, 0, 1}});
     if type=="E" and m==8 then (
	  return {{0, 0, 0, 0, 0, 0, -1, 2}, {0, 0, 0, 0, 0, -1, 1, 1}, {0, 0, 0, 0, -1, 1, 0, 1}, {0, 0, 0, -1, 1, 0, 0, 1}, {0, -1, -1, 1, 0, 0, 0, 1}, {-1, -1, 1, 0, 0, 0, 0, 1}, {0, 1, -1, 0, 0, 0, 0, 1}, {-1, 1, 1, -1, 0, 0, 0, 1}, {-1, 0, 0, 1, -1, 0, 0, 1}, {-1, 0, 0, 0, 1, -1, 0, 1}, {-1, 0, 0, 0, 0, 1, -1, 1}, {1, -1, 0, 0, 0, 0, 0, 1}, {1, 1, 0, -1, 0, 0, 0, 1}, {1, 0, -1, 1, -1, 0, 0, 1}, {1, 0, -1, 0, 1, -1, 0, 1}, {1, 0, -1, 0, 0, 1, -1, 1}, {0, 0, 1, 0, -1, 0, 0, 1}, {0, 0, 1, -1, 1, -1, 0, 1}, {0, 0, 1, -1, 0, 1, -1, 1}, {0, -1, 0, 1, 0, -1, 0, 1}, {0, -1, 0, 1, -1, 1, -1, 1}, {0, 1, 0, 0, 0, -1, 0, 1}, {0, 1, 0, 0, -1, 1, -1, 1}, {0, -1, 0, 0, 1, 0, -1, 1}, {0, 0, 1, 0, -1, 0, 1, -1}, {0, 0, 1, -1, 1, -1, 1, -1}, {0, 0, 1, -1, 0, 1, 0, -1}, {0, -1, 0, 1, 0, -1, 1, -1}, {0, -1, 0, 1, -1, 1, 0, -1}, {0, 1, 0, 0, 0, -1, 1, -1}, {0, 1, 0, 0, -1, 1, 0, -1}, {0, -1, 0, 0, 1, 0, 0, -1}, {0, 1, 0, -1, 1, 0, 0, -1}, {0, 0, -1, 1, 0, 0, 0, -1}, {-1, 0, 1, 0, 0, 0, 0, -1}, {1, 0, 0, 0, 0, 0, 0, -1}, {0, 0, 0, 0, -1, 2, -1, 0}, {0, 0, 0, -1, 1, 1, -1, 0}, {0, -1, -1, 1, 0, 1, -1, 0}, {-1, -1, 1, 0, 0, 1, -1, 0}, {1, -1, 0, 0, 0, 1, -1, 0}, {0, 1, -1, 0, 0, 1, -1, 0}, {-1, 1, 1, -1, 0, 1, -1, 0}, {1, 1, 0, -1, 0, 1, -1, 0}, {-1, 0, 0, 1, -1, 1, -1, 0}, {1, 0, -1, 1, -1, 1, -1, 0}, {-1, 0, 0, 0, 1, 0, -1, 0}, {1, 0, -1, 0, 1, 0, -1, 0}, {1, 0, -1, 1, 0, -1, 0, 0}, {0, 0, 1, 0, 0, -1, 0, 0}, {0, -1, -1, 2, -1, 0, 0, 0}, {-1, -1, 1, 1, -1, 0, 0, 0}, {0, 1, -1, 1, -1, 0, 0, 0}, {-1, 1, 1, 0, -1, 0, 0, 0}, {1, 0, 1, -1, 0, 0, 0, 0}, {0, 2, 0, -1, 0, 0, 0, 0}, {2, 0, -1, 0, 0, 0, 0, 0}, {-1, 0, 2, -1, 0, 0, 0, 0}, {1, 1, 0, 0, -1, 0, 0, 0}, {1, -1, 0, 1, -1, 0, 0, 0}, {-1, 0, 0, 1, 0, -1, 0, 0}, {1, 1, 0, -1, 1, -1, 0, 0}, {1, -1, 0, 0, 1, -1, 0, 0}, {-1, 1, 1, -1, 1, -1, 0, 0}, {-1, -1, 1, 0, 1, -1, 0, 0}, {0, 1, -1, 0, 1, -1, 0, 0}, {0, -1, -1, 1, 1, -1, 0, 0}, {0, 0, 0, -1, 2, -1, 0, 0}, {0, 1, 0, 0, 0, 0, -1, 0}, {0, -1, 0, 1, 0, 0, -1, 0}, {0, 0, 1, -1, 1, 0, -1, 0}, {0, 0, 1, 0, -1, 1, -1, 0}, {1, 0, -1, 0, 0, 1, 0, -1}, {1, 0, -1, 0, 1, -1, 1, -1}, {1, 0, -1, 1, -1, 0, 1, -1}, {1, 1, 0, -1, 0, 0, 1, -1}, {1, -1, 0, 0, 0, 0, 1, -1}, {-1, 0, 0, 0, 0, 1, 0, -1}, {-1, 0, 0, 0, 1, -1, 1, -1}, {-1, 0, 0, 1, -1, 0, 1, -1}, {-1, 1, 1, -1, 0, 0, 1, -1}, {0, 1, -1, 0, 0, 0, 1, -1}, {-1, -1, 1, 0, 0, 0, 1, -1}, {0, -1, -1, 1, 0, 0, 1, -1}, {0, 0, 0, -1, 1, 0, 1, -1}, {0, 0, 0, 0, -1, 1, 1, -1}, {0, 0, 0, 0, 0, -1, 2, -1}, {0, 0, 0, 0, 0, 0, 1, -1}, {0, 0, 0, 0, 0, 1, -1, 0}, {0, 0, 0, 0, 1, -1, 0, 0}, {0, 0, 0, 1, -1, 0, 0, 0}, {0, 1, 1, -1, 0, 0, 0, 0}, {0, -1, 1, 0, 0, 0, 0, 0}, {1, 1, -1, 0, 0, 0, 0, 0}, {-1, 1, 0, 0, 0, 0, 0, 0}, {1, -1, -1, 1, 0, 0, 0, 0}, {-1, -1, 0, 1, 0, 0, 0, 0}, {1, 0, 0, -1, 1, 0, 0, 0}, {-1, 0, 1, -1, 1, 0, 0, 0}, {0, 0, -1, 0, 1, 0, 0, 0}, {1, 0, 0, 0, -1, 1, 0, 0}, {-1, 0, 1, 0, -1, 1, 0, 0}, {0, 0, -1, 1, -1, 1, 0, 0}, {0, 1, 0, -1, 0, 1, 0, 0}, {0, -1, 0, 0, 0, 1, 0, 0}, {1, 0, 0, 0, 0, -1, 1, 0}, {-1, 0, 1, 0, 0, -1, 1, 0}, {0, 0, -1, 1, 0, -1, 1, 0}, {0, 1, 0, -1, 1, -1, 1, 0}, {0, 1, 0, 0, -1, 0, 1, 0}, {0, -1, 0, 0, 1, -1, 1, 0}, {0, -1, 0, 1, -1, 0, 1, 0}, {0, 0, 1, -1, 0, 0, 1, 0}, {1, 0, -1, 0, 0, 0, 1, 0}, {-1, 0, 0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 0, 0, 1}, {1, 0, 0, 0, 0, 0, -1, 1}, {-1, 0, 1, 0, 0, 0, -1, 1}, {0, 0, -1, 1, 0, 0, -1, 1}, {0, 1, 0, -1, 1, 0, -1, 1}});
     if type=="F" and m==4 then (
	  return {{0, 0, 0, 1}, {1, 0, 0, -1}, {-1, 1, 0, -1}, {0, -1, 2, -1}, {1, 0, 0, 0}, {-1, 1, 0, 0}, {0, -1, 2, 0}, {0,1,0,-2}, {1,-1,2,-2}, {-1, 0, 2, -2}, {-1, 0, 0, 2}, {1, -1, 0, 2}, {0, 1, -2, 2}, {2, -1, 0, 0}, {1, 1, -2, 0}, {-1, 2, -2, 0}, {0, 0, 1, -1}, {0, 1, -1, 0}, {1, -1, 1, 0}, {1, 0, -1, 1}, {-1, 0, 1, 0}, {-1, 1, -1, 1}, {0, -1, 1, 1}, {0, 0, -1, 2}});
     if type=="G" and m==2 then return {{-3, 2}, {-1, 1}, {0, 1}, {2, -1}, {3, -1}, {1, 0}};
     return ans
))



--In the next four functions we implement Freudenthal's recursive algorithm for computing the weights in a representation and their multiplicities
Freud = memoize ((type,m,v) -> (
     simpleroots:=simpleRoots(type,m);
     if apply(#v, i -> v_i < 0) == apply(#v, i->true) then return set({v});
     ans:=set {v};
     for i from 0 to #v-1 do (
          if v_i < 0 then continue;
          for j from 1 to lift(v_i,ZZ) do (
               ans= ans+Freud(type,m,v-j*simpleroots_i)
     ));
     ans=toList ans;
     ans=apply(#ans, i -> apply(#(ans_i), j-> lift(ans_i_j,ZZ)));
     return set ans
))

weightsAboveLambda = memoize( (type,m,v,w) -> (
     Omega:=Freud(type,m,v);
     if w==v then return {};
     simpleroots:=simpleRoots(type,m);
     ans:={};
     k:=0;
     for i from 0 to #simpleroots-1 do (
          k=0;
          while isSubset(set {w+k*(simpleroots_i)},Omega) do (
               if k>0 then ans = append(ans,w+k*(simpleroots_i));
               k=k+1;
     ));
     ans=unique ans;
     alllevels:={ans};
     for i from 0 to #ans-1 do (
          alllevels = append(alllevels,weightsAboveLambda(type,m,v,ans_i))
     );
     return unique flatten alllevels
))


-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------
-- Exported functions for Lie algebra modules 
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------

multiplicityOfWeightInLieAlgebraModule=method(
     TypicalValue=>ZZ)
multiplicityOfWeightInLieAlgebraModule(String,ZZ,List,List) := memoize((type,m,v,w) -> (
     rho:=apply(m, i -> 1);
     if v==w then return 1;
     L:=weightsAboveLambda(type,m,v,w);
     Omega:=Freud(type,m,v);
     posroots:=positiveRoots(type,m);
     rhs:=0;
     lhs:=1;
     K:=0;
     for a from 0 to #posroots-1 do (
          K=0;
          while isSubset(set {w+K*(posroots_a)},Omega) do (K=K+1);
          if K <= 1 then continue;
          for k from 1 to K-1 do (
               rhs= rhs+scaledKillingForm(type,m,w+k*(posroots_a),posroots_a)*multiplicityOfWeightInLieAlgebraModule(type,m,v,w+k*(posroots_a)) ));
     lhs=scaledKillingForm(type,m,v+rho,v+rho)-scaledKillingForm(type,m,w+rho,w+rho);
     return lift(2*rhs/lhs,ZZ)
))
multiplicityOfWeightInLieAlgebraModule(LieAlgebra,List,List) := (g,v,w) -> (
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";
     multiplicityOfWeightInLieAlgebraModule(type,m,v,w)	  
)
multiplicityOfWeightInLieAlgebraModule(List,LieAlgebraModule) := (w,M) -> (
     g:=M#"LieAlgebra";
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";
     v:=M#"highestWeight";
     multiplicityOfWeightInLieAlgebraModule(type,m,v,w)	  
)


weightDiagram = method(
     TypicalValue=>HashTable)
weightDiagram(String,ZZ,List) := memoize((type,m,v) -> (
     Omega:=toList Freud(type,m,v);     
     return new HashTable from apply(#Omega, i-> {Omega_i,multiplicityOfWeightInLieAlgebraModule(type,m,v,Omega_i)})     
))

weightDiagram(LieAlgebraModule) := (M) -> (
     if  M#?"isIrreducible"==false or M#"isIrreducible"==false then error "Weight diagrams are currently implemented only for irreducible Lie algebra modules";
     g:=M#"LieAlgebra";
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";
     v:=M#"highestWeight";    
     return weightDiagram(type,m,v)
)

dim LieAlgebraModule := M -> (
     tensordecomp:=pairs(M#"DecompositionIntoIrreducibles");
     tensordecomp=apply(#tensordecomp, i -> {irreducibleLieAlgebraModule(tensordecomp_i_0,M#"LieAlgebra"), tensordecomp_i_1});
     return sum apply(#tensordecomp, i -> (tensordecomp_i_1)*(sum values weightDiagram(tensordecomp_i_0)))
)	  

     

---------------------------------------------------------
---------------------------------------------------------
--Tensor product decomposition
---------------------------------------------------------
--------------------------------------------------------- 

--Action of word in Coxeter group or affine Coxeter group on weights
wordAction = (type,m,l,I,v) -> (
     simpleroots:=simpleRoots(type,m);
     w:=v;
     J:=reverse I; 
     for j from 0 to #J-1 do (     
          if J_j >0 then (
	       rho:=apply(#w, i-> 1);
               w=w+rho;     
               w = w-(w_(J_j-1))*simpleroots_(J_j-1);     
               w=w-rho);
          if J_j ==0 then (
               theta:=highestRoot(type,m);
               theta=apply(#theta, i -> lift(theta_i,ZZ));
               l0:=lift(l-scaledKillingForm(type,m,w,theta),ZZ);
               w = w+(l0+1)*theta);
      );
      return w
)


squarefreeWordsOfLengthP = (L,p) -> (
     if p==0 then return {};     
     if p==1 then return apply(#L, i -> {L_i});
     wlm1:=squarefreeWordsOfLengthP(L,p-1);
     ans:={};
     for i from 0 to #L-1 do (
          for j from 0 to #wlm1-1 do (
               if L_i != wlm1_j_0 then ans=append(ans,prepend(L_i,wlm1_j))          
     ));
     return ans
)

isIdentity = (type,m,l,w) -> (
     fdw:=apply(m, i -> apply(m, j -> if i==j then 1 else 0));
     return apply(m, i -> wordAction(type,m,l,w,fdw_i)) == fdw      
     )



tensorReflectionData = memoize( (type,m,maxwordlength,remwts) -> (
     theta:=highestRoot(type,m);
     l:=max apply(#remwts, i -> scaledKillingForm(type,m,remwts_i,theta));	
     l=lift(l,ZZ);
     Pl:=weylAlcove(type,m,l);
     wl:=1;
--initialize;
     remwts=toList(set(remwts)-set(Pl));
     found:= set Pl;
     ans:= set apply(#Pl, i -> {Pl_i,{}});
     fixed:={};
     S:=apply(m,i->i+1);
     while #remwts >0 and wl<=maxwordlength do (
          words:=squarefreeWordsOfLengthP(S,wl);
          for i from 0 to #words-1 do (
               if isIdentity(type,m,l,words_i) then continue;
               newremwts:={};
               for j from 0 to #remwts-1 do ( 
                    if wordAction(type,m,l,words_i,remwts_j)==remwts_j then (
                         ans = ans + set {{remwts_j,reverse(words_i)}};
                         fixed = append(fixed,remwts_j)) 
	            else newremwts=append(newremwts,remwts_j)   
               );
               remwts=newremwts;
--image of basis under words_i
               im:=apply(#Pl, j -> wordAction(type,m,l,words_i,Pl_j));
               if isSubset(set(im),found) then continue else (
                    found = found + set(im);
                    remwts=toList(set(remwts)-set(im));
                    ans=ans+set apply(#im, k -> {im_k,reverse(words_i)});
                ));
           wl=wl+1);
     if #remwts==0 then return {sort toList(ans),sort fixed,true,remwts} else return {sort toList(ans), sort fixed,false,remwts}
))



LieAlgebraModule ** LieAlgebraModule := memoize( (V,W) -> (
     if V#"LieAlgebra" != W#"LieAlgebra" then error "V and W must be modules over the same Lie algebra";	  
     g:=V#"LieAlgebra"; 
     type:=g#"RootSystemType";
     m:=g#"LieAlgebraRank";	  
     posRoots:=positiveRoots(type,m);
     wl:=#posRoots;	  
     lambda:=V#"highestWeight";
     mu:=W#"highestWeight";
     wd:=pairs weightDiagram(type,m,lambda);
     theta:=highestRoot(type,m);
     l:=max apply(#wd, i -> scaledKillingForm(type,m,wd_i_0,theta));
     l=lift(l,ZZ);	  
     Pl:=weylAlcove(type,m,l);
     wd=apply(#wd, i -> {wd_i_0+mu,wd_i_1});
     rd:=tensorReflectionData(type,m,wl,apply(#wd, i -> wd_i_0));
     if rd_2 == false then error "Need to allow longer words";
     fixed:=rd_1;
     rd=hashTable(rd_0);
     wtsinPl:={};
     for i from 0 to #wd-1 do (
          if isSubset(set {wd_i_0},Pl)==true and isSubset(set{wd_i_0},fixed)==false then wtsinPl=append(wtsinPl,wd_i)     
     );
     wdh:=new MutableHashTable from wtsinPl;
     for i from 0 to #wd-1 do (
          if isSubset(set {wd_i_0},Pl) then continue;     
          if isSubset(set{wd_i_0},fixed) then continue;
          word:=rd#(wd_i_0);
          e:=#word;
          e=(-1)^e;
          im:=wordAction(type,m,l,word,wd_i_0);
          if wdh#?im == false then  wdh#im = (e)*(wd_i_1) else  wdh#im = wdh#im + (e)*(wd_i_1)     
     );
     wdh=pairs(wdh);
     newwdh:={};
     for i from 0 to #wdh-1 do (
          if wdh_i_1 != 0 then newwdh=append(newwdh,wdh_i)
     );
     newdim:=(dim V)*(dim W);
     if #newwdh == 1 and newwdh_0_1 == 1 then return irreducibleLieAlgebraModule(newwdh_0_0,g);
     return new LieAlgebraModule from {"LieAlgebra"=>g,"DecompositionIntoIrreducibles"=>new HashTable from newwdh,"isIrreducible"=>false};
))

tensorCoefficient = method(
     TypicalValue=>ZZ)
tensorCoefficient(LieAlgebraModule, LieAlgebraModule,LieAlgebraModule) := memoize((U,V,W) -> (
     nu:=W#"highestWeight";	  
     fulltens:=(U**V)#"DecompositionIntoIrreducibles";
     if fulltens#?nu then return fulltens#nu else return 0     
     ))


fusionReflectionData = memoize( (type,m,l,maxwordlength,remwts) -> (
    Pl:=weylAlcove(type,m,l);
    wl:=1;
    --initialize;
    remwts=toList(set(remwts)-set(Pl));
    found:= set Pl;
    ans:= set apply(#Pl, i -> {Pl_i,{}});
    fixed:={};
    S:=apply(m+1,i->i);
    while #remwts >0 and wl<=maxwordlength do (
        words:=squarefreeWordsOfLengthP(S,wl);
        for i from 0 to #words-1 do (
            if isIdentity(type,m,l,words_i) then continue;
            newremwts:={};
            for j from 0 to #remwts-1 do (
                if wordAction(type,m,l,words_i,remwts_j)==remwts_j then (
                    ans = ans + set {{remwts_j,reverse(words_i)}};
                    fixed = append(fixed,remwts_j)) else newremwts=append(newremwts,remwts_j)   
                );
            remwts=newremwts;
            im:=apply(#Pl, j -> wordAction(type,m,l,words_i,Pl_j));
            if isSubset(set(im),found) then continue else (
                found = found + set(im);
                remwts=toList(set(remwts)-set(im));
                ans=ans+set apply(#im, k -> {im_k,reverse(words_i)});
            )
        );
        wl=wl+1);
    if #remwts==0 then return {sort toList(ans),sort fixed,true,remwts} else return {sort toList(ans), sort fixed,false,remwts}
))

fusionProduct = method(
     TypicalValue=>HashTable,Options=>{MaxWordLength=>10})

fusionProduct(LieAlgebraModule,LieAlgebraModule,ZZ) := memoize( opts-> (M,N,l) -> (
    wl:=opts.MaxWordLength;	  
    if M#"LieAlgebra" != N#"LieAlgebra" then error "The Lie algebra modules must be over the same Lie algebra.";
    g:=M#"LieAlgebra";
    type:=g#"RootSystemType";
    m:=g#"LieAlgebraRank";
    wl=max {wl, m+1};	  
    lambda:=M#"highestWeight";
    mu:=N#"highestWeight";
    wd:=pairs weightDiagram(type,m,lambda);
    wd=apply(#wd, i -> {wd_i_0+mu,wd_i_1});
    rd:=fusionReflectionData(type,m,l,wl,apply(#wd, i -> wd_i_0));
    if rd_2 == false then error "Need to allow longer words";
    fixed:=rd_1;
    rd=hashTable(rd_0);
    Pl:=weylAlcove(type,m,l);
    wtsinPl:={};
    for i from 0 to #wd-1 do (
        if isSubset(set {wd_i_0},Pl)==true and isSubset(set{wd_i_0},fixed)==false then wtsinPl=append(wtsinPl,wd_i)     
    );
    wdh:=new MutableHashTable from wtsinPl;
    for i from 0 to #wd-1 do (
        if isSubset(set {wd_i_0},Pl) then continue;     
        if isSubset(set{wd_i_0},fixed) then continue;
        word:=rd#(wd_i_0);
        e:=#word;
        e=(-1)^e;
        im:=wordAction(type,m,l,word,wd_i_0);
        wdh#im = wdh#im + (e)*(wd_i_1)     
    );
    wdh=pairs(wdh);
    newwdh:={};
    for i from 0 to #wdh-1 do (
        if wdh_i_1 != 0 then newwdh=append(newwdh,wdh_i)
    );
    if #newwdh == 1 and newwdh_0_1 == 1 then return irreducibleLieAlgebraModule(newwdh_0_0,simpleLieAlgebra(type,m));
    return new LieAlgebraModule from {"LieAlgebra"=>simpleLieAlgebra(type,m),"DecompositionIntoIrreducibles"=>new HashTable from newwdh,"isIrreducible"=>false};	  
))


fusionCoefficient=method(
     TypicalValue=>ZZ,Options=>{MaxWordLength=>10})
fusionCoefficient(LieAlgebraModule,LieAlgebraModule,LieAlgebraModule,ZZ) := memoize(opts -> (U,V,W,l) -> (
    wl:=opts.MaxWordLength;	  
    g:=U#"LieAlgebra";
    type:=g#"RootSystemType";
    m:=g#"LieAlgebraRank";
    fullfus:=fusionProduct(U,V,l,MaxWordLength=>wl);
    if fullfus#?(W#"highestWeight") then return fullfus#(W#"highestWeight") else return 0     
))



beginDocumentation()

doc ///
     Key
          LieTypes
     Headline
          Common types for Lie groups and Lie algebras
     Description
          Text 
               This package defines types used by the package {\tt ConformalBlocks} and may someday be used by other packages as well.  The package 
	       is currently in an extremely preliminary form.  If you would like to see a type or function added to this package (or better yet, if 
	       you would like to write types or functions for this package), please contact Dan Grayson, Mike Stillman, or Dave Swinarski.  
///

doc ///
     Key
          LieAlgebra
     Headline
          class for Lie algebras
     Description
          Text 
     	       This class represents Lie algebras.  Currently only simple Lie algebras over the complex numbers are supported.  
	  Example
	       g=simpleLieAlgebra(sl_2)
	       g=simpleLieAlgebra("E",6)                    
///

doc ///
     Key
          simpleLieAlgebra
	  (simpleLieAlgebra,String,ZZ)
	  (simpleLieAlgebra,IndexedVariable)
     Headline
          construct a simple Lie algebra
     Usage
          simpleLieAlgebra("A",1), simpleLieAlgebra(sl_2)
     Inputs
          t:String
               the type of the root system of the desired Lie algebra
          k:ZZ
               the rank of the desired Lie algebra
     Outputs
          g:LieAlgebra
               the simple Lie algebra with the given rank and type	        
     Description
          Text
              The classification of simple Lie algebras over the complex numbers is well-known.  There are four infinite families (types A, B, C, D) 
	      corresponding to the Lie algebras $sl(n+1,\mathbb{C})$, $so(2n+1,\mathbb{C})$, $sp(2n,\mathbb{C})$, $so(2n,\mathbb{C})$  
	      respectively, and five exceptional types, E6, E7, E8, F4, G2.  The user may enter the classical Lie algebras either by using the 
	      classical notation (e.g. sl_2) or by using type-rank notation ("A",1).  	   
          Example
              simpleLieAlgebra(sl_2)
	      simpleLieAlgebra("A",1)
	      simpleLieAlgebra(sp_10)
	      simpleLieAlgebra("E",6)
///	 	 

TEST ///
     assert(simpleLieAlgebra(sl_2) === new LieAlgebra from {"LieAlgebraRank"=>1,"RootSystemType"=>"A","isSimple"=>true} )
///

doc ///
     Key
          dualCoxeterNumber
	  (dualCoxeterNumber,LieAlgebra)
	  (dualCoxeterNumber,String,ZZ)
     Headline
          returns the dual Coxeter number of a simple Lie algebra
     Usage
          dualCoxeterNumber(g)
     Inputs
          g:LieAlgebra
	       a simple Lie algebra
     Outputs
          n:ZZ
	       the dual Coxeter number of g
     Description
          Text
	       The dual Coxeter number is defined as the sum of the comarks plus 1.  See Di Francesco, Mathieu, and Senechal, 
	       {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, Formula (13.35) and Appendix A.  
          Example
	       dualCoxeterNumber("A",2)	
	       g=simpleLieAlgebra(sl_3)
	       dualCoxeterNumber(g)
///

TEST ///
     assert(dualCoxeterNumber("A",2) === 3)
///

doc ///
     Key
          highestRoot
	  (highestRoot,String,ZZ)
	  (highestRoot,LieAlgebra)
     Headline
          returns the highest root of a simple Lie algebra
     Usage
          highestRoot(g), highestRoot("A",2)
     Inputs
          g:LieAlgebra
     Outputs
          t:List
     Description
          Text  
               Let R be an irreducible root system of rank m, and choose a set of simple roots $\alpha_1,...,\alpha_m$.  
	       Then there is a unique root $\theta$ such that when $\theta$ is expanded in terms of the simple roots,
	       i.e. $\theta= \sum c_i \alpha_i$, the sum $\sum c_i$ is maximized.  The formulas implemented here are 
	       taken from the tables following Bourbaki's {\it Lie Groups and Lie Algebras} Chapter 6.
	       
	       In the example below, we see that for $sl_3$, the highest root $\theta$ is $\omega_1+ \omega_2$, 
	       where $\omega_1$ and $\omega_2$ are the fundamental dominant weights.
	  Example
	       highestRoot("A",2)
///

TEST ///
     assert(highestRoot("A",2) === {1,1})
///	


doc ///
     Key
          starInvolution
	  (starInvolution,List,LieAlgebra)
	  (starInvolution,String,ZZ,List)
     Headline
          computes w* for a weight w
     Usage
          starInvolution(w,g)
     Inputs
          w:List
	  g:LieAlgebra
     Description
          Text
	       Let $\mathbf{g}$ be a Lie algebra.  We give three descriptions of an involution * on the weights of $\mathbf{g}$:  
	  Text 
	       1. The involution * is given by the longest word in the Weyl group $W(\mathbf{g})$.
	  Text
	       2. If $\mu$ is a dominant integral weight, and $V_{\mu}$ is the irreducible Lie algebra module with highest weight $\mu$, then $\mu^*$ is the highest weight of the dual module $(V_{\mu})^*$.
	  Text 
	       3. If the Dynkin diagram of $\mathbf{g}$ has an involution, then * corresponds to the action of this involution on weights.
          Text
               The formulas implemented have been adapted from Di Francesco, Mathieu, and Senechal, 
	       {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, p. 511.  The changes are needed because we use the 
	       Bourbaki ordering of the roots in type E instead of the [DMS] ordering.
	  Text     
	       In the example below, we see that for $sl_3$, $\omega_1^* = \omega_2.$
          Example
	       g=simpleLieAlgebra(sl_3)
	       starInvolution({1,0},g)
///

TEST ///
     g=simpleLieAlgebra(sl_3)
     assert(starInvolution({1,0},g) === {0,1})
///



doc ///
    Key
        scaledKillingForm
	(scaledKillingForm,LieAlgebra,List,List)
	(scaledKillingForm,String,ZZ,List,List)
    Headline 
        computes the scaled Killing form applied to two weights
    Usage 
        scaledKillingForm(g,v,w)
    Inputs 
        g:LieAlgebra
	v:List
	w:List
    Description
        Text
	    Let $\mathbf{g}$ be a Lie algebra.  The Killing form on $\mathbf{g}$ is the symmetric bilinear form given 
	    by $(x,y) = Tr(ad x ad y)$.  It can restricted to a Cartan subalgebra $\mathbf{h}$ and transfered to 
	    $\mathbf{h}^*$, yielding a symmetric bilinear form on weights.  One popular 
	    convention is to scale the Killing form so that $(\theta,\theta) =2$, where $\theta$ is the highest root.
        Example
            g=simpleLieAlgebra(sl_3)
	    scaledKillingForm(g,{1,0},{0,1})
///

TEST ///
    g=simpleLieAlgebra(sl_3)
    assert(scaledKillingForm(g,{1,0},{0,1}) === 1/3)
///	
	
doc ///
    Key
        weylAlcove
	(weylAlcove,String,ZZ,ZZ)
	(weylAlcove,ZZ,LieAlgebra)
    Headline 
        the dominant integral weights of level less than or equal to l
    Usage 
        weylAlcove(l,g)
    Inputs 
        l:ZZ
        g:LieAlgebra
    Description
        Text
            Let $\mathbf{g}$ be a Lie algebra, and let $l$ be a nonnegative integer.  Choose a Cartan subalgebra $\mathbf{h}$
	    and a base $\Delta= \{ \alpha_1,\ldots,\alpha_n\}$ of simple roots of $\mathbf{g}$.  These choices determine a highest root $\theta$. 
	    (see TO highestRoot).   Let $(,)$ denote the Killing form, normalized so that $(\theta,\theta)=2$.  The fundamental 
	    Weyl chamber consisting of those weights $\lambda$ such that $(\lambda,\alpha_i)$ is a positive integer 
	    for $i=1,\ldots,n$.  The fundamental Weyl alcove is the subset of the Weyl chamber such that $(\lambda,\theta) \leq l$.
        Text
            In the example below, we see that the Weyl alcove of $sl_3$ at level 3 contains 10 weights.
	Example 
	    g=simpleLieAlgebra(sl_3)
	    weylAlcove(3,g)
///

TEST ///
    g=simpleLieAlgebra(sl_3)
    assert(set(weylAlcove(3,g)) ===set {{0, 0}, {1, 0}, {0, 1}, {1, 1}, {2, 0}, {2, 1}, {0, 2}, {1, 2}, {3, 0}, {0, 3}}) 
///	
	

doc ///
     Key
          LieAlgebraModule
     Headline
          class for Lie algebra modules
     Description
          Text 
     	       This class represents Lie algebra modules.  Currently only irreducible modules over simple Lie algebras over the complex numbers are supported. 
	       The data used to specify a Lie algebra module is the Lie algebra and the decomposition of the module into irreducible Lie algebra modules. 
	  Example
	       g=simpleLieAlgebra(sl_3)
	       M=irreducibleLieAlgebraModule({1,1},g)                   
///

doc ///
     Key
          irreducibleLieAlgebraModule
	  (irreducibleLieAlgebraModule,List,LieAlgebra)
     Headline
          construct the irreducible Lie algebra module with given highest weight
     Usage
          irreducibleLieAlgebraModule(w,g)
     Inputs
          w:List
	       the highest weight of the desired module
	  g:LieAlgebra     
     Outputs
          M:LieAlgebraModule
     Description
          Text
               This function creates the irreducible Lie algebra module with a given highest weight.
          Example
	       g=simpleLieAlgebra(sl_3)
               irreducibleLieAlgebraModule({1,1},g)
///

TEST ///
     assert(irreducibleLieAlgebraModule({1,1},simpleLieAlgebra(sl_3)) === new LieAlgebraModule from {"LieAlgebra"=>simpleLieAlgebra(sl_3),"highestWeight"=>{1,1}, "DecompositionIntoIrreducibles"=>new HashTable from {{1,1}=>1}, "isIrreducible"=>true})
///	
		
doc ///
     Key
          multiplicityOfWeightInLieAlgebraModule
	  (multiplicityOfWeightInLieAlgebraModule,List,LieAlgebraModule)
	  (multiplicityOfWeightInLieAlgebraModule,String,ZZ,List,List)
	  (multiplicityOfWeightInLieAlgebraModule,LieAlgebra,List,List)
     Headline
          compute the multiplicity of a weight in a Lie algebra module
     Usage
          multiplicityOfWeightInLieAlgebraModule(v,M)
     Inputs
          v:List
	  M:LieAlgebraModule
     Outputs
          k:ZZ
     Description
          Text
	       This function implements Freudenthal's recursive algorithm; see Humphreys, {\it Introduction to Lie Algebras and Representation Theory}, 
	       Section 22.3. This function returns the multiplicity of the weight v in the irreducible Lie algebra module M.  For Type A (that is, $g = sl_k$), 
	       these multiplicities are also known as the Kostka numbers.  
	  Text     
	       The example below shows that the $sl_3$ module with highest weight $(2,1)$ contains the weight $(-1,1)$ with multiplicity 2.
          Example
	        g=simpleLieAlgebra(sl_3)
		V=irreducibleLieAlgebraModule({2,1},g)
	        multiplicityOfWeightInLieAlgebraModule({-1,1},V)
     SeeAlso
          weightDiagram
	     
///

TEST ///
     assert(multiplicityOfWeightInLieAlgebraModule("A",2,{2,1},{-1,1}) === 2)
///

doc ///
     Key
          weightDiagram
	  (weightDiagram,LieAlgebraModule)
	  (weightDiagram,String,ZZ,List)
     Headline
          computes the weights in a Lie algebra module and their multiplicities
     Usage
          weightDiagram(V)
     Inputs
          V:LieAlgebraModule
     Outputs
          T:HashTable
     Description
          Text
	       This function implements Freudenthal's recursive algorithm; see Humphreys, {\it Introduction to Lie Algebras and Representation Theory}, 
	       Section 22.3.  Let V be the irreducible g module with highest weight v.  This function returns a hash table whose keys are the weights 
	       appearing in V and whose values are the multiplicities of these weights.  
          Example
	       g=simpleLieAlgebra(sl_3)
	       V=irreducibleLieAlgebraModule({2,1},g)
	       weightDiagram(V)
     SeeAlso
          multiplicityOfWeightInLieAlgebraModule     
///

TEST ///
     assert(weightDiagram(irreducibleLieAlgebraModule({2,1},simpleLieAlgebra(sl_3))) === new HashTable from {{{-1, 1}, 2}, {{1, 0}, 2}, {{3, -1}, 1}, {{-2, 0}, 1}, {{0, -1}, 2}, {{2, -2}, 1}, {{-2, 3}, 1}, {{0, 2}, 1}, {{2, 1}, 1}, {{-1, -2}, 1}, {{1, -3}, 1}, {{-3, 2}, 1}})
///	

	

doc ///
     Key
	  (symbol **, LieAlgebraModule, LieAlgebraModule)
     Headline
          tensor product of LieAlgebraModules
     Usage
          U ** V
     Inputs
          U:LieAlgebraModule
	  V:LieAlgebraModule
     Outputs
          W:LieAlgebraModule
     Description
          Text
	       Computes the tensor product of two Lie algebra modules.  
          Example
	       g=simpleLieAlgebra(sl_3)
	       U=irreducibleLieAlgebraModule({4,2},g)
	       V=irreducibleLieAlgebraModule({3,1},g)
	       U**V
     SeeAlso
          tensorCoefficient
///

TEST ///
     assert(irreducibleLieAlgebraModule({2,1},simpleLieAlgebra(sl_3)) ** irreducibleLieAlgebraModule({1,2},simpleLieAlgebra(sl_3)) === new LieAlgebraModule from {"LieAlgebra"=>simpleLieAlgebra(sl_3),"isIrreducible"=>false, ,"DecompositionIntoIrreducibles"=>new HashTable from {{{1, 1}, 2}, {{3, 0}, 1}, {{1, 4}, 1}, {{3, 3}, 1}, {{0, 0}, 1}, {{0, 3}, 1}, {{2, 2}, 2}, {{4, 1}, 1}} })
///

doc ///
     Key
          tensorCoefficient
	  (tensorCoefficient,LieAlgebraModule,LieAlgebraModule,LieAlgebraModule)     
     Headline
          computes the multiplicity of W in U tensor V
     Usage
          tensorCoefficient(U,V,W)
     Inputs
          U:LieAlgebraModule
	  V:LieAlgebraModule
	  W:LieAlgebraModule
     Outputs
          k:ZZ
     Description
          Text
	       This function implements the Racah-Speiser algorithm; see Di Francesco, Mathieu, and Senechal, 
	       {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, Section 13.5.2. 
	       Given three irreducible Lie algebra modules U, V, and W, the function returns the multiplicity of W in $U \otimes V$.  In Type A, 
	       these are related to the Littlewood-Richardson coefficients (though in this package, weights are specified by their Dynkin labels,  
	       rather than as partitions).  
          Text
	       The example below shows that for $g=sl_3$ and $\lambda=2 \omega_1 + \omega_2$, $\mu= \omega_1 + 2 \omega_2$, and 
	       $\nu= 2 \omega_1 + 2 \omega_2$, the tensor product of sl_3 modules $V_{\lambda} \otimes V_{\mu}$ contains two copies of $V_{\nu}$.
          Example
	       g=simpleLieAlgebra(sl_3)
	       U=irreducibleLieAlgebraModule({2,1},g)
	       V=irreducibleLieAlgebraModule({1,2},g)
	       W=irreducibleLieAlgebraModule({2,2},g)
	       tensorCoefficient(U,V,W)
     SeeAlso
          (symbol **, LieAlgebraModule, LieAlgebraModule)
///


TEST ///
     g=simpleLieAlgebra(sl_3);
     U=irreducibleLieAlgebraModule({2,1},g);
     V=irreducibleLieAlgebraModule({1,2},g);
     W=irreducibleLieAlgebraModule({2,2},g);
     assert(tensorCoefficient(U,V,W) === 2)         
///
		


doc ///
    Key
        fusionCoefficient
	(fusionCoefficient,LieAlgebraModule,LieAlgebraModule,LieAlgebraModule,ZZ)     
    Headline
        computes the multiplicity of W in the fusion product of U and V
    Usage
        fusionCoefficient(U,V,W,l)
    Inputs
        U:LieAlgebraModule
	V:LieAlgebraModule
	W:LieAlgebraModule
        l:ZZ	
    Description
        Text
	    This function implements the Kac-Walton algorithm; see Di Francesco, Mathieu, and Senechal, {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, Section 16.2.2.  Given three irreducible Lie algebra modules U, V, and W, the function returns the multiplicity of W in the fusion product of $U$ and $V$ at level $l$.
        Text 
            The Weyl group of a simple Lie algebra is finite; in contrast, the affine Weyl group of an affine Lie algebra is infinite.  To keep Macaulay2 from trying to compute infinitely long words in this group, the default length of allowed words is set to max {10, rank($\mathbf{g}$)+1}.   The user may override this with the optional argument "MaxWordLength". 
        Text
	    The example below shows that for $g=sl_3$ and $\lambda=2 \omega_1 + \omega_2$, $\mu= \omega_1 + 2 \omega_2$, and $\nu= 2 \omega_1 + 2 \omega_2$, the level 3 fusion product  $V_{\lambda} \otimes_3  V_{\mu}$ contains one copy of $V_{\nu}$.
        Example
	    g=simpleLieAlgebra(sl_3);
	    U=irreducibleLieAlgebraModule({2,1},g);
	    V=irreducibleLieAlgebraModule({1,2},g);
	    W=irreducibleLieAlgebraModule({2,2},g);
	    fusionCoefficient(U,V,W,3)
///

doc ///
    Key
        fusionProduct
	(fusionProduct,LieAlgebraModule,LieAlgebraModule,ZZ)     
    Headline
        computes the multiplicities of irreducibles in the decomposition of the fusion product of U and V
    Usage
        fusionProduct(U,V,l)
    Inputs
        U:LieAlgebraModule
	V:LieAlgebraModule
        l:ZZ
    Description
        Text
	    This function implements the Kac-Walton algorithm; see Di Francesco, Mathieu, and Senechal, {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, Section 16.2.2.  Given two irreducible Lie algebra modules U and V, the function returns the fusion product of $U$ and $V$ at level $l$.  (We are abusing notation and terminology here; the fusion product is really a product for modules over an affine Lie algebra.  However, since the Kac-Walton algorithm is defined entirely using the combinatorics of the root system of the underlying finite-dimensional Lie algebra, we may therefore use the Kac-Walton algorithm to define a product on Lie algebra modules as well.)  
        Text 
            The Weyl group of a simple Lie algebra is finite; in contrast, the affine Weyl group of an affine Lie algebra is infinite.  To keep Macaulay2 from trying to compute infinitely long words in this group, the default length of allowed words is set to max {10, rank($\mathbf{g}$)+1}.   The user may override this with the optional argument "MaxWordLength". 
        Text
	    The example below shows that for $g=sl_3$ and $\lambda=2 \omega_1 + \omega_2$, $\mu= \omega_1 + 2 \omega_2$, and $\nu= 2 \omega_1 + 2 \omega_2$, the level 3 fusion product  $V_{\lambda} \otimes_3  V_{\mu}$ contains one copy of $V_{\nu}$.
        Example
	    g=simpleLieAlgebra(sl_3);
	    U=irreducibleLieAlgebraModule({2,1},g);
	    V=irreducibleLieAlgebraModule({1,2},g);
	    peek fusionProduct(U,V,3)
///


TEST ///
     g=simpleLieAlgebra(sl_3);
     U=irreducibleLieAlgebraModule({2,1},g);
     V=irreducibleLieAlgebraModule({1,2},g);
--     assert(fusionCoefficient(U,V,W,3) === 1)         
///



doc ///
     Key
          casimirScalar
	  (casimirScalar,LieAlgebraModule)
	  (casimirScalar,String,ZZ,List)
     Headline
          computes the scalar by which the Casimir operator acts on an irreducible Lie algebra module
     Usage
          casimirScalar(V)
     Inputs 
          V:LieAlgebraModule
     Outputs
          k:QQ
     Description
          Text
	       The Casimir operator is an element of the universal enveloping algebra that acts by a scalar on each irreducible Lie algebra module.  One has 
	       $c(\mu) = (\mu,\mu) + 2(\mu,\rho)$, where $\rho$ is half the sum of the positive weights and (,) is the Killing form scaled so that 
	       $(\theta,\theta)=2$, where $\theta$ is the highest root.  See Di Francesco, Mathieu, and Senechal, 
	       {\it Conformal Field Theory}, Springer Graduate Texts in Theoretical Physics, (13.127) p. 512, and (13.46) p. 499.
	  Text     
               In the example below, we see that the Casimir operator acts as multiplication by 8/3 on the standard representation of $sl_3$.  
          Example
	       g=simpleLieAlgebra(sl_3)
	       V=irreducibleLieAlgebraModule({1,0},g)
	       casimirScalar(V)
///

TEST ///
     g=simpleLieAlgebra(sl_3)
     V=irreducibleLieAlgebraModule({1,0},g)
     assert(casimirScalar(V) === 8/3)
///


doc ///
     Key
          isIsomorphic
	  (isIsomorphic,LieAlgebraModule,LieAlgebraModule)
     Headline
          tests whether two Lie algebra modules are isomorphic
     Usage
          isIsomorphic(V,W)
     Inputs
          V:LieAlgebraModule
	  W:LieAlgebraModule
     Outputs
          b:Boolean
     Description
          Text
	       To test whether two Lie algebra modules are isomorphic, we first test whether they are modules over the same Lie algebra, and if so, then test 
	       whether they have the same decomposition into irreducible Lie algebra modules.
          Example
	       g=simpleLieAlgebra(sl_3)
	       M=irreducibleLieAlgebraModule({2,1},g)
	       N=irreducibleLieAlgebraModule({1,2},g)
	       Z=irreducibleLieAlgebraModule({0,0},g)
	       isIsomorphic(M,N)
	       isIsomorphic(M,M)
	       isIsomorphic(M,M**Z)
	       isIsomorphic(M**N,N**M)
///

TEST ///
     g=simpleLieAlgebra(sl_3);
     M=irreducibleLieAlgebraModule({2,1},g);
     N=irreducibleLieAlgebraModule({1,2},g);
     Z=irreducibleLieAlgebraModule({0,0},g)'
     assert(isIsomorphic(M,N) === false)
     assert(isIsomorphic(M,M) === true)
     assert(isIsomorphic(M,M**Z) === true)
     assert(isIsomorphic(M**N,N**M) ===true)
///

doc ///
    Key
        MaxWordLength
    Headline
        @TO Option@ to specify the allowable length of words in the affine Weyl group when computing fusion products.
///


endPackage "LieTypes" 
