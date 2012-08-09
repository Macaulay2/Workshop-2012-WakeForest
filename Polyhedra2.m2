--*- coding: utf-8 -*-
---------------------------------------------------------------------------
--
-- PURPOSE: Computations with convex polyhedra 
-- PROGRAMMER : Nathan Ilten, Josephine Yu, Qingchun Ren 
-- UPDATE HISTORY : August 2012 
---------------------------------------------------------------------------
newPackage("Polyhedra2",
    Headline => "A package for computations with convex polyhedra",
    Version => ".1",
    Date => "August 5, 2011",
    Authors => {
         {Name => "Nathan Ilten",
	  HomePage => "http://math.berkeley.edu/~nilten",
	  Email => "nilten@math.berkeley.edu"},
     	  {Name => "Qingchun Ren"},
	  {Name => "Josephine Yu"}
     },
    Configuration => {"UsePolymake"=>false,"PolymakePath"=>"./"},
    DebuggingMode => true
    )

---------------------------------------------------------------------------
-- COPYRIGHT NOTICE:
--
-- Copyright 2012 Nathan Ilten, Josephine Yu, and Qingchun Ren 
-- Some parts copyright 2010 Rene Birkner
--
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see <http://www.gnu.org/licenses/>.
--
---------------------------------------------------------------------------
UsePolymake = (options Polyhedra2).Configuration#"UsePolymake"
PolymakePath = (options Polyhedra2).Configuration#"PolymakePath"

export {
     	  "latticePoints",
     	  "isCompact",
	  "affinePreimage",
     	  "affineImage",
        "hilbertBasis",
     	"coneToPolyhedron",
	"directProduct",
	"UsePolymake",
	"PolymakePath",
     	"emptyPolyhedron",
	"isEmpty",
	"minkowskiSum",
	"dualCone",
	"affineHull",
	"intersection",
	"linSpace",
	"vertices",
	"rays",
	"ambDim",
	"hyperplanes",
	"halfspaces",
	"convexHull", 
	"posHull"}
	
needsPackage "FourierMotzkin"
needsPackage "PolyhedralObjects"
if UsePolymake then needsPackage "PolymakeInterface"


Cone == Cone := (C1,C2)->(
     (set entries rays C1 === set entries rays C2) and 
     image transpose linSpace C1==image transpose linSpace C2
     )

Polyhedron == Polyhedron := (C1,C2)->(
     (set entries rays C1 === set entries rays C2) and 
     (set entries vertices C1 === set entries vertices C2) and 
     image transpose linSpace C1==image transpose linSpace C2
     )

convexHull = method()
convexHull (Matrix,Matrix,Matrix):=(M,N,L)->(
     new Polyhedron from hashTable {
	  "InputRays"=>promote(homCoordinates(transpose M,transpose N),QQ),
     	  "InputLineality"=>promote(homRays(transpose L),QQ)}
     )

convexHull (Matrix,Matrix):=(M,N)->(convexHull(M,N,map(QQ^(numRows M),QQ^0,0)))
     
convexHull Matrix :=M->(convexHull(M,map(QQ^(numRows M),QQ^0,0)))

convexHull (Polyhedron,Polyhedron):=(P1,P2)->convexHull {P1,P2}
convexHull (Cone,Cone):=(C1,C2)->posHull {C1,C2}

convexHull List := L->(
   datalist:=apply(L,P->(
       if instance(P,Polyhedron) then (
	    if not P#?"InputRays" and not P#?"Rays" then (rays P; linSpace P);
	    if P#?"Rays" and P#?"LinealitySpace" then return(P#"Rays",P#"LinealitySpace");
	    if not P#?"InputLineality" then P#"InputLineality"=map(QQ^0,numColumns P#"InputRays",0);
	    return (P#"InputRays",P#"InputLineality")
	    )
       else if instance(P,Cone) then (
	    if not P#?"InputRays" and not P#?"Rays" then (rays P; linSpace P);
	    if P#?"Rays" then return(homRays P#"Rays",homRays P#"LinealitySpace");
    	    if not P#?"InputLineality" then P#"InputLineality"=map(QQ^0,numColumns P#"InputRays",0);
	    return (homRays P#"InputRays",homRays P#"InputLineality")	   
    	   )
	else if instance(P,Matrix) then (
	     return (homPoints transpose promote(P,QQ),transpose map(QQ^(1+numRows P),QQ^0,0))
		    )
	      else return (promote(homCoordinates(transpose P#0,transpose P#1),QQ),
		   transpose map(QQ^(1+numRows P),QQ^0,0))));
    vlist:=matrix apply(datalist,i->{i#0});
    llist:=matrix apply(datalist,i->{i#1});
    new Polyhedron from hashTable {
	  "InputRays"=>vlist,
     	  "InputLineality"=>llist})


posHull = method()
posHull (Matrix, Matrix):= (M,N)-> (
     new Cone from hashTable {
	  "InputLineality"=>promote(transpose N,QQ),
  	  "InputRays"=>promote(transpose M,QQ)}
     )

posHull Matrix:=M ->(posHull(M,map(QQ^(numRows M),QQ^0,0)))
posHull (Cone,Cone):=(C1,C2)->(posHull {C1,C2})
posHull Polyhedron:=C1->(posHull {C1})
     
posHull List:=L->(
     datalist:=apply(L,P->(
	       if instance(P,Polyhedron) then (
		    if not P#?"Rays" and not P#?"InputRays" then (rays P,linSpace P);
		    if P#?"Rays" then return(dehom P#"Rays",dehom P#"LinealitySpace");
	    	    if not P#?"InputLineality" then P#"InputLineality"=map(QQ^0,numColumns P#"InputRays",0);
		    return(dehom P#"InputRays",dehom P#"InputLineality")		    
		    )
	       else if instance(P,Cone) then (
		    if not P#?"Rays" and not P#?"InputRays" then (rays P; linSpace P);
		    if P#?"Rays" then return(P#"Rays",P#"LinealitySpace");
	    	    if not P#?"InputLineality" then P#"InputLineality"=map(QQ^0,numColumns P#"InputRays",0);
		    return(P#"InputRays",P#"InputLineality")		    		    
		    )
	       else if instance(P,Matrix) then (
		    return(promote(transpose P,QQ),map(QQ^0,numRows P,0))
		    )
	       else (
		    return(transpose P#0,transpose P#1)		    
		    )
	       ));
     rlist:= matrix apply(datalist,i->{i#0});
     llist:= matrix apply(datalist,i->{i#1});
     new Cone from hashTable {
	  "InputLineality"=>llist,
  	  "InputRays"=>rlist}     
     )

intersection = method()
intersection (Matrix,Matrix):=(M,N)->(
     if not numColumns N ==1 then return new Cone from hashTable {
	  "Equations"=>promote(- N,QQ),
  	  "Inequalities"=>promote(- M,QQ)};
     intersection(M,N,map(QQ^0,QQ^(1+numColumns M),0),map(QQ^0,QQ^0,0))
     )	  

intersection Matrix:=M->(intersection(M,map(QQ^0,QQ^(numColumns M),0)))

intersection (Matrix,Matrix,Matrix,Matrix):=(M,v,N,w)->(
     new Polyhedron from hashTable {
	  "Inequalities"=>promote(v|(-M),QQ),
 	  "Equations"=>promote(w|(-N),QQ)
	  }
     )     

intersection (Cone,Cone):=(P1,P2)->intersection {P1,P2}
intersection (Polyhedron,Polyhedron):=(P1,P2)->intersection {P1,P2}

intersection List := L -> (
     datalist:=apply(L,P->(
	       if instance(P,Polyhedron) then (
		    if not P#?"Facets" and not P#?"Inequalities" then (hyperplanes P;halfspaces P);
		    if P#?"Facets" then return(P#"Facets",P#"LinearSpan");
		    if not P#?"Equations" then P#"Equations"=map(QQ^0,numColumns P#"Inequalities",0);
		    return(P#"Inequalities",P#"Equations")		    
		    )
	       else if instance(P,Cone) then (
		    if not P#?"Facets" and not P#?"Inequalities" then (hyperplanes P;halfspaces P);
		    if P#?"Facets" then return(homRays P#"Facets",homRays P#"LinearSpan");
		    if not P#?"Equations" then P#"Equations"=map(QQ^0,numColumns P#"Inequalities",0);		    
		    return(homRays P#"Inequalities",homRays P#"Equations")		    		    
		    )
	       else if instance(P,Sequence) then (
		    return(promote(P#1|(-P#0),QQ),map(QQ^(numRows P#0),QQ^(1+numColumns P#0),0))
		    )
	       else (
		    return(map(QQ^(numRows P#0),QQ^(1+numColumns P#0),0),promote(P#1|(-P#0),QQ))		    
		    )
	       ));
     ilist:=matrix apply(datalist,i->{i#0});
     elist:=matrix apply(datalist,i->{i#1});
     new Polyhedron from hashTable{
	  "Inequalities"=>ilist,
 	  "Equations"=>elist}
     )

hyperplanes = method()
hyperplanes Cone := P -> (
	if P#?"LinearSpan" then return P#"LinearSpan";
	if UsePolymake then runPolymake(P,"LinearSpan")
	else computeFacets P;
	P#"LinearSpan")

hyperplanes Polyhedron := P -> (
	if not P#?"LinearSpan" then 
	if UsePolymake then runPolymake(P,"LinearSpan")
	else computeFacets P;
	M:=P#"LinearSpan";
	(-M_(toList(1..numColumns M-1)),M_{0})
	)


halfspaces = method()
halfspaces Cone := P -> (
	if P#?"Facets" then return -P#"Facets";
	if UsePolymake then runPolymake(P,"Facets")
	else computeFacets P;	
	-P#"Facets")
   
halfspaces Polyhedron := P -> (
	if not P#?"Facets" then 
	if UsePolymake then runPolymake(P,"Facets")
	else computeFacets P;
	computeFacets P;
	M:=P#"Facets";
	(-M_(toList(1..numColumns M-1)),M_{0})
	)



rays = method()
rays Cone := P -> (
	if P#?"Rays" then return transpose P#"Rays";
	computeRays P;
	transpose P#"Rays")
   
rays Polyhedron := P -> (
	if not P#?"Rays" then computeRays P;
	transpose (dehomCoordinates P#"Rays")_1)   

vertices = method()
vertices Polyhedron := P -> (
	if not P#?"Rays" then computeRays P;
	transpose (dehomCoordinates P#"Rays")_0)   

linSpace = method()
linSpace Cone := P -> (
	if P#?"LinealitySpace" then return transpose P#"LinealitySpace";
	computeRays P;
	transpose P#"LinealitySpace")
   

linSpace Polyhedron := P -> (
	if P#?"LinealitySpace" then return transpose P#"LinealitySpace";
	computeRays P;
	transpose P#"LinealitySpace")
   


ambDim = method ()
ambDim Cone:=C->(
     if not C#?"AmbientDim" then (
     if C#?"Rays" then C#"AmbientDim"=numColumns C#"Rays" 	  
     else if C#?"InputRays" then C#"AmbientDim"=numColumns C#"InputRays" 	  
     else if C#?"Inequalities" then C#"AmbientDim"=numColumns C#"Inequalities" 	  
     else if C#?"Facets" then C#"AmbientDim"=numColumns C#"Facets"
     else error ("Your cone is ill-defined")); 	  
      C#"AmbientDim")
 
ambDim Polyhedron:=C->(
     if not C#?"AmbientDim" then (
     if C#?"Rays" then C#"AmbientDim"=numColumns C#"Rays" -1 	  
     else if C#?"InputRays" then C#"AmbientDim"=numColumns C#"InputRays" -1	  
     else if C#?"Inequalities" then C#"AmbientDim"=numColumns C#"Inequalities"-1 	  
     else if C#"Facets" then C#"AmbientDim"=numColumns C#"Facets"-1
     else error ("Your cone is ill-defined")); 	  
      C#"AmbientDim")


dim Cone:=C->(if not C#?"Dim" then C#"Dim"=ambDim C-numRows ((hyperplanes C));C#"Dim")
dim Polyhedron:=C->(if not C#?"Dim" then C#"Dim"=ambDim C-numRows ((hyperplanes C)_0);C#"Dim")

affineHull = method ()
affineHull Polyhedron := P->(hp:=hyperplanes P;
     intersection(map(QQ^0,QQ^(1+ambDim P),0),map(QQ^0,QQ^0,0),hp#0,hp#1))

dualCone = method ()
dualCone Cone:=C->(
     C2:=new Cone from hashTable {};
     if C#?"InputRays" then C2#"Inequalities"=C#"InputRays";
     if C#?"InputLineality" then C2#"Equations"=C#"InputLineality";
     if C#?"Rays" then C2#"Facets"=C#"Rays";     
     if C#?"LinealitySpace" then C2#"LinearSpan"=C#"LinealitySpace";
     if C#?"Facets" then C2#"Vertices"=C#"Facets";
     if C#?"LinearSpan" then C2#"LinealitySpace"=C#"LinearSpan";
     if C#?"Inequalities" then C2#"InputRays"=C#"Inequalities";
     if C#?"Equations" then C2#"InputLineality"=C#"Equations";
     C2)


affineImage = method ()
affineImage (Matrix,Polyhedron,Matrix) := (A,P,v)->(
     if not P#?"InputRays" and not P#?"Rays" then vertices P;
     Q:=new Polyhedron from hashTable {};
     M:=(transpose (map(QQ^1,1+numColumns A,(i,j)->if j==0 then 1 else 0)||(v|A)));
     if P#?"Rays" then (Q#"InputRays"=P#"Rays"*M;     
     	  Q#"InputLineality"=P#"LinealitySpace"*M)
     else  (Q#"InputRays"=P#"InputRays"*M;
      Q#"InputLineality"=P#"InputLineality"*M);
     Q)

affineImage (Matrix,Polyhedron) := (A,P)->(affineImage(A,P,map(QQ^(numRows A),QQ^1,0)))
     
affineImage (Polyhedron,Matrix) := (P,v)->(affineImage(id_(QQ^(ambDim P)),P,v))     



affineImage (Matrix,Cone):=(A,P)->(
     if not P#?"InputRays" and not P#?"Rays" then rays P;
     Q:=new Cone from hashTable {};
     if P#?"Rays" then (Q#"InputRays"=P#"Rays"*(transpose (A));     
     	  Q#"InputLineality"=P#"LinealitySpace"*(transpose (A)))
     else  (Q#"InputRays"=P#"InputRays"*(transpose (A));
      Q#"InputLineality"=P#"InputLineality"*(transpose (A)));
     Q)

affineImage (Matrix,Cone,Matrix) := (A,P,v)->(
     if v==0 then return affineImage(A,P);
     affineImage(A,coneToPolyhedron P,v))

affineImage (Cone,Matrix) :=(P,v)->(
     if v==0 then return P;
     affineImage(coneToPolyhedron,v))

affinePreimage = method ()
affinePreimage(Matrix,Polyhedron,Matrix) := (A,P,b) -> (
     --note: could set up to use eq/ineq if facets don't exist
     -- Checking for input errors
     if P#"ambient dimension" =!= numRows A then error("Matrix source must be ambient space");
     if numRows A =!= numRows b then error("Vector must lie in target space of matrix");
     if numColumns b =!= 1 then error("Second argument must be a vector");
     -- Constructing the new half-spaces and hyperplanes
     (M,v) := halfspaces P;
     (N,w) := hyperplanes P;
     v = v - (M * b);
     w = w - (N * b);
     M = M * A;
     N = N * A;
     intersection(M,v,N,w))


affinePreimage(Matrix,Polyhedron) := (A,P) -> (
     affinePreimage(A,P,map(target A,QQ^1,0)))

affinePreimage(Polyhedron,Matrix) := (P,b) -> affinePreimage(map(QQ^(ambDim P),QQ^(ambDim P),1),P,b)

affinePreimage(Matrix,Cone,Matrix) := (A,C,b) -> if b == 0 then affinePreimage(A,C) else affinePreimage(A,coneToPolyhedron C,b)

affinePreimage(Matrix,Cone) := (A,C) -> posHull affinePreimage(A,coneToPolyhedron C)

affinePreimage(Cone,Matrix) := (C,b) -> affinePreimage(coneToPolyhedron C,b)

latticePoints = method(TypicalValue => List)
latticePoints Polyhedron := P -> (
     if not P#?"LatticePoints" then (
	  -- Checking for input errors
	  if  not isCompact P then error("The polyhedron must be compact");
	  -- Recursive function that intersects the polyhedron with parallel hyperplanes in the axis direction
	  -- in which P has its minimum extension
	  latticePointsRec := P -> (
	       -- Finding the direction with minimum extension of P
	       V := entries vertices P;
	       n := ambDim P;
	       print n;
	       minv := apply(V,min);
	       maxv := apply(V,max);
	       minmaxv := maxv-minv;
	       pos := min minmaxv;
	       pos = position(minmaxv,v -> v == pos);
	       -- Determining the lattice heights in this direction
	       L := toList({{ceiling minv_pos}}..{{floor maxv_pos}});
	       -- If the dimension is one, then it is just a line and we take the lattice points
	       if n == 1 then apply(L,matrix)
	       -- Otherwise intersect with the hyperplanes and project into the hyperplane
	       else flatten apply(L,p -> (
			 NP := intersection {P,{map(QQ^1,QQ^n,(i,j) -> if j == pos then 1 else 0),matrix p}};
			 if numColumns vertices P == 1 then (
			      v := vertices NP;
			      if promote(substitute(v,ZZ),QQ) == v then substitute(v,ZZ) else {})
			 else (
			      A := matrix drop((entries id_(QQ^n)),{pos,pos});
			      apply(latticePointsRec affineImage(A,NP),v -> v^{0..(pos-1)} || matrix p || v^{pos..(n-2)})))));
	  -- Checking if the polytope is just a point
	  if dim P == 0 then P#"LatticePoints" = if liftable(vertices P,ZZ) then transpose lift(vertices P,ZZ) else map(ZZ^0,ZZ^(ambDim P,0))
	  -- Checking if the polytope is full dimensional
	  else if (dim P == ambDim P) then P#"LatticePoints" = transpose matrix {latticePointsRec P}
	  -- If not checking first if the affine hull of P contains lattice points at all and if so projecting the polytope down
	  -- so that it becomes full dimensional with a map that keeps the lattice
	  else (
	       (M,v) := hyperplanes P;
	       -- Finding a lattice point in the affine hull of P
	       b := if all(entries M, e -> gcd e == 1) then (
		    -- Computing the Smith Normal Form to solve the equation over ZZ
		    (M1,Lmatrix,Rmatrix) := smithNormalForm substitute(M,ZZ);
		    v1 := flatten entries (Lmatrix*v);
		    w := apply(numRows M1, i -> M1_(i,i));
		    -- Checking if the system is at least solvable over QQ
		    if all(#w, i -> w#i != 0 or v1#i == 0) then (
			 -- If it is, then solve over QQ
			 w = apply(#w, i -> (v1#i/w#i,v1#i%w#i));
			 if all(w, e -> e#1 == 0) then (
			      -- If the solution is in fact in ZZ then return it
			      w = transpose matrix{apply(w,first) | toList(numColumns M1 - numRows M1:0)};
			      Rmatrix * w)));
	       -- If there is no lattice point in the affine hull then P has none
	       if b === null then P#"LatticePoints" = map(ZZ^0,ZZ^(ambDim P),0)
	       else (
		    A := gens ker substitute(M,ZZ);
		    -- Project the translated polytope, compute the lattice points and map them back
		    P#"LatticePoints" = transpose matrix apply(latticePoints affinePreimage(A,P,b),e -> substitute(A*e + b,ZZ)))));
     apply(numColumns P#"LatticePoints",i->(P#"LatticePoints")_i)
     )



emptyPolyhedron=method ()
emptyPolyhedron ZZ:=n->(
     if n < 1 then error("The ambient dimension must be positive");
     C:=convexHull map(QQ^n,QQ^0,0);
     C#"AmbientDim"=n;
     C#"Dim"=-1;
     C)
     

isEmpty=method()
isEmpty Polyhedron:=P->(dim P==-1)

isCompact = method(TypicalValue => Boolean)
isCompact Polyhedron := P -> (linSpace P == 0 and rays P == 0)


minkowskiSum = method()

minkowskiSum(Polyhedron,Polyhedron) := (P1,P2) -> (
     if (ambDim P1) =!= (ambDim P2) then error("Polyhedral objects must lie in the same space");
     if isEmpty P1 or isEmpty P2 then emptyPolyhedron ambDim P1 else if P1 == P2 then 2 * P1;
     V1 := vertices P1;
     V2 := vertices P2;
     R := promote(rays P1 | rays P2,QQ) | map(target V1,QQ^1,0);
     Vnew := map(target V1,QQ^0,0);
     -- Collecting all sums of vertices of P1 with vertices of P2
     Vnew = matrix {unique flatten apply(numColumns V1, i -> apply(numColumns V2, j -> V1_{i}+V2_{j}))};
     convexHull(Vnew,R))



minkowskiSum(Cone,Cone) := (C1,C2) -> (
     -- Checking for input errors
     if (ambDim C1) =!= (ambDim C2) then error("Cones must lie in the same space");
     posHull((rays C1)|(rays C2),(linSpace C1)|linSpace C2))


minkowskiSum(Cone,Polyhedron) := (C,P) -> minkowskiSum(coneToPolyhedron C,P)

minkowskiSum(Polyhedron,Cone) := (P,C) -> minkowskiSum(P,coneToPolyhedron C)

QQ * Polyhedron := (k,P) -> (
     -- Checking for input errors
     if k <= 0 then error("The factor must be strictly positiv");
     Q:=new Polyhedron from hashTable {};
     if P#?"InputRays" then Q#"InputRays"=homCoordinates(k*(dehomCoordinates P#"InputRays")_0,(dehomCoordinates P#"InputRays")_1);
     if P#"InputLineality" then Q#"InputLineality"=P#"InputLineality";
     if P#"Rays" then Q#"Rays"=homCoordinates(k*(dehomCoordinates P#"Rays")_0,(dehomCoordinates P#"Rays")_1);
     if P#?"LinealitySpace" then Q#"LinealitySpace"=P#"LinealitySpace";
     if P#?"Inequalities" then Q#"Inequalities"=((k*(P#"Inequalities")_{0})|(P#"Inequalities")_(toList(1..numColumns P#"Inequalities")));
     if P#?"Equations" then Q#"Equations"=P#"Equations";
     if P#?"Facets" then Q#"Facets"=((k*(P#"Facets")_{0})|(P#"Facets")_(toList(1..numColumns P#?"Facets")));
     if P#?"LinSpan" then Q#"LinSpan"=P#"LinSpan";
     if P#?"AmbDim" then Q#"AmbDim"=P#"AmbDim";
     if P#?"Dim" then Q#"Dim"=P#"Dim";
     Q)
      
coneToPolyhedron=method()
coneToPolyhedron Cone:=P->(
     Q:=new Polyhedron from hashTable {};
     if P#?"InputRays" then Q#"InputRays"=homRays(P#"InputRays");
     if P#?"InputLineality" then Q#"InputLineality"=homRays P#"InputLineality";
     if P#?"Rays" then Q#"Rays"=homRays P#"Rays";
     if P#?"LinealitySpace" then Q#"LinealitySpace"=homRays P#"LinealitySpace";
     if P#?"Inequalities" then Q#"Inequalities"=homRays P#"Inequalities";
     if P#?"Equations" then Q#"Equations"=homRays P#"Equations";
     if P#?"Facets" then Q#"Facets"=homRays P#"Facets";
     if P#?"LinSpan" then Q#"LinSpan"=homRays P#"LinSpan";
     if P#?"AmbDim" then Q#"AmbDim"=P#"AmbDim";
     if P#?"Dim" then Q#"Dim"=P#"Dim";      
      Q)


ZZ * Polyhedron := (k,P) -> promote(k,QQ) * P


Cone + Polyhedron := minkowskiSum
Cone + Cone := minkowskiSum

directProduct = method ()
directProduct(Cone,Polyhedron) :=(C,P)->directProduct((coneToPolyhedron C),P)
directProduct (Polyhedron ,Cone):=(P,C)->directProduct(P,(coneToPolyhedron C))

directProduct (Polyhedron, Polyhedron):=(P1,P2)->(
     --very lazy implementation; we should really check what keys exist
     C:=convexHull((vertices P1)++(vertices P2),(rays P1)++(rays P2),linSpace P1++linSpace P2);
     C#"LinealitySpace"=C#"InputLineality";
     C#"Rays"=C#"InputRays";
     C     )

directProduct (Cone, Cone):=(P1,P2)->(
     --very lazy implementation; we should really check what keys exist
     C:=posHull(rays P1++rays P2,linSpace P1++linSpace P2);
     C#"LinealitySpace"=C#"InputLineality";
     C#"Rays"=C#"InputRays";
     C
     )

PolyhedralObject * PolyhedralObject := directProduct
Polyhedron + Polyhedron := minkowskiSum
Polyhedron + Cone := minkowskiSum
--Non-exported stuff

--rows are coordinates as in Polymake
homCoordinates=(M,N)->((map(QQ^(numRows M),QQ^1,(i,j)->1)|M)||(map(QQ^(numRows N),QQ^1,0)|N))
homRays=(N)->(map(QQ^(numRows N),QQ^1,0)|N)
homPoints=(N)->(map(QQ^(numRows N),QQ^1,(i,j)->1)|N)
--makes first coordinate 1 or 0
normalizeCoordinates=M->transpose matrix {apply(numRows M,i->(v:=(transpose M)_{i};
	  if v_(0,0)==0 then return  v;
	  ((1/(v_(0,0)))*v)))}
--assume that coordinates are normalized
dehom=M->transpose (transpose (M_(toList(1..numColumns M-1))))
     
dehomCoordinates=M->(
     MT:=transpose M;
     DM:=transpose (M_(toList(1..numColumns M-1)));
     verticesp:=select(numRows M,i->(MT_{i})_(0,0)==1);
     raysp:=select(numRows M,i->(MT_{i})_(0,0)==0);
     (transpose DM_verticesp,transpose DM_raysp))


computeFacets = method ()
computeFacets Cone := C -> (
     local fm;
     if not C#?"Rays" and not C#?"InputRays" then computeRays C;
     if C#?"Rays" then fm=fourierMotzkin(transpose  C#"Rays",transpose C#"LinealitySpace")
     else fm=fourierMotzkin(transpose  C#"InputRays",transpose C#"InputLineality");
     C#"Facets"=-transpose fm_0;
     C#"LinearSpan"=-transpose fm_1;
     )
     
computeFacets Polyhedron :=C->(
     local fm;
     if not C#?"Rays" and not C#?"InputRays" then computeRays C;     
     if C#?"Rays" then fm=fourierMotzkin(transpose  C#"Rays",transpose C#"LinealitySpace")
     else fm=fourierMotzkin(transpose  C#"InputRays",transpose C#"InputLineality");
     C#"Facets"=-transpose fm_0;
     C#"LinearSpan"=-transpose fm_1;     
     )

computeRays = method ()
computeRays Cone := C -> (
     local fm;
     if not C#?"Facets" and not C#?"Inequalities" then computeFacets C;
     if C#?"Facets" then fm=fourierMotzkin(transpose C#"Facets",transpose C#"LinearSpan")
     else fm=fourierMotzkin(transpose C#"Inequalities",transpose C#"Equations");
     C#"Rays"=-transpose fm_0;
     C#"LinealitySpace"=-transpose fm_1;
     )

computeRays Polyhedron := C -> (
     local fm;
     if not C#?"Facets" and not C#?"Inequalities" then computeFacets C;
     if C#?"Facets" then fm=fourierMotzkin(
	  transpose (C#"Facets"||map(QQ^1,QQ^(numColumns C#"Facets"),(i,j)->(if j==0 then 1 else 0))),transpose C#"LinearSpan")
     else fm=fourierMotzkin(
	  transpose (C#"Inequalities"||map(QQ^1,QQ^(numColumns C#"Inequalities"),(i,j)->(if j==0 then 1 else 0))),transpose C#"Equations");
     C#"Rays"=normalizeCoordinates (-transpose fm_0);
     C#"LinealitySpace"=-transpose fm_1;
     )

-- PURPOSE : Computing the Hilbert basis of a Cone 
--   INPUT : 'C',  a Cone
--  OUTPUT : 'L',  a list containing the Hilbert basis as one column matrices 
hilbertBasis = method(TypicalValue => List)
hilbertBasis Cone := C -> (
     if C#?"HilbertBasis" then return (apply(numRows C#"HilbertBasis",i->(transpose C#"HilbertBasis")_{i}));
     -- Computing the row echolon form of the matrix M
     ref := M -> (
	  n := numColumns M;
	  s := numRows M;
	  BC := map(ZZ^n,ZZ^n,1);
	  m := min(n,s);
	  -- Scan through the first square part of 'M'
	  i := 0;
	  stopper := 0;
	  while i < m and stopper < n do (
		    -- Selecting the first non-zero entry after the i-th row in the i-th column
		    j := select(1,toList(i..s-1),k -> M_i_k != 0);
		    -- if there is a non-zero entry, scan the remaining entries and compute the reduced form for this column
		    if j != {} then (
			 j = j#0;
			 scan((j+1)..(s-1), k -> (
				   if M_i_k != 0 then (
					a := M_i_j;
					b := M_i_k;
					L := gcdCoefficients(a,b);
					a = substitute(a/(L#0),ZZ);
					b = substitute(b/(L#0),ZZ);
					M = M^{0..j-1} || (L#1)*M^{j} + (L#2)*M^{k} || M^{j+1..k-1} || (-b)*M^{j} + a*M^{k} || M^{k+1..s-1})));
			 if i != j then (
			      M = M^{0..i-1} || M^{j} || M^{i+1..j-1} || M^{i} || M^{j+1..s-1});
			 if M_i_i < 0 then M = M^{0..i-1} || -M^{i} || M^{i+1..s-1})
		    else (
			 M = M_{0..i-1} | M_{i+1..n-1} | M_{i};
			 BC = BC_{0..i-1} | BC_{i+1..n-1} | BC_{i};
			 i = i-1);
		    i = i+1;
		    stopper = stopper + 1);
	  (M,BC));
     -- Function to compute the/one preimage of h under A
     preim := (h,A) -> (
	  -- Take the generators of the kernel of '-h|A' and find an element with 1 as first entry -> the other entrys are a preimage
	  -- vector
	  N := gens ker(-h|A);
	  N = transpose (ref transpose N)#0;
	  N_{0}^{1..(numRows N)-1});
     A := -halfspaces C;
     if hyperplanes C =!= 0 then A = A || hyperplanes C || -hyperplanes C;
     A = substitute(A,ZZ);
     -- Use the project and lift algorithm to compute a basis of the space of vectors positive on 'A' whose preimages are the HilbertBasis
     (B,BC) := ref transpose A; 
     H := constructHilbertBasis B;
     BC = inverse transpose BC;
     C#"HilbertBasis"=transpose matrix {apply(H,h -> preim(BC*h,A))};
     (apply(numRows C#"HilbertBasis",i->(transpose C#"HilbertBasis")_{i})))
     

constructHilbertBasis = A -> (
    -- Defining the function to determine if u is lower v
    lowvec := (u,v) -> (
	 n := (numRows u)-1;
	 diffvec := flatten entries(u-v);
	 if all(diffvec, i -> i <= 0) then abs(u_(n,0)) <= abs(v_(n,0)) and (u_(n,0))*(v_(n,0)) >= 0
	 else false);
    -- Collecting data
    A = substitute(A,ZZ);
    H := {A^{0}_{0}};
    s := numRows A;
    n := numColumns A;
    --doing the project and lift algorithm step by step with increasing dimensions
    scan(n-1, i -> (
	      -- the set 'F' will contain the lifted basis vectors, 'B' are the first i+2 columns of 'A' as a rowmatrix,
	      -- the set 'H' contains the vectors from the last loop that are one dimension smaller
	      F := {};
	      B := transpose A_{0..(i+1)};
	      -- Decide between lifting the existing vectors (i > s-1) or also adding the next column of 'B'
	      if i < s-1 then (
		   -- Lifting the existing vectors from 'H'
		   F = apply(H, h -> (
			     j := 0;
			     while numRows h == i+1 do (
				  if isSubset(image(h || matrix{{j}}), image B) then h = (h || matrix{{j}});
				  j = j+1);
			     h));
		   -- Adding +- times the next column of 'B'
		   F = join(F,{B_{i+1}^{0..(i+1)},-B_{i+1}^{0..(i+1)}}))
	      else (
		   -- Lifting the existing vectors from 'H'
		   nullmap := map(ZZ^1,ZZ^s,0);
		   nullvec := map(ZZ^1,ZZ^1,0);
		   F = apply(H, h -> B*substitute(vertices intersection(nullmap,nullvec,B^{0..i},h),ZZ)));
	      -- Computing the S-pairs from the elements of 'F' and saving them in 'C'
	      C := select(subsets(#F,2), j -> (
			f := F#(j#0);
			g := F#(j#1);
			(f_(i+1,0))*(g_(i+1,0)) < 0 and f+g != 0*(f+g)));
	      C = apply(C, j -> F#(j#0)+F#(j#1));
	      -- The elements of 'F' are saved in 'G'
	      G := F;
	      j := 0;
	      -- Adding those elements of 'C' to 'G' that satisfy the "normalform" condition by increasing last entry
	      while C != {} do (
		   Cnow := partition(e -> sum drop(flatten entries e,-1) == j,C);
		   C = if Cnow#?false then Cnow#false else {};
		   Cnow = if Cnow#?true then select(Cnow#true, f -> all(G, g -> not lowvec(g,f))) else {};
		   Cnew := flatten apply(Cnow, f -> apply(select(G, g -> f_(i+1,0)*g_(i+1,0) < 0 and f+g != 0*(f+g)), g -> f+g));
		   if all(Cnew, e -> sum drop(flatten entries e,-1) != j) then j = j+1;
		   C = unique (C | Cnew);
		   G = unique (G | Cnow));
	      -- saving those elements of 'G' with positive last entry into 'H'
	      H = select(G, g -> g_(i+1,0) >= 0)));
    H)





beginDocumentation()




