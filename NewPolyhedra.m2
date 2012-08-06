--*- coding: utf-8 -*-
---------------------------------------------------------------------------
--
-- PURPOSE: Computations with convex polyhedra 
-- PROGRAMMER : Nathan Ilten 
-- UPDATE HISTORY : August 2012 
---------------------------------------------------------------------------
newPackage("NewPolyhedra",
    Headline => "A package for computations with convex polyhedra",
    Version => ".1",
    Date => "August 5, 2011",
    Authors => {
         {Name => "Nathan Ilten",
	  HomePage => "http://math.berkeley.edu/~nilten",
	  Email => "nilten@math.berkeley.edu"}},
    DebuggingMode => true
    )

---------------------------------------------------------------------------
-- COPYRIGHT NOTICE:
--
-- Copyright 2012 Nathan Ilten
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


export {"intersection",
	"linSpace",
	"vertices",
	"rays",
	"ambDim",
	"hyperplanes",
	"halfspaces",
	"PolyhedralObject", 
        "Polyhedron", 
	"Cone", 
	"Fan", 
	"PolyhedralComplex", 
	"convexHull", 
	"posHull"}
	
needsPackage "FourierMotzkin"



-- Defining the new type PolyhedralObject
PolyhedralObject = new Type of MutableHashTable
globalAssignment PolyhedralObject

-- Defining the new type Polyhedron
Polyhedron = new Type of PolyhedralObject
Polyhedron.synonym = "convex polyhedron"
globalAssignment Polyhedron

-- Defining the new type Cone
Cone = new Type of Polyhedron
Cone.synonym = "convex rational cone"
globalAssignment Cone

-- Defining the new type Fan
Fan = new Type of PolyhedralObject
globalAssignment Fan

-- Defining the new type PolyhedralComplex
PolyhedralComplex = new Type of PolyhedralObject
globalAssignment PolyhedralObject


-- PURPOSE : Computing the Convex Hull of a given set of points and rays
convexHull = method(TypicalValue => Polyhedron)

--   INPUT : 'Mvert'  a Matrix containing the generating points as column vectors
--		 'Mrays'  a Matrix containing the generating rays as column vectors
--  OUTPUT : 'P'  a Polyhedron
-- COMMENT : The description by vertices and rays is stored in P as well as the 
--           description by defining half-spaces and hyperplanes.
convexHull(Matrix,Matrix) := (Mvert,Mrays) -> (
	Mvert = chkZZQQ(Mvert,"points");
        Mrays = chkZZQQ(Mrays,"rays");
	new Polyhedron from {
		"genlinealitySpace" => map(QQ^(numgens target Mrays),QQ^1,0),
		"genpoints" => Mvert,
		"genrays" => Mrays}
	)

--   INPUT : 'M'  a Matrix containing the generating points as column vectors
convexHull Matrix := M -> (
	-- Checking for input errors
	M = chkZZQQ(M,"points");
	if numRows M == 0 then M = matrix{{0}};
	if numColumns M == 0 then M = map(target M,QQ^1,0);
	-- Generating the zero ray R
	R := map(target M,QQ^1,0);
	convexHull(M,R))


--   INPUT : '(P1,P2)'  two polyhedra
convexHull(Polyhedron,Polyhedron) := (P1,P2) -> convexHull{P1,P2}


--   INPUT : 'L',   a list of Cones, Polyhedra, vertices given by M, 
--     	    	    and (vertices,rays) given by '(V,R)'

convexHull List := L -> (
     vrlist:=apply(L,P->(
	if instance(P,Polyhedron) then (
		if P#?"vertices" then return (P#"vertices",P#"rays",P#"linealitySpace");
		if P#?"genpoints" then return (P#"genpoints",P#"genrays",P#"genlinealitySpace");
		computeVertices P;
		return (P#"vertices",P#"rays",P#"linealitySpace"));
	if instance(P,Matrix) then return (chkZZQQ(P,"points"),map(QQ^(numgens target P),QQ^1,0),map(QQ^(numgens target P),QQ^1,0));
	(chkZZQQ(P#0,"points"),chkZZQQ(P#1,"rays",map(QQ^(numgens target P#0),QQ^1,0)))));
	vlist:=matrix {apply(vrlist,v->v#0)};
	rlist:=matrix {apply(vrlist,v->v#1)};
	llist:=matrix {apply(vrlist,v->v#2)};
	new Polyhedron from {
		"genlinealitySpace" => llist,
		"genpoints" => vlist,
		"genrays" => rlist}
	)



-- PURPOSE : Computing a polyhedron as the intersection of affine half-spaces and hyperplanes
intersection = method()

--   INPUT : '(M,v,N,w)',  where all four are matrices (although v and w are only vectors), such
--     	    	      	  that the polyhedron is given by P={x | Mx<=v and Nx=w} 
--  OUTPUT : 'P', the polyhedron
intersection(Matrix,Matrix,Matrix,Matrix) := (M,v,N,w) -> (
	-- checking for input errors
	if numColumns M =!= numColumns N then error("equations of half-spaces and hyperplanes must have the same dimension");
	if numRows M =!= numRows v or numColumns v =!= 1 then error("invalid condition vector for half-spaces");
	if numRows N =!= numRows w or numColumns w =!= 1 then error("invalid condition vector for hyperplanes");
	new Polyhedron from {
		"genhalfspaces"=>(chkZZQQ(M,"half-spaces"),chkZZQQ(v,"condition vector for half-spaces")),
		"genhyperplanes"=>(chkZZQQ(N,"hyperplanes"),chkZZQQ(w,"condition vector for hyperplanes"))
		}
	)

--   INPUT : '(M,N)',  two matrices where either 'P' is the Cone {x | Mx<=0, Nx=0} if 'M' and 'N' have the same source space 
--     	    	       or, if 'N' is only a Column vector the Polyhedron {x | Mx<=v} 
--  OUTPUT : 'P', the Cone or Polyhedron
intersection(Matrix,Matrix) := (M,N) -> (
	-- Checking for input errors
	if ((numColumns M =!= numColumns N and numColumns N =!= 1) or (numColumns N == 1 and numRows M =!= numRows N)) and N != 0*N then 
		error("invalid condition vector for half-spaces");
	M = chkZZQQ(M,"half-spaces");
	N = chkZZQQ(N,"condition vector for half-spaces");
	-- Decide whether 'M,N' gives the Cone C={p | M*p >= 0, N*p = 0}
	if numColumns M == numColumns N and numColumns N != 1 then return (
		intersection(M,map(source M,QQ^1,0),N,map(source M,QQ^1,0)))
	-- or the Cone C={p | M*p >= N=0}
	else if numRows N == 0 then return (
		intersection(M,map(source M,QQ^1,0),map(QQ^1,source M,0),map(source M,QQ^1,0)))
	-- or the Polyhedron P={p | M*p >= N != 0}
	else return intersection(M,N,map(QQ^1,source M,0),map(QQ^1,QQ^1,0)))
   







halfspaces = method()
halfspaces Polyhedron := P -> (
	if P#?"halfspaces" then return P#"halfspaces";
	computeHalfspaces P;
	P#"halfspaces")

hyperplanes = method()
hyperplanes Polyhedron := P -> (
	if P#?"hyperplanes" then return P#"hyperplanes";
	computeHalfspaces P;
	P#"hyperplanes")

vertices = method()
vertices Polyhedron := P -> (
	if P#?"vertices" then return P#"vertices";
	computeVertices P;
	P#"vertices")

rays = method()
rays Polyhedron := P -> (
	if P#?"rays" then return P#"rays";
	computeVertices P;
	P#"rays")

linSpace = method()
linSpace Polyhedron := P -> (
	if P#?"rays" then return P#"linealitySpace";
	computeVertices P;
	P#"linealitySpace")






ambDim = method(TypicalValue => ZZ)

--   INPUT : 'P'  a Polyhedron 
--  OUTPUT : an integer, the dimension of the ambient space
ambDim Polyhedron := X -> (
	if X#?"genrays" then return numgens target X#"genrays";
	numgens target (X#"genhyperplanes")_0
	)


--aux functions

computeHalfspaces = P -> (
	if not P#?"vertices" and not P#?"genpoints" then (
		computeVertices P);
	local Mvert; local Mrays; local Mlin;
	if P#?"vertices" then (Mvert=P#"vertices";Mrays=P#"rays";Mlin=P#"linealitySpace")
	else (Mvert=P#"genpoints";Mrays=P#"genrays";Mlin=P#"genlinealitySpace");
	if numRows Mvert == 0 then Mvert = matrix{{0}};
	if numColumns Mvert == 0 then Mvert = map(target Mvert,QQ^1,0);
	if numRows Mrays == 0 then Mrays = matrix{{0}};
	if numColumns Mrays == 0 then Mrays = map(target Mrays,QQ^1,0);
	if numRows Mlin == 0 then Mlin = matrix{{0}};
	if numColumns Mlin == 0 then Mlin = map(target Mlin,QQ^1,0);
	Mvert = map(QQ^1,source Mvert,(i,j)->1) || Mvert;
	Mrays = map(QQ^1,source Mrays,0) || Mrays;
	Mlin = map(QQ^1,source Mrays,0) || Mlin;
	M := Mvert | Mrays;
	fm:= fourierMotzkin(M,Mlin);
	HP := transpose(fm_1);
	P#"hyperplanes"= (HP_{1..(numgens source HP)-1},-HP_{0});
	HS := transpose(fm_0);
	P#"halfspaces"= (HS_{1..(numgens source HS)-1},-HS_{0});
	)

computeVertices = P-> (
	if not P#?"hyperplanes" and not P#?"genhyperplanes" then (
		computeHalfspaces P);
	local M; local N; 
	if P#?"hyperplanes" then (M=P#"halfspaces";N=P#"hyperplanes")
	else (M=P#"genhalfspaces";N=P#"genhalfspaces");
	M=(-M#1)|(M#0);
	N=(-N#1)|(N#0);
	M = transpose M | map(source M,QQ^1,(i,j) -> if i == 0 then -1 else 0);
	N = transpose N;
	verticesA := fourierMotzkin(M,N);
	VR := verticesA#0;
        C := map(target VR,QQ^0,0);
	B := promote(C,QQ);
	VRpart := partition(n -> VR_n_0 != 0,toList(0..(numColumns VR)-1));
	if VRpart#?true then (
	     B = promote(VR_(VRpart#true),QQ);
	     B = matrix transpose apply(numColumns B, j -> flatten entries((1/B_j_0)*B_{j})));
	if VRpart#?false then C = VR_(VRpart#false);
	LS := verticesA#1;
	LS = LS^{1..(numgens target LS)-1};
	P#"vertices"=B^{1..(numgens target B)-1};
	P#"rays"=C^{1..(numgens target C)-1};
	P#"linealitySpace"=LS;
	)



liftable (Matrix,Number) := (f,k) -> try (lift(f,k); true) else false; 

makePrimitiveMatrix = M -> if M != 0 then lift(transpose matrix apply(entries transpose M, w -> (g := abs gcd w; apply(w, e -> e//g))),ZZ) else lift(M,ZZ);

-- PURPOSE : check whether a matrix is over ZZ or QQ
--   INPUT : '(M,msg)', a matrix 'M' and a string 'msg'
--  OUTPUT : the matrix 'M' promoted to QQ if it was over ZZ or QQ, otherwise an error
chkZZQQ = (M,msg) -> (
     R := ring M;
     if R =!= ZZ and R =!= QQ then error("expected matrix of ",msg," to be over ZZ or QQ");
     promote(M,QQ));

-- PURPOSE : check whether a matrix is over ZZ or QQ, return it over ZZ
--   INPUT : '(M,msg)', a matrix 'M' and a string 'msg'
--  OUTPUT : the matrix 'M' cleared of denominatorx columnwise and lifted to ZZ if it was over QQ, 
--     	     itself if already over ZZ, otherwise an error
chkQQZZ = (M,msg) -> (
     R := ring M;
     if R === ZZ then M else if R === QQ then makePrimitiveMatrix M else error("expected matrix of ",msg," to be over ZZ or QQ"));







beginDocumentation()

