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
-- Parts Copyright 2010 Rene Birkner
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


export {"vertices",
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

-- WISHLIST
--  -Symmetry group for polytopes


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
convexHull(Polyhedron,Polyhedron) := (P1,P2) -> (
	-- Checking for input errors
	if ambDim P1 =!= ambDim P2 then error("Polyhedra must lie in the same ambient space");
	if member("genhyperplanes",keys P1) and member("genhyperplanes",keys P1) then return (
		new Polyhedron from {
			"genhyperplanes" => (P1#"genhyperplanes"|P2#"genhyperplanes"),
			"genhalfspaces" => (P1#"genhalfspaces"|P2#"genhalfspaces")
			});
	if member("genpoints",keys P1) and member("genpoints",keys P1) then return (
		new Polyhedron from {
			"genpoints" => (P1#"genpoints"|P2#"genpoints"),
			"genrays" => (P1#"genrays"|P2#"genrays")
			});
	--descriptions don't agree, so we will compute point/ray description
	)

halfspaces = method()
halfspaces Polyhedron := P -> (
	if member("halfspaces",keys P) then return P#"halfspaces";
	computeHalfspaces P;
	P#"halfspaces")

hyperplanes = method()
hyperplanes Polyhedron := P -> (
	if member("hyperplanes",keys P) then return P#"hyperplanes";
	computeHalfspaces P;
	P#"hyperplanes")

vertices = method()
vertices Polyhedron := P -> (
	if member("vertices",keys P) then return P#"vertices";
	computeVertices P;
	P#"vertices")

rays = method()
rays Polyhedron := P -> (
	if member("rays",keys P) then return P#"rays";
	computeVertices P;
	P#"rays")







ambDim = method(TypicalValue => ZZ)

--   INPUT : 'P'  a Polyhedron 
--  OUTPUT : an integer, the dimension of the ambient space
ambDim Polyhedron := X -> (
	if member("ambient dimension",keys X) then return X#"ambient dimension";
	if member("genrays",keys X) then X#"ambient dimension"=numgens target X#"genrays"
	else if member("genhyperplanes",keys X) then X#"ambient dimension"=numgens target (X#"genhyperplanes")_0;
	return X#"ambient dimension")


--aux functions

computeHalfspaces = P -> (
	if not member ("vertices",keys P) and not member("genpoints",keys P) then (
		computeVertices P);
	local Mvert; local Mrays; 
	if member("vertices",keys P) then (Mvert=P#"vertices";Mrays=P#"rays")
	else (Mvert=P#"genpoints";Mrays=P#"genrays");
	if numRows Mvert == 0 then Mvert = matrix{{0}};
	if numColumns Mvert == 0 then Mvert = map(target Mvert,QQ^1,0);
	if numRows Mrays == 0 then Mrays = matrix{{0}};
	if numColumns Mrays == 0 then Mrays = map(target Mrays,QQ^1,0);
	Mvert = map(QQ^1,source Mvert,(i,j)->1) || Mvert;
	Mrays = map(QQ^1,source Mrays,0) || Mrays;
	M := Mvert | Mrays;
	fm:= fourierMotzkin M;
	HP := transpose(fm_1);
	P#"hyperplanes"= (HP_{1..(numgens source HP)-1},-HP_{0});
	HS := transpose(fm_0);
	P#"halfspaces"= (HS_{1..(numgens source HS)-1},-HS_{0});
	)

computeVertices = P-> (
	if not member ("hyperplanes",keys P) and not member("genhyperplanes",keys P) then (
		computeHalfspaces P);
	local M; local N; 
	if member("hyperplanes",keys P) then (M=P#"halfspaces";N=P#"hyperplanes")
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
	P#"vertices"=B^{1..(numgens target B)-1},
	P#"rays"=C^{1..(numgens target C)-1}
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

