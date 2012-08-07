newPackage(
	"Polymake",
    	Version => "0.3", 
    	Date => "Aug 6, 2012",
    	Authors => {{Name => "Josephine Yu", 
		  Email => "josephine.yu@math.gatech.edu", 
		  HomePage => "http://people.math.gatech.edu/~jyu67"},
	            {Name => "Qingchun Ren", 
		  Email => "qingchun.ren@gmail.com", 
		  HomePage => "http://math.berkeley.edu/~qingchun/"}},
    	Headline => "a package for interfacing with polymake",
    	DebuggingMode => true
    	)

export {
     runPolymakeCommand,
     PolymakePolytope,
     createPolymakePolytope,
     getPropertyNames,
     getProperty
     }


---------------------------------------------------------------------------
-- Code
---------------------------------------------------------------------------

needsPackage "SimpleDoc"

runPolymakePrefix = "polymake"

runPolymakeCommand = method(TypicalValue => String)
runPolymakeCommand(String) := (command) -> (
     filename := temporaryFileName()|currentTime()|".poly";
     filename << command << endl << close;
     get("!"|runPolymakePrefix|" "|filename)
     )

---------------------------------------------------------------------------
-- A Wrapper for a polytope object
---------------------------------------------------------------------------

PolymakePolytope = new Type of MutableHashTable

new PolymakePolytope from HashTable := (this,properties) -> (
     new MutableHashTable from {
	 "parsedProperties" => new MutableHashTable from properties,
	 "availableProperties" => new MutableHashTable from apply(keys(properties),x->{x,1}),
	 "polymakeFile" => null
	 }
     )

new PolymakePolytope from String := (this,fileName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|fileName|"\");
	 my @properties = $object->list_properties;
	 my $numberOfProperties = scalar @properties;
	 for(my $i=0;$i<$numberOfProperties;$i++){print \"$properties[$i]\\n\";}";
     propertiesString := runPolymakeCommand(script);
     propertiesList := lines propertiesString;
     new MutableHashTable from {
	 "parsedProperties" => new MutableHashTable,
	 "availableProperties" => new MutableHashTable from apply(propertiesList,x->{x,1}),
	 "polymakeFile" => fileName
	 }
     )

createPolymakePolytope = method(TypicalValue=>PolymakePolytope)
createPolymakePolytope(String,String) := (command,variableName) -> (
     fileName := temporaryFileName()|currentTime()|".poly";
     << "using temporary file " << fileName << endl;
     script := "use application \"polytope\";"|command|"save($"|variableName|",\""|fileName|"\");";
     runPolymakeCommand(script);
     new PolymakePolytope from fileName
     )
     
-- The old version of Polyhedron is no longer available
--
--new PolymakePolytope from Polyhedron := (this,P) -> (
--     properties := new MutableHashTable from {};
--     if P===null then null
--     else(
--	  properties#"DIM" = P#"dimension of polyhedron";
--	  if(P#"dimension of lineality space" == 0) then (
--	      properties#"VERTICES" = transpose(P#"homogenizedVertices"#0);
--	      properties#"N_VERTICES" = P#"number of rays" + P#"number of vertices";
--	      );
--	  properties#"INEQUALITIES" = transpose(-P#"homogenizedHalfspaces"#0);
--	  properties#"EQUATIONS" = transpose(-P#"homogenizedHalfspaces"#1);
--	  new PolymakePolytope from properties
--	  )
--     )

getPropertyNames = method(TypicalValue => List)
getPropertyNames(PolymakePolytope) := (P) -> (
     keys P#"availableProperties"
     )

---------------------------------------------------------------------------
-- Create a polymake input file

toPolymakeFormat = method(TypicalValue => String)
toPolymakeFormat(String, Matrix) := (propertyName, M) -> (
     if M === null then ""
     else(
     	  S := propertyName|"\n";
     	  if numRows M > 0 then
	     S = S|replace("\\|", "", toString net M);
     	  S
     	  )
     )
toPolymakeFormat(String,Vector) := (propertyName,V) -> (
     if V === null then ""
     else(
     	  S := propertyName|"\n";
     	  if length V > 0 then
              S = S|replace("\\|", "", toString net matrix{V});     
     	  S
     	  )
     )
toPolymakeFormat(String,ZZ) := (propertyName,x) -> (
     if x === null then ""
     else(
     	  S := propertyName|"\n"|x|"\n";
     	  S
     	  )
     )
toPolymakeFormat(PolymakePolytope) := (P) -> (
     concatenate apply(pairs(P#"parsedProperties"), a -> toPolymakeFormat(a)|"\n\n")
     )

writePolymakeFile = method(TypicalValue => String)
writePolymakeFile(PolymakePolytope,String) := (P, fileName) ->(
     fileName << toPolymakeFormat(P) << endl << close;
     P#"polymakeFile" = fileName;
     fileName	  
     )
writePolymakeFile(PolymakePolytope) := (P) ->(
     fileName := temporaryFileName()|currentTime()|".poly";
     << "using temporary file " << fileName << endl;
     writePolymakeFile(P,fileName);
     fileName	  
     )

---------------------------------------------------------------------------
----- Run Polymake

runPolymake = method(TypicalValue => String)
runPolymake(PolymakePolytope,String) := (P,propertyName) -> (
     if(P#"polymakeFile"===null) then (
	  writePolymakeFile(P);
	  );
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 $object->"|propertyName|";
	 save($object,\""|(P#"polymakeFile")|"\");
	 my @properties = $object->list_properties;
	 my $numberOfProperties = scalar @properties;
	 for(my $i=0;$i<$numberOfProperties;$i++){print \"$properties[$i]\\n\";}";
     propertiesString := runPolymakeCommand(script);
     propertiesList := lines propertiesString;
     for property in propertiesList do (
	  P#"availableProperties"#property = 1;
	  );
     )

---------------------------------------------------------------------------
----- Utilities

makeList = (str) -> (
     t := separateRegexp(" +",str);
     t = apply(t,value);
     select(t, x-> x =!= null)
     )

makeMatrix = (str) -> (
     L := lines str;
     L = select (L, x -> x!="");
     if #L == 0 then map(QQ^0,QQ^0,0)
     else matrix(L/makeList)
     )

------------------------------------------------------------------------------
--Types of properties in polymake (hard coded)
------------------------------------------------------------------------------

propertyTypes = new HashTable from {
     "AFFINE_HULL" => "Matrix",
     "ALTSHULER_DET" => "Integer",
     "BALANCE" => "Integer",
     "BALANCED" => "Boolean",
     "BOUNDED" => "Boolean",
     "BOUNDED_COMPLEX" => "PolyhedralComplex",
     "CD_INDEX_COEFFICIENTS" => "Vector",
     "CENTERED" => "Boolean",
     "CENTROID" => "Vector",
     "CHIROTOPE" => "Text",
     "COCUBICAL" => "Boolean",
     "COCUBICALITY" => "Integer",
     "COMBINATORIAL_DIM" => "Integer",
     "COMPLEXITY" => "Float",
     "CONE_AMBIENT_DIM" => "Integer",
     "CONE_DIM" => "Integer",
     "COORDINATE_LABELS" => "ArrayOfString",
     "CUBICAL" => "Boolean",
     "CUBICALITY" => "Integer",
     "CUBICAL_H_VECTOR" => "Vector",
     "DUAL_BOUNDED_H_VECTOR" => "Vector",
     "DUAL_GRAPH" => "Graph",
     "DUAL_H_VECTOR" => "Vector",
     "EQUATIONS" => "Matrix",
     "ESSENTIALLY_GENERIC" => "Boolean",
     "F2_VECTOR" => "Matrix",
     "FACETS" => "Matrix",
     "FACETS_THRU_INPUT_RAYS" => "IncidenceMatrix",
     "FACETS_THRU_POINTS" => "IncidenceMatrix",
     "FACETS_THRU_RAYS" => "IncidenceMatrix",
     "FACETS_THRU_VERTICES" => "IncidenceMatrix",
     "FACET_LABELS" => "ArrayOfString",
     "FACET_SIZES" => "Array",
     "FACE_SIMPLICITY" => "Integer",
     "FAR_FACE" => "Set",
     "FAR_HYPERPLANE" => "Vector",
     "FATNESS" => "Float",
     "FEASIBLE" => "Boolean",
     "FLAG_VECTOR" => "Vector",
     "FTR_CYCLIC_NORMAL" => "ArrayOfList",
     "FTV_CYCLIC_NORMAL" => "ArrayOfList",
     "FULL_DIM" => "Boolean",
     "F_VECTOR" => "Vector",
     "GALE_TRANSFORM" => "Matrix",
     "GALE_VERTICES" => "Matrix",
     "GRAPH" => "Graph",
     "GROUP" => "GroupOfCone",
     "G_VECTOR" => "Vector",
     "HASSE_DIAGRAM" => "FaceLattice",
     "H_VECTOR" => "Vector",
     "INEQUALITIES" => "Matrix",
     "INEQUALITIES_THRU_RAYS" => "IncidenceMatrix",
     "INEQUALITIES_THRU_VERTICES" => "IncidenceMatrix",
     "INPUT_LINEALITY" => "Matrix",
     "INPUT_RAYS" => "Matrix",
     "INPUT_RAYS_IN_FACETS" => "IncidenceMatrix",
     "LINEALITY_DIM" => "Integer",
     "LINEALITY_SPACE" => "Matrix",
     "LINEAR_SPAN" => "Matrix",
     "LP" => "LinearProgram",
     "MINIMAL_VERTEX_ANGLE" => "Float",
     "NEIGHBORLINESS" => "Integer",
     "NEIGHBORLY" => "Boolean",
     "NEIGHBOR_FACETS_CYCLIC_NORMAL" => "ArrayOfList",
     "NEIGHBOR_VERTICES_CYCLIC_NORMAL" => "ArrayOfList",
     "N_BOUNDED_VERTICES" => "Integer",
     "N_EQUATIONS" => "Integer",
     "N_FACETS" => "Integer",
     "N_INEQUALITIES" => "Integer",
     "N_INPUT_LINEALITY" => "Integer",
     "N_INPUT_RAYS" => "Integer",
     "N_POINTS" => "Integer",
     "N_RAYS" => "Integer",
     "N_RAY_FACET_INC" => "Integer",
     "N_VERTEX_FACET_INC" => "Integer",
     "N_VERTICES" => "Integer",
     "ONE_RAY" => "Vector",
     "ONE_VERTEX" => "Vector",
     "POINTED" => "Boolean",
     "POINTS" => "Matrix",
     "POINTS_IN_FACETS" => "IncidenceMatrix",
     "POLYTOPAL_SUBDIVISION" => "PolyhedralComplex",
     "POSITIVE" => "Boolean",
     "RAYS" => "Matrix",
     "RAYS_IN_FACETS" => "IncidenceMatrix",
     "RAYS_IN_INEQUALITIES" => "IncidenceMatrix",
     "RAY_LABELS" => "ArrayOfString",
     "RAY_SEPARATORS" => "Matrix",
     "RAY_SIZES" => "Array",
     "REL_INT_POINT" => "Vector",
     "RIF_CYCLIC_NORMAL" => "ArrayOfArray",
     "SCHLEGEL_DIAGRAM" => "SchlegelDiagram",
     "SELF_DUAL" => "Boolean",
     "SIMPLE" => "Boolean",
     "SIMPLE_POLYHEDRON" => "Boolean",
     "SIMPLICIAL" => "Boolean",
     "SIMPLICIALITY" => "Integer",
     "SIMPLICIAL_CONE" => "Boolean",
     "SIMPLICITY" => "Integer",
     "SPECIAL_FACETS" => "Set",
     "SPLITS" => "Matrix",
     "SPLIT_COMPATIBILITY_GRAPH" => "Graph",
     "STEINER_POINT" => "Vector",
     "STEINER_POINTS" => "Matrix",
     "SUBRIDGE_SIZES" => "Map",
     "TOWARDS_FAR_FACE" => "Vector",
     "TRIANGULATION" => "SimplicialComplex",
     "TRIANGULATION_INT" => "ArrayOfSet",
     "TWO_FACE_SIZES" => "Map",
     "UNBOUNDED_FACETS" => "Set",
     "VALID_POINT" => "Vector",
     "VERTEX_BARYCENTER" => "Vector",
     "VERTEX_LABELS" => "ArrayOfString",
     "VERTEX_NORMALS" => "Matrix",
     "VERTEX_SIZES" => "Array",
     "VERTICES" => "Matrix",
     "VERTICES_IN_FACETS" => "IncidenceMatrix",
     "VERTICES_IN_INEQUALITIES" => "IncidenceMatrix",
     "VIF_CYCLIC_NORMAL" => "ArrayOfArray",
     "VOLUME" => "Scalar",
     "ZONOTOPE_INPUT_VECTORS" => "Matrix",
     }

------------------------------------------------------------------------------
--Parse properties into M2 format
------------------------------------------------------------------------------

parseUnknownProperty = method(TypicalValue => String)
parseUnknownProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 print $object->"|propertyName|";";
     propertyValue := runPolymakeCommand(script);
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseBooleanProperty = method(TypicalValue => Boolean)
parseBooleanProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 my $v = $object->"|propertyName|";
	 if($v){print(\"true\")}else{print(\"false\");}";
     propertyValue := (runPolymakeCommand(script)=="true");
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseScalarProperty = method()
parseScalarProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 print $object->"|propertyName|";";
     propertyValue := value(runPolymakeCommand(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseListProperty = method(TypicalValue => List)
parseListProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 print $object->"|propertyName|";";
     propertyValue := makeList(runPolymakeCommand(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseMatrixProperty = method(TypicalValue => Matrix)
parseMatrixProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"polymakeFile")|"\");
	 print $object->"|propertyName|";";
     propertyValue := makeMatrix(runPolymakeCommand(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseProperty = method()
parseProperty(PolymakePolytope,String) := (P, propertyName) -> (
     if(not(propertyTypes#?propertyName)) then (
	  parseUnknownProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="Boolean") then (
	  parseBooleanProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="Integer" or propertyTypes#propertyName=="Float" or propertyTypes#propertyName=="Scalar") then (
	  parseScalarProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="Vector" or propertyTypes#propertyName=="Array") then (
	  parseListProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="Matrix") then (
	  parseMatrixProperty(P,propertyName)
	  )
     else (
	  parseUnknownProperty(P,propertyName)
	  );
     )

getProperty = method()
getProperty(PolymakePolytope,String) := (P, propertyName) -> (
     if(not(P#"availableProperties"#?propertyName)) then (
	  runPolymake(P,propertyName);
	  );
     if(not(P#"parsedProperties"#?propertyName)) then (
	  parseProperty(P,propertyName);
	  );
     P#"parsedProperties"#propertyName
     )

---------------------------------------------------------------------------
-----------------------DOCUMENTATION----------------------
---------------------------------------------------------------------------

beginDocumentation()

doc ///
  Key
    Polymake
  Headline
    Interface for Polymake
  Description
   Text 
     {\tt Polymake} is a software for convex polyhedra, simplicial complexes, and other discrete geometric objects, written by Ewgenij Gawrilow and Michael Joswig.  It is available at @HREF "http://www.math.tu-berlin.de/polymake/"@. The user should have {\tt Polymake} installed on their machine.
   Text 
     Warning: this package is not complete, and is mostly undocumented, but it is used in  @TO "gfanInterface::gfanInterface"@. 
   Text
     We can use the interface to get properties of @TO "Polyhedra::Polyhedron"@
   Example
     P = cyclicPolytope(3,5)
     getVectorProperty(P, "F_VECTOR")
     getMatrixProperty(P, "VERTEX_NORMALS")
   Text
     Instead of creating a new temporary file every time, we can reuse one and also save computation time.
   Example
     polyFile = writePolymakeFile(P)
     runPolymake(polyFile, "F_VECTOR")
     runPolymake(polyFile, "VERTEX_NORMALS")
   Text
     Look in the polymake file for the properties already computed.
   Example
     getPropertyNames(polyFile)
     runPolymake(polyFile, "VERTICES_IN_FACETS")
   Text
     We can save the {\tt Polymake} output as a vector, a matrix or a list of things.
   Example
     getVectorProperty(polyFile, "VERTEX_DEGREES")
     getMatrixProperty(polyFile, "VERTEX_NORMALS")
     getListProperty(polyFile, "VERTICES_IN_FACETS")
     getProperty(polyFile, "SIMPLICIAL")
     removeFile(polyFile)
  Caveat
     You may need to manually remove the temporary files created in {\tt /tmp}.
  SeeAlso
     Polyhedra
///


{*
doc ///
  Key
    PolymakeObject
  Headline
    Polymake object
  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///
*}

{*
doc ///
  Key
    polymakeObject
    (polymakeObject,String)
    (polymakeObject,String,List)
  Headline
    Makes PolymakeObject either from the name of a polymake file, or the file name and a list of properties.
  Usage
  
  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///



doc ///
  Key
    getPropertyNames
    (getPropertyNames, String)
    (getPropertyNames, List)
  Headline
     Get the list of known properties in a polymake file or a list containing lines of a polymake (xml) format file.
  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///


doc ///
  Key
    getListProperty
    (getListProperty, List,String) 
    (getListProperty, Polyhedron,String)
    (getListProperty, String,String)
  Headline
    get proprety of a polyhedron as a list
  Usage
    getListProperty(dataLines, property)
    getListProperty(P, property)
    getListProperty(polyFileName, property)
  Inputs
    dataLines: List
      list of strings, typically output of polymake
    property: String
      name of polymake property
    polyFileName: String
      file name of {\tt Polymake} file
    P: Polyhedron
  Outputs
    L:List
      whose entries are values of the strings in dataLines or output of , with {\tt Polymake} comments removed.
  Consequences

  Description
   Text
   Text
   Example
     P = cyclicPolytope(3,5)
     getListProperty(P, "VERTICES_IN_FACETS")
   Text
   Example
  Caveat
    A temporary file may get created.
  SeeAlso
///


doc ///
  Key
    getMatrixProperty
    (getMatrixProperty,String,String) 
    (getMatrixProperty,Polyhedron,String)
    (getMatrixProperty,List,String)
  Headline
    Get a property as a matrix, given a @TO Polyhedra::Polyhedron@, a polymake file name, or a list of lines in a polymake output.
  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    getProperty
    (getProperty,List,String)
    (getProperty,Polyhedron,String)
    (getProperty,String,String)
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///


doc ///
  Key
    getVectorProperty
    (getVectorProperty,List,String)
    (getVectorProperty,Polyhedron,String) 
    (getVectorProperty,String,String)
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    makemat
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    makevec
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    runPolymake
    (runPolymake,Polyhedron,String) 
    (runPolymake,PolymakeObject,String) 
    (runPolymake,String,String)
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    toPolymakeFormat
    (toPolymakeFormat,Polyhedron) 
    (toPolymakeFormat,PolymakeObject)
    (toPolymakeFormat,String,Matrix)
    (toPolymakeFormat,String,Vector)
    (toPolymakeFormat,String,ZZ) 
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

doc ///
  Key
    writePolymakeFile
    (writePolymakeFile,Polyhedron)
    (writePolymakeFile,Polyhedron,String) 
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

*}

---------------------------------------------------------------------------
------------------------- TEST ---------------------------
---------------------------------------------------------------------------


TEST ///

///

end

---------------------------------------------------------------------------
------------------------- END ---------------------------
---------------------------------------------------------------------------
restart
needsPackage "Polymake"
testScript = ///
    use application "polytope";
    my $a = cube(2,2);
    print $a->F_VECTOR;
    ///
runPolymakeCommand(testScript)
P = createPolymakePolytope("my $a=cube(2,2);","a")
getProperty(P,"DIM")
class oo
getProperty(P,"CONE_DIM")
class oo
getProperty(P,"F_VECTOR")
class oo
getProperty(P,"FACETS")
class oo
getProperty(P,"FACET_SIZES")
class oo
getProperty(P,"MINIMAL_VERTEX_ANGLE")
class oo
getProperty(P,"FACETS_THRU_VERTICES")
class oo
getPropertyNames(P)

---------------------------------------------------------------------------
------------------------- TO DO ---------------------------
---------------------------------------------------------------------------
-- Parse IncidenceMatrix objects and other types
-- Parse all properties in one round to save the overhead
-- Solve the prefix problem
-- Documentation
-- Find why "DIM" does not appear in polymake documentation