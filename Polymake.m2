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

export {PolymakePolytope,getProperty,getPropertyNames}


---------------------------------------------------------------------------
-- Code
---------------------------------------------------------------------------

needsPackage "Polyhedra"
needsPackage "SimpleDoc"

PolymakePolytope = new Type of MutableHashTable

new PolymakePolytope from HashTable := (this,properties) -> (
     new MutableHashTable from {
	  "parsedProperties" => new MutableHashTable from properties,
	  "availableProperties" => new MutableHashTable from apply(keys(properties),x->{x,1}),
	  "polymakeFile" => null
	  }
     )

new PolymakePolytope from Polyhedron := (this,P) -> (
     properties := new MutableHashTable from {};
     if P===null then null
     else(
	  properties#"DIM" = P#"dimension of polyhedron";
	  if(P#"dimension of lineality space" == 0) then (
	      properties#"VERTICES" = transpose(P#"homogenizedVertices"#0);
	      properties#"N_VERTICES" = P#"number of rays" + P#"number of vertices";
	      );
	  properties#"INEQUALITIES" = transpose(-P#"homogenizedHalfspaces"#0);
	  properties#"EQUATIONS" = transpose(-P#"homogenizedHalfspaces"#1);
	  new PolymakePolytope from properties
	  )
     )

getPropertyNames = method(TypicalValue => List)
getPropertyNames(PolymakePolytope) := (P) -> (
     keys P#"availableProperties"
     )

---------------------------------------------------------------------------
-- Create a polymake input file

toPolymakeFormat = method(TypicalValue => String)
toPolymakeFormat(String, Matrix) := (propertyname, M) -> (
     if M === null then ""
     else(
     	  S := propertyname|"\n";
     	  if numRows M > 0 then
	     S = S|replace("\\|", "", toString net M);
     	  S
     	  )
     )
toPolymakeFormat(String,Vector) := (propertyname,V) -> (
     if V === null then ""
     else(
     	  S := propertyname|"\n";
     	  if length V > 0 then
              S = S|replace("\\|", "", toString net matrix{V});     
     	  S
     	  )
     )
toPolymakeFormat(String,ZZ) := (propertyname,x) -> (
     if x === null then ""
     else(
     	  S := propertyname|"\n"|x|"\n";
     	  S
     	  )
     )
toPolymakeFormat(PolymakePolytope) := (P) -> (
     concatenate apply(pairs(P#"parsedProperties"), a -> toPolymakeFormat(a)|"\n\n")
     )

writePolymakeFile = method(TypicalValue => String)
writePolymakeFile(PolymakePolytope,String) := (P, filename) ->(
     filename << toPolymakeFormat(P) << endl << close;
     P#"polymakeFile" = filename;
     filename	  
     )
writePolymakeFile(PolymakePolytope) := (P) ->(
     filename := temporaryFileName()|currentTime()|".poly";
     << "using temporary file " << filename << endl;
     writePolymakeFile(P,filename);
     filename	  
     )

---------------------------------------------------------------------------
----- Run Polymake

runPolymake = method(TypicalValue => String)

runPolymakePrefix = "export ResourcesDir=/Applications/polymake.app/Contents/Resources;export POLYMAKE_USER_DIR=\"${HOME}/.polymake-macbundle\";export POLYMAKE_BASE_PATH=$ResourcesDir/polymake;export LD_LIBRARY_PATH=$ResourcesDir/lib:$ResourcesDir/include/boost_1_47_0/:$LD_LIBRARY_PATH;export CPLUS_INCLUDE_PATH=$ResourcesDir/include/;export CFLAGS=-I$ResourcesDir/include/;export CPPFLAGS=-I$ResourcesDir/include/;export PERL5LIB=$ResourcesDir/lib/perl5/site_perl/$perlversion/darwin-thread-multi-2level/:$ResourcesDir/polymake/lib/polymake/lib/:$ResourcesDir/lib/perl5/:$ResourcesDir/polymake/lib/polymake/perlx/:$ResourcesDir/polymake/share/polymake/perllib/:$PERL5LIB;/Applications/polymake.app/Contents/Resources/polymake/bin/polymake"

runPolymake(PolymakePolytope,String) := (P,propertyName) -> (
     if(P#"polymakeFile"===null) then (
	  writePolymakeFile(P);
	  );
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");\\$object->"|propertyName|";save(\\$object,\\\""|(P#"polymakeFile")|"\\\");my @properties = \\$object->list_properties;my \\$numberOfProperties = scalar @properties;for(my \\$i=0;\\$i<\\$numberOfProperties;\\$i++){print \\\"\\$properties[\\$i]\\\\n\\\";}";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertiesString := get(script);
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
     "CENTROID" => "LIST",
     "SPLITS" => "MATRIX",
     "SPLIT_COMPATIBILITY_GRAPH" => "GRAPH",
     "STEINER_POINT" => "LIST",
     "AFFINE_HULL" => "MATRIX",
     "BOUNDED" => "BOOLEAN",
     "CENTERED" => "BOOLEAN",
     "FEASIBLE" => "BOOLEAN",
     "GALE_TRANSFORM" => "MATRIX",
     "MINIMAL_VERTEX_ANGLE" => "SCALAR",
     "N_POINTS" => "SCALAR",
     "ONE_VERTEX" => "LIST",
     "POINTS" => "MATRIX",
     "STEINER_POINTS" => "MATRIX",
     "VALID_POINT" => "LIST",
     "VERTEX_BARYCENTER" => "LIST",
     "VERTEX_LABELS" => "LIST_OF_STRING",
     "VERTEX_NORMALS" => "MATRIX",
     "VERTICES" => "MATRIX",
     "ZONOTOPE_INPUT_VECTORS" => "MATRIX",
     "ALTSHULER_DET" => "SCALAR",
     "BALANCE" => "SCALAR",
     "BALANCED" => "BOOLEAN",
     "CD_INDEX_COEFFICIENTS" => "LIST",
     "COCUBICAL" => "BOOLEAN",
     "COCUBICALITY" => "SCALAR",
     "COMPLEXITY" => "SCALAR",
     "CUBICAL" => "BOOLEAN",
     "CUBICALITY" => "SCALAR",
     "CUBICAL_H_VECTOR" => "LIST",
     "DUAL_BOUNDED_H_VECTOR" => "LIST",
     "DUAL_H_VECTOR" => "LIST",
     "F2_VECTOR" => "MATRIX",
     "FACETS_THRU_POINTS" => "INCIDENCE_MATRIX",
     "FACETS_THRU_VERTICES" => "INCIDENCE_MATRIX",
     "FACE_SIMPLICITY" => "SCALAR",
     "FATNESS" => "SCALAR",
     "F_VECTOR" => "LIST",
     "GRAPH" => "GRAPH",
     "G_VECTOR" => "LIST",
     "H_VECTOR" => "LIST",
     "NEIGHBORLINESS" => "SCALAR",
     "NEIGHBORLY" => "BOOLEAN",
     "N_VERTEX_FACET_INC" => "SCALAR",
     "N_VERTICES" => "SCALAR",
     "SIMPLICIALITY" => "SCALAR",
     "SIMPLICITY" => "SCALAR",
     "SUBRIDGE_SIZES" => "MAP",
     "TWO_FACE_SIZES" => "MAP",
     "VERTEX_SIZES" => "LIST",
     "VERTICES_IN_FACETS" => "INCIDENCE_MATRIX",
     "INEQUALITIES_THRU_VERTICES" => "INCIDENCE_MATRIX",
     "POINTS_IN_FACETS" => "INCIDENCE_MATRIX",
     "VERTICES_IN_INEQUALITIES" => "INCIDENCE_MATRIX",
     "LP" => "LINEAR_PROGRAM",
     "CHIROTOPE" => "TEXT",
     "FAR_HYPERPLANE" => "LIST",
     "SPECIAL_FACETS" => "SET",
     "POLYTOPAL_SUBDIVISION" => "POLYHEDRAL_COMPLEX",
     "VOLUME" => "SCALAR",
     "BOUNDED_COMPLEX" => "POLYHEDRAL_COMPLEX",
     "FAR_FACE" => "SET",
     "N_BOUNDED_VERTICES" => "SCALAR",
     "SIMPLE_POLYHEDRON" => "BOOLEAN",
     "TOWARDS_FAR_FACE" => "LIST",
     "UNBOUNDED_FACETS" => "SET",
     "FTV_CYCLIC_NORMAL" => "ARRAY_OF_LIST",
     "GALE_VERTICES" => "MATRIX",
     "NEIGHBOR_VERTICES_CYCLIC_NORMAL" => "ARRAY_OF_LIST",
     "SCHLEGEL_DIAGRAM" => "SCHLEGEL_DIAGRAM",
     "VIF_CYCLIC_NORMAL" => "ARRAY_OF_ARRAY",
     }

------------------------------------------------------------------------------
--Parse properties into M2 format
------------------------------------------------------------------------------

parseUnknownProperty = method(TypicalValue => String)
parseUnknownProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");print \\$object->"|propertyName|";";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertyValue := get(script);
     print propertyValue;
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseBooleanProperty = method(TypicalValue => Boolean)
parseBooleanProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");my \\$v = \\$object->"|propertyName|";if(\\$v){print(\\\"true\\\")}else{print(\\\"false\\\");}";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertyValue := (get(script)=="true");
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseScalarProperty = method()
parseScalarProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");print \\$object->"|propertyName|";";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertyValue := value(get(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseListProperty = method(TypicalValue => List)
parseListProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");print \\$object->"|propertyName|";";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertyValue := makeList(get(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseMatrixProperty = method(TypicalValue => Matrix)
parseMatrixProperty(PolymakePolytope,String) := (P, propertyName) -> (
     script := "use application \\\"polytope\\\";my \\$object = load(\\\""|(P#"polymakeFile")|"\\\");print \\$object->"|propertyName|";";
     script = "!"|runPolymakePrefix|" \""|script|"\"";
     propertyValue := makeMatrix(get(script));
     P#"parsedProperties"#propertyName = propertyValue;
     propertyValue
     )

parseProperty = method()
parseProperty(PolymakePolytope,String) := (P, propertyName) -> (
     if(not(propertyTypes#?propertyName)) then (
	  parseUnknownProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="BOOLEAN") then (
	  parseBooleanProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="SCALAR") then (
	  parseScalarProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="LIST") then (
	  parseListProperty(P,propertyName)
	  )
     else if(propertyTypes#propertyName=="MATRIX") then (
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
needsPackage "Polyhedra"
needsPackage "Polymake"
P = new PolymakePolytope from cyclicPolytope(2,3)
getProperty(P,"DIM")
getProperty(P,"CONE_DIM")
getProperty(P,"F_VECTOR")
getProperty(P,"FACETS")
getPropertyNames(P)
