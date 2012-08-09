newPackage(
	"PolymakeInterface",
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
     runPolymake,
     ParseAllProperties,
     createPolymakePolytope,
     hasProperty,
     getProperty,
     getPropertyNames,
     parseAllAvailableProperties
     }


---------------------------------------------------------------------------
-- Code
---------------------------------------------------------------------------

needsPackage "SimpleDoc"
needsPackage "PolyhedralObjects"

runPolymakePrefix = "polymake"

runPolymake = method(Options => {ParseAllProperties => false})
runPolymake(String) := o -> (script) -> (
     filename := temporaryFileName()|currentTime()|".poly";
     filename << script << endl << close;
     get("!"|runPolymakePrefix|" "|filename)
     )

createPolymakePolytope = method()
createPolymakePolytope(String,String) := (script,variableName) -> (
     fileName := temporaryFileName()|currentTime()|".poly";
     << "using temporary file " << fileName << endl;
     script = "use application \"polytope\";"|script|"
         my $object = $"|variableName|";
	 save($object,\""|fileName|"\");
	 my @properties = $object->list_properties;
	 my $numberOfProperties = scalar @properties;
	 for(my $i=0;$i<$numberOfProperties;$i++){print \"$properties[$i]\\n\";}";
     propertiesString := runPolymake(script);
     propertiesList := lines propertiesString;
     new PolyhedralObject from {
	  "PolymakeFile" => fileName,
	  "AvailableProperties" => new Set from propertiesList
	  }
     )

------------------------------------------------------------------------------
--Types of properties in polymake (hard coded)
------------------------------------------------------------------------------

propertyTypes = {
     {    
	  "M2PropertyName" => "ConeDim",
	  "PolymakePropertyName" => "CONE_DIM",
	  "ValueType" => "Integer"
	  },
     {   
	  "M2PropertyName" => "InputLineality",
	  "PolymakePropertyName" => "INPUT_LINEALITY",
	  "ValueType" => "Matrix"
	  },
     {    
	  "M2PropertyName" => "FVector",
	  "PolymakePropertyName" => "F_VECTOR",
	  "ValueType" => "Vector"
	  },
     {   
	  "M2PropertyName" => "Points",
	  "PolymakePropertyName" => "POINTS",
	  "ValueType" => "Matrix"
	  },
     {    
	  "M2PropertyName" => "InputRays",
	  "PolymakePropertyName" => "INPUT_RAYS",
	  "ValueType" => "Matrix"
	  },
     {    
	  "M2PropertyName" => "Vertices",
	  "PolymakePropertyName" => "VERTICES",
	  "ValueType" => "Matrix"
	  },
     {   
	  "M2PropertyName" => "Facets",
	  "PolymakePropertyName" => "FACETS",
	  "ValueType" => "Matrix"
	  },
     {    
	  "M2PropertyName" => "Feasible",
	  "PolymakePropertyName" => "FEASIBLE",
	  "ValueType" => "Boolean"
	  },
     {    
	  "M2PropertyName" => "Bounded",
	  "PolymakePropertyName" => "BOUNDED",
	  "ValueType" => "Boolean"
	  }
     };

propertyTypes = apply(propertyTypes, x -> new HashTable from x);
polymakePropertyNameToValueType = new HashTable from apply(propertyTypes, x -> (x#"PolymakePropertyName",x#"ValueType"));
M2PropertyNameToPolymakePropertyName = new HashTable from apply(propertyTypes, x -> (x#"M2PropertyName",x#"PolymakePropertyName"));
polymakePropertyNameToM2PropertyName = new HashTable from apply(propertyTypes, x -> (x#"PolymakePropertyName",x#"M2PropertyName"));

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
toPolymakeFormat(PolyhedralObject) := (P) -> (
     parsedPropertyNames := for propertyName in keys(P) when (propertyName!="AvailableProperties") and (propertyName!="PolymakeFile") and (M2PropertyNameToPolymakePropertyName#?propertyName) list propertyName;
     parsedProperties := apply(parsedPropertyNames,x->(M2PropertyNameToPolymakePropertyName#x,P#x));
     concatenate apply(parsedProperties, a -> toPolymakeFormat(a)|"\n\n")
     )

writePolymakeFile = method(TypicalValue => Nothing)
writePolymakeFile(PolyhedralObject, String) := (P, header) ->(
     fileName := temporaryFileName()|currentTime()|".poly";
     << "using temporary file " << fileName << endl;
     fileName << header << endl << endl << toPolymakeFormat(P) << endl << close;
     P#"PolymakeFile" = fileName;
     fileName	  
     )
writePolymakeFile(PolyhedralObject) := (P) -> (
     writePolymakeFile(P, "")
     )
writePolymakeFile(Cone) := (C) -> (
     header := "_type Cone\n";
     writePolymakeFile(C, header)
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
--Parse properties into M2 format
------------------------------------------------------------------------------

parseUnknownProperty = method(TypicalValue => String)
parseUnknownProperty(PolyhedralObject,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"PolymakeFile")|"\");
	 print $object->"|propertyName|";";
     runPolymake(script)
     )

parseBooleanProperty = method(TypicalValue => Boolean)
parseBooleanProperty(PolyhedralObject,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"PolymakeFile")|"\");
	 my $v = $object->"|propertyName|";
	 if($v){print(\"true\")}else{print(\"false\");}";
     (runPolymake(script)=="true")
     )

parseScalarProperty = method()
parseScalarProperty(PolyhedralObject,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"PolymakeFile")|"\");
	 print $object->"|propertyName|";";
     value(runPolymake(script))
     )

parseListProperty = method(TypicalValue => List)
parseListProperty(PolyhedralObject,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"PolymakeFile")|"\");
	 print $object->"|propertyName|";";
     makeList(runPolymake(script))
     )

parseMatrixProperty = method(TypicalValue => Matrix)
parseMatrixProperty(PolyhedralObject,String) := (P, propertyName) -> (
     script := "use application \"polytope\";
         my $object = load(\""|(P#"PolymakeFile")|"\");
	 print $object->"|propertyName|";";
     makeMatrix(runPolymake(script))
     )

parseProperty = method()
parseProperty(PolyhedralObject,String) := (P, propertyName) -> (
     valueType := polymakePropertyNameToValueType#propertyName;
     if (valueType=="Boolean") then (
	  parseBooleanProperty(P,propertyName)
	  )
     else if (valueType=="Integer" or valueType=="Float" or valueType=="Scalar") then (
	  parseScalarProperty(P,propertyName)
	  )
     else if (valueType=="Vector" or valueType=="Array") then (
	  parseListProperty(P,propertyName)
	  )
     else if (valueType=="Matrix") then (
	  parseMatrixProperty(P,propertyName)
	  )
     else (
	  parseUnknownProperty(P,propertyName)
	  )
     )

------------------------------------------------------------------------------
--Getting properties from cache
------------------------------------------------------------------------------

hasProperty = method()
hasProperty(PolyhedralObject,String) := (P, propertyName) -> (
     if (P#?propertyName) then (
	  true
	  )
     else if (P#?"AvailableProperties" and M2PropertyNameToPolymakePropertyName#?propertyName and P#"AvailableProperties"#?(M2PropertyNameToPolymakePropertyName#propertyName)) then (
	  true
	  )
     else (
	  false
	  )
     )

getProperty = method()
getProperty(PolyhedralObject,String) := (P, propertyName) -> (
     if (P#?propertyName) then (
	  P#propertyName
	  )
     else if (P#?"AvailableProperties" and M2PropertyNameToPolymakePropertyName#?propertyName and P#"AvailableProperties"#?(M2PropertyNameToPolymakePropertyName#propertyName)) then (
	  propertyValue := parseProperty(P,M2PropertyNameToPolymakePropertyName#propertyName);
	  P#propertyName = propertyValue;
	  propertyValue
	  )
     else (
	  error ("The polyhedral object does not have property "|propertyName);
	  )
     )

getPropertyNames = method()
getPropertyNames(PolyhedralObject) := (P) -> (
     if (P#?"AvailableProperties") then (
	  polymakePropertyNames := select(keys(P#"AvailableProperties"),x -> (polymakePropertyNameToM2PropertyName#?x));
	  M2PropertyNames := apply(polymakePropertyNames,x -> polymakePropertyNameToM2PropertyName#x);
	  new Set from M2PropertyNames
	  )
     else (
	  parsedPropertyNames := for propertyName in keys(P) when (
	       (propertyName!="AvailableProperties") and (propertyName!="PolymakeFile")
	       )
	  list propertyName;
	  new Set from parsedPropertyNames
	  )
     )

parseAllAvailableProperties = method()
parseAllAvailableProperties(PolyhedralObject) := (P) -> (
     for propertyName in keys(getPropertyNames(P)) do (
	  if (not(P#?propertyName)) then (
	       polymakePropertyName := M2PropertyNameToPolymakePropertyName#propertyName;
	       P#propertyName = parseProperty(P,polymakePropertyName);
	       )
	  )
     )

---------------------------------------------------------------------------
----- Run Polymake with PolyhedralObject

runPolymake(PolyhedralObject,String) := o -> (P,propertyName) -> (
     if (not(M2PropertyNameToPolymakePropertyName#?propertyName)) then (
	  error ("Property does not exist:"|propertyName)
	  )
     else (
	  polymakePropertyName := M2PropertyNameToPolymakePropertyName#propertyName;
          if (not(hasProperty(P,polymakePropertyName))) then (
               if (not P#?"PolymakeFile") then (
                    writePolymakeFile(P);
	            );
               script := "use application \"polytope\";
                    my $object = load(\""|(P#"PolymakeFile")|"\");
	            $object->"|polymakePropertyName|";
	            save($object,\""|(P#"PolymakeFile")|"\");
	            my @properties = $object->list_properties;
	            my $numberOfProperties = scalar @properties;
	            for(my $i=0;$i<$numberOfProperties;$i++)
	            {print \"$properties[$i]\\n\";}";
               propertiesString := runPolymake(script);
               propertiesList := lines propertiesString;
               P#"AvailableProperties" = new Set from propertiesList;
	       );
	  if (o.ParseAllProperties) then (
	       parseAllAvailableProperties(P);
	       );
	  getProperty(P,propertyName)
	  )
     )

---------------------------------------------------------------------------
-----------------------DOCUMENTATION----------------------
---------------------------------------------------------------------------

beginDocumentation()

doc ///
  Key
    PolymakeInterface
  Headline
    Interface for Polymake
  Description
   Text 
     {\tt Polymake} is a software for convex polyhedra, simplicial complexes, and other discrete geometric objects, written by Ewgenij Gawrilow and Michael Joswig.  It is available at @HREF "http://www.math.tu-berlin.de/polymake/"@. The user should have {\tt Polymake} installed on their machine.
   Text 
     Warning: this package is not complete, and is mostly undocumented, but it is used in  @TO "gfanInterface::gfanInterface"@. 
   Text
     We can use the interface to get properties of @TO "PolyhedralObjects"@
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
     PolyhedralObjects
///

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
needsPackage "PolymakeInterface"
needsPackage "Polyhedra2"
needsPackage "PolyhedralObjects"
testScript = ///
    use application "polytope";
    my $a = cube(2,2);
    print $a->F_VECTOR;
    ///
runPolymake(testScript)
P = convexHull matrix{{0,0,1,1},{0,1,0,1}}
--P#"Points" = P#"InputRays";
runPolymake(P,"Feasible")
class oo
runPolymake(P,"Bounded",ParseAllProperties=>true)
class oo
peek P
runPolymake(P,"FVector")
class oo
runPolymake(P,"Facets")
class oo
getPropertyNames(P)
class oo
peek P
parseAllAvailableProperties(P)
peek P
C = posHull matrix{{0,0,1,1},{0,1,0,1},{1,1,1,1}}
runPolymake(C,"Facets")
runPolymake(P,"dsgjewlksjflkdsjgflksdjlfksd")
getProperty(P,"sdgjlejgoiwefioew")

---------------------------------------------------------------------------
------------------------- TO DO ---------------------------
---------------------------------------------------------------------------
-- Add new properties to the table
-- Parse IncidenceMatrix,SimplicialComplex objects and other types
-- Parse all properties in one round to save the overhead
-- Documentation