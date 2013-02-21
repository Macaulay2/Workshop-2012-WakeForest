newPackage("NCAlgebra",
     Headline => "Data types for Noncommutative algebras",
     Version => "0.1",
     Date => "February 16, 2013",
     Authors => {
	  {Name => "Frank Moore",
	   HomePage => "http://www.math.wfu.edu/Faculty/Moore.html",
	   Email => "moorewf@wfu.edu"}},
     DebuggingMode => true
     )

export { NCRing, generatorSymbols, -- can I get away with not exporting this somehow?
         NCRingElement,
         NCGroebnerBasis, ncGroebnerBasis,
         NCIdeal, NCLeftIdeal, NCRightIdeal,
         ncIdeal, ncLeftIdeal, ncRightIdeal,
         twoSidedNCGroebnerBasisBergman,
         ComputeNCGB,
         InstallGB,
         CheckPrefixOnly,
         normalFormBergman,
         hilbertBergman,
         NCMatrix, ncMatrix,
         NCMonomial,
         isCentral,
         wallTiming
}

NCRing = new Type of Ring
NCRingElement = new Type of HashTable
NCGroebnerBasis = new Type of List
NCMatrix = new Type of HashTable
NCMonomial = new Type of List
NCIdeal = new Type of HashTable
NCLeftIdeal = new Type of HashTable
NCRightIdeal = new Type of HashTable
NCQuotientRing = new Type of QuotientRing

emptyMon := new NCMonomial from {}

removeZeroes := myHash -> select(myHash, c -> c != 0)

-- get base m representation of an integer n
rebase = (m,n) -> (
   if (n < 0) then error "Must provide an integer greater than or equal to 1";
   if n == 0 then return {};
   if n == 1 then return {1};
   k := floor (log_m n);
   loopn := n;
   reverse for i from 0 to k list (
      digit := loopn // m^(k-i);
      loopn = loopn % m^(k-i);
      digit
   )   
)

--- NCRing methods --------------
new NCRing from List := (NCRing, inits) -> new NCRing of NCRingElement from new HashTable from inits

Ring List := (R, varList) -> (
   A := new NCRing from {(symbol generators) => {},
                         (symbol generatorSymbols) => varList,
                         CoefficientRing => R};
   newGens := apply(varList, v -> v <- new A from {(symbol ring) => A,
                                                   (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   A#(symbol generators) = newGens;
   
   promote (ZZ,A) := (n,A) -> new A from {(symbol ring) => A,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,R))}};
   promote (QQ,A) := (n,A) -> new A from {(symbol ring) => A,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,R))}};
   promote (NCMatrix,A) := (M,A) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> promote(entry,A))); 
   promote (A,A) := (f,A) -> f;
      
   A * A := (f,g) -> (
      newHash := new MutableHashTable;
      for t in pairs f.terms do (
         for s in pairs g.terms do (
            newMon := t#0 | s#0;
            if newHash#?newMon then newHash#newMon = newHash#newMon + t#1*s#1 else newHash#newMon = t#1*s#1;
         );
      );
      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes hashTable pairs newHash)}
   );
   -- need to make this more intelligent(hah!) via repeated squaring and binary representations.
   --A ^ ZZ := (f,n) -> quickExponentiate(n,f);
   A ^ ZZ := (f,n) -> product toList (n:f);
   
   A + A := (f,g) -> (
      newHash := new MutableHashTable from pairs f.terms;
   
      for s in pairs g.terms do (
         newMon := s#0;
         if newHash#?newMon then newHash#newMon = newHash#newMon + s#1 else newHash#newMon = s#1;
      );
      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes hashTable pairs newHash)}   
   );
   R * A := (r,f) -> (
      if r == 0 then return new A from hashTable {(symbol ring, f.ring), 
                                                  (symbol terms, new HashTable from {})};

      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes applyValues(f.terms, v -> r*v))}      
   );
   A * R := (f,r) -> r*f;
   QQ * A := (r,f) -> (
      if r == 0 then return new A from hashTable {(symbol ring, f.ring), 
                                                  (symbol terms, new HashTable from {})};

      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes applyValues(f.terms, v -> r*v))}      
   );
   A * QQ := (f,r) -> r*f;
   ZZ * A := (r,f) -> (
      if r == 0 then return new A from hashTable {(symbol ring, f.ring), 
                                                  (symbol terms, new HashTable from {})};
      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes applyValues(f.terms, v -> r*v))}      
   );
   A * ZZ := (f,r) -> r*f;
   A - A := (f,g) -> f + (-1)*g;
   - A := f -> (-1)*f;
   A + ZZ := (f,r) -> f + (new f.ring from {(symbol ring) => f.ring,
                                            (symbol terms) => new HashTable from {(emptyMon,sub(r,R))}});
   ZZ + A := (r,f) -> f + r;
   A + QQ := (f,r) -> f + (new f.ring from {(symbol ring) => f.ring,
                                            (symbol terms) => new HashTable from {(emptyMon,sub(r,R))}});
   QQ + A := (r,f) -> f + r;

   A == A := (f,g) -> (sort pairs f.terms) == (sort pairs g.terms);
   A == ZZ := (f,n) -> (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n));
   ZZ == A := (n,f) -> f == n;
   A == QQ := (f,n) -> (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n));
   QQ == A := (n,f) -> f == n;
   A == R := (f,n) -> (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n));
   R == A := (n,f) -> f == n;
   A
)

coefficientRing NCRing := A -> A.CoefficientRing

generators NCRing := opts -> A -> (
    if A.?generators then A.generators else {}
)

net NCRing := A -> net A.CoefficientRing | net A.generators

use NCRing := A -> (scan(A.generatorSymbols, A.generators, (sym,val) -> sym <- val); A)
---------------------------------

------------- NCIdeal ---------------------
ncIdeal = method()
ncIdeal List := idealGens -> (
   if #idealGens == 0 then error "Expected at least one generator.";
   new NCIdeal from new HashTable from {(symbol ring) => (idealGens#0).ring,
                                        (symbol generators) => idealGens,
                                        (symbol cache) => new CacheTable from {}}
)

generators NCIdeal := opts -> I -> I.generators;

net NCIdeal := I -> "Two-sided ideal " | net (I.generators);

-------------------------------------------

--- NCQuotientRing functions --------------
new NCQuotientRing from List := (NCQuotientRing, inits) -> new NCQuotientRing of NCRingElement from new HashTable from inits

NCRing / NCIdeal := (A, I) -> (
   ncgb := ncGroebnerBasis I;
   B := new NCQuotientRing from {(symbol generators) => {},
                                 (symbol generatorSymbols) => A.generatorSymbols,
                                 CoefficientRing => A.CoefficientRing,
                                 (symbol ambient) => A,
                                 (symbol ideal) => I};
   newGens := apply(B.generatorSymbols, v -> v <- new B from {(symbol ring) => B,
                                                              (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   B#(symbol generators) = newGens;
   
   R := A.CoefficientRing;
   
   promote (A,B) := (f,B) -> new B from {(symbol ring) => B,
                                         (symbol terms) => f.terms};
   promote (B,A) := (f,A) -> new A from {(symbol ring) => A,
                                         (symbol terms) => f.terms};
   promote (ZZ,B) := (n,B) -> new B from {(symbol ring) => B,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,A.CoefficientRing))}};
   promote (QQ,B) := (n,B) -> new B from {(symbol ring) => B,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,A.CoefficientRing))}};
   promote (B,B) := (f,B) -> f;
   promote (NCMatrix,B) := (M,B) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> promote(entry,B)));
   lift B := opts -> f -> promote(f,A);
   push := f -> (
      temp := f % ncgb;
      new B from {(symbol ring) => B,
                  (symbol terms) => temp.terms}
   );
   B * B := (f,g) -> push((lift f)*(lift g));
   B ^ ZZ := (f,n) -> push((lift f)^n);  -- note that ^ for tensor algebra uses faster expon. already
   B + B := (f,g) -> push((lift f)+(lift g));
   R * B := (r,f) -> push(r*(lift f));
   B * R := (f,r) -> r*f;
   A * B := (f,g) -> push(f*(lift g));
   B * A := (f,g) -> push((lift f)*g);
   QQ * B := (r,f) -> push(r*(lift f));
   B * QQ := (f,r) -> r*f;
   ZZ * B := (r,f) -> push(r*(lift f));
   B * ZZ := (f,r) -> r*f;
   B - B := (f,g) -> f + (-1)*g;
   - B := f -> (-1)*f;
   B + ZZ := (f,r) -> push((lift f) + r);
   ZZ + B := (r,f) -> f + r;
   B + QQ := (f,r) -> push((lift f) + r);
   QQ + B := (r,f) -> f + r;

   B == B := (f,g) -> (lift(f - g) % ncgb) == 0;
   B == ZZ := (f,n) -> (f = push(lift f); (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
   ZZ == B := (n,f) -> f == n;
   B == QQ := (f,n) -> (f = push(lift f); (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
   QQ == B := (n,f) -> f == n;
   B == R := (f,n) -> (f = push(lift f); (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
   R == B := (n,f) -> f == n;
   B
)

coefficientRing NCQuotientRing := A -> A.CoefficientRing

generators NCQuotientRing := opts -> A -> (
    if A.?generators then A.generators else {}
)

-- can't get this to work
--reverseLookup := f -> S -> if hasAttribute(S,ReverseDictionary) then toString getAttribute(S,ReverseDictionary) else f expression S
--net NCQuotientRing := reverseLookup net

net NCQuotientRing := B -> net (B.ambient) | " / " | net (B.ideal.generators)

use NCQuotientRing := B -> (scan(B.generatorSymbols, B.generators, (sym,val) -> sym <- val); B)

-------------------------------------------

--- NCMonomial functions -----------
net NCMonomial := mon -> (
   if mon === emptyMon then return net "";
   myNet := net "";
   tempVar := first mon;
   curDegree := 0;
   for v in mon do (
      if v == tempVar then curDegree = curDegree + 1
      else (
          myNet = myNet | (net tempVar) | if curDegree == 1 then (net "") else ((net curDegree)^1);
          tempVar = v;
          curDegree = 1;
      );
   );
   myNet | (net tempVar) | if curDegree == 1 then (net "") else ((net curDegree)^1)
)

toString NCMonomial := mon -> (
   if mon === emptyMon then return "";
   myNet := "";
   tempVar := first mon;
   curDegree := 0;
   for v in mon do (
      if v == tempVar then curDegree = curDegree + 1
      else (
          myNet = myNet | (toString tempVar) | if curDegree == 1 then "*" else "^" | curDegree | "*";
          tempVar = v;
          curDegree = 1;
      );
   );
   myNet | (toString tempVar) | if curDegree == 1 then "" else "^" | curDegree
)

degree NCMonomial := mon -> #mon

NCMonomial _ List := (mon,substr) -> new NCMonomial from (toList mon)_substr

findSubstring = method(Options => {CheckPrefixOnly => false})
findSubstring (NCMonomial,NCMonomial) := opts -> (lt, mon) -> (
   deg := length lt;
   if opts#CheckPrefixOnly and take(toList mon, deg) == toList lt then
      return true
   else if opts#CheckPrefixOnly then
      return false;
   substrIndex := null;
   matchLength := 0;
   for i from 0 to #mon-1 do (
      if matchLength + #mon - i < deg then break;  -- break if not enough for a match
      if lt#matchLength == mon#i then matchLength = matchLength + 1 else matchLength = 0;
      if matchLength == deg then (
         substrIndex = i - deg + 1;
         break;
      );
   );
   if substrIndex =!= null then (take(mon,substrIndex),take(mon,-#mon+substrIndex+deg)) else null
)

NCMonomial ? NCMonomial := (m,n) -> if (toList m) == (toList n) then symbol == else
                                    if #m < #n then symbol < else
                                    if #m > #n then symbol > else
                                    if (#m == #n and (toList m) < (toList n)) then symbol < else symbol >
-----------------------------------------

--- NCRingElement methods ---------------
net NCRingElement := f -> (
   if #(f.terms) == 0 then "0" else (
      firstTerm := true;
      myNet := net "";
      for t in sort pairs f.terms do (
         tempNet := net t#1;
         printParens := ring t#1 =!= QQ and ring t#1 =!= ZZ and size t#1 > 1;
         myNet = myNet |
                 (if not firstTerm and t#1 > 0 then
                    net "+"
                 else 
                    net "") |
                 (if printParens then net "(" else net "") | 
                 (if t#1 != 1 and t#1 != -1 then
                    tempNet
                  else if t#1 == -1 then net "-"
                  else net "") |
                 (if printParens then net ")" else net "") |
                 (if t#0 === emptyMon and t#1 == 1 then net "1" else net t#0);
         firstTerm = false;
      );
      myNet
   )
)

toStringMaybeSort := method(Options => {"Sort" => false})
toStringMaybeSort NCRingElement := opts -> f -> (
   sortFcn := if opts#"Sort" then sort else identity;
   if #(f.terms) == 0 then "0" else (
      firstTerm := true;
      myNet := "";
      for t in sortFcn pairs f.terms do (
         tempNet := toString t#1;
         printParens := ring t#1 =!= QQ and ring t#1 =!= ZZ and size t#1 > 1;
         myNet = myNet |
                 (if not firstTerm and t#1 > 0 then
                    "+"
                 else 
                    "") |
                 (if printParens then "(" else "") | 
                 (if t#1 != 1 and t#1 != -1 then
                    tempNet | "*"
                  else if t#1 == -1 then "-"
                  else "") |
                 (if printParens then ")" else "") |
                 (if t#0 === emptyMon and t#1 == 1 then "1" else toString t#0);
         firstTerm = false;
      );
      myNet
   )
)

toString NCRingElement := f -> toStringMaybeSort(f,"Sort"=>true)

degree NCRingElement := f -> (pairs f.terms) / first / degree // max
leadTerm NCRingElement := f -> new (f.ring) from {(symbol ring) => f.ring,
                                                  (symbol terms) => new HashTable from {last sort (pairs f.terms)}};
leadMonomial NCRingElement := f -> first last sort (pairs f.terms);
leadCoefficient NCRingElement := f -> last last sort (pairs f.terms);
isConstant NCRingElement := f -> f.terms === hashTable {} or (#(f.terms) == 1 and f.terms#?{})

terms NCRingElement := f -> apply(pairs (f.terms), (m,c) -> new (f.ring) from {(symbol ring) => f.ring,
                                                                               (symbol terms) => new HashTable from {(m,c)}});

isCentral = method()
isCentral (NCRingElement, NCGroebnerBasis) := (f,ncgb) -> (
   varsList := gens f.ring;
   all(varsList, x -> (f*x - x*f) % ncgb == 0)
)

isCentral NCRingElement := f -> (
   varsList := gens f.ring;
   all(varsList, x -> (f*x - x*f) == 0)   
)

ncRingElement = method()
ncRingElement (NCMonomial,NCRing) := (mon,A) -> (
   new A from {(symbol ring) => A,
               (symbol terms) => new HashTable from {(mon,1)}}
)
----------------------------------------

----------------------------------------
--- Bergman related functions
----------------------------------------

runCommand := cmd -> (
   --- comment this line out eventually, or add a verbosity option
   stderr << "--running: " << cmd << " ... " << flush;
   r := run cmd;
   if r != 0 then error("--command failed, error return code ",r) else stderr << "Complete!" << endl;
)

writeBergmanInputFile = method(Options => {ComputeNCGB => true})
writeBergmanInputFile (List, String, ZZ) := opts -> (genList, tempInput, maxDeg) -> (
   R := (first genList).ring;
   charR := char coefficientRing R;
   
   fil := openOut tempInput;
   -- print the setup of the computation
   fil << "(noncommify)" << endl;
   fil << "(setmodulus " << charR << ")" << endl;
   fil << "(setmaxdeg " << maxDeg << ")" << endl;
   fil << "(algforminput)" << endl;
   
   -- print out the list of variables we are using
   fil << "vars ";
   gensR := gens (first genList).ring;
   lastVar := last gensR;
   scan(drop(gensR,-1), x -> fil << toStringMaybeSort x << ",");
   fil << toStringMaybeSort lastVar << ";" << endl;
   
   --- print out the generators of ideal
   lastGen := last genList;
   scan(drop(genList,-1), f -> fil << toStringMaybeSort f << ",");
   fil << toStringMaybeSort lastGen << ";" << endl;
   fil << close;
)

------------------------------------------------------
----- Bergman GB commands
------------------------------------------------------

writeGBInitFile = method()
writeGBInitFile (String, String, String) := (tempInit, tempInput, tempOutput) -> (
   fil := openOut tempInit;
   fil << "(simple \"" << tempInput << "\" \"" << tempOutput << "\")" << endl;
   fil << "(quit)" << endl << close;   
)

gbFromOutputFile = method()
gbFromOutputFile String := tempOutput -> (
   fil := openIn tempOutput;
   myFile := select(lines get fil, s -> s#0#0 != "%");
   gensList := select(apply(myFile, l -> value l), f -> class f === Sequence) / first;
   gensList = apply(gensList, f -> 1/(leadCoefficient f)*f);
   new NCGroebnerBasis from apply(gensList, f -> (f, leadMonomial f))
)

twoSidedNCGroebnerBasisBergman = method(Options=>{DegreeLimit=>100})
twoSidedNCGroebnerBasisBergman NCIdeal := opts -> I -> (
  coeffRing := coefficientRing I.ring;
  if coeffRing =!= QQ and coeffRing =!= ZZ/(char coeffRing) then
     error << "Can only handle coefficients over QQ or ZZ/p at the present time." << endl;
  -- call Bergman for this, at the moment
  tempInit := temporaryFileName() | ".init";      -- init file
  tempInput := temporaryFileName() | ".bi";       -- gb input file
  tempOutput := temporaryFileName() | ".bo";      -- gb output goes here
  tempTerminal := temporaryFileName() | ".ter";   -- terminal output goes here
  gensI := gens I;
  writeBergmanInputFile(gensI,tempInput, opts#DegreeLimit);
  writeGBInitFile(tempInit,tempInput,tempOutput);
  runCommand("bergman -i " | tempInit | " --silent > " | tempTerminal);
  gbFromOutputFile(tempOutput)
)

------------------------------------------------------
----- Bergman Normal Form commands
------------------------------------------------------

writeNFInputFile = method()
writeNFInputFile (List,NCGroebnerBasis, List, ZZ) := (fList,ncgb, inputFileList, maxDeg) -> (
   genList := (toList ncgb) / first;
   --- set up gb computation
   -- need to also test if ncgb is in fact a gb, and if so, tell Bergman not to do the computation
   writeBergmanInputFile(genList,inputFileList#0,maxDeg);
   --- now set up the normal form computation
   fil := openOut inputFileList#1;
   for f in fList do (
      fil << "(readtonormalform)" << endl;
      fil << toStringMaybeSort f << ";" << endl;
   );
   fil << close;
)
writeNFInputFile (NCRingElement, NCGroebnerBasis,List,ZZ) := (f, ncgb, inputFileList, maxDeg) ->
   writeNFInputFile({f},ncgb,inputFileList,maxDeg)

writeNFInitFile = method()
writeNFInitFile (String, String, String, String) := (tempInit, tempGBInput, tempNFInput, tempGBOutput) -> (
   fil := openOut tempInit;
   fil << "(simple \"" << tempGBInput << "\" \"" << tempGBOutput << "\")" << endl;
   fil << "(simple \"" << tempNFInput << "\")" << endl;
   fil << "(quit)" << endl << close;   
)

nfFromTerminalFile = method()
nfFromTerminalFile (NCRing,String) := (A,tempTerminal) -> (
   fil := openIn tempTerminal;
   outputLines := lines get fil;
   eltPositions := positions(outputLines, l -> l == "is reduced to");
   -- remember previous setup
   oldVarSymbols := A.generatorSymbols;
   oldVarValues := oldVarSymbols / value;
   -- switch to tensor algebra
   use A;
   retVal := outputLines_(apply(eltPositions, i -> i + 1)) / value / first;
   -- roll back to old variables
   scan(oldVarSymbols, oldVarValues, (sym,val) -> sym <- val);
   -- return normal form, promoted to A (in case there are any ZZ or QQ)
   retVal / (f -> promote(f,A))
)

normalFormBergman = method(Options => options twoSidedNCGroebnerBasisBergman)
normalFormBergman (List, NCGroebnerBasis) := opts -> (fList, ncgb) -> (
   A := (first fList).ring;
   coeffRing := coefficientRing (first fList).ring;
   if coeffRing =!= QQ and coeffRing =!= ZZ/(char coeffRing) then
      error << "Can only handle coefficients over QQ or ZZ/p at the present time." << endl;
   -- call Bergman for this, at the moment
   tempInit := temporaryFileName() | ".init";      -- init file
   tempGBInput := temporaryFileName() | ".bigb";   -- gb input file
   tempOutput := temporaryFileName() | ".bo";      -- gb output goes here
   tempTerminal := temporaryFileName() | ".ter";   -- terminal output goes here
   tempNFInput := temporaryFileName() | ".binf";   -- nf input file
   writeNFInputFile(fList,ncgb,{tempGBInput,tempNFInput},opts#DegreeLimit);
   writeNFInitFile(tempInit,tempGBInput,tempNFInput,tempOutput);
   runCommand("bergman -i " | tempInit | " --silent > " | tempTerminal);
   nfFromTerminalFile(A,tempTerminal)
)
normalFormBergman (NCRingElement, NCGroebnerBasis) := opts -> (f,ncgb) ->
   first normalFormBergman({f},ncgb,opts)

------------------------------------------------------
----- Bergman Hilbert commands
------------------------------------------------------
writeHSInitFile = method()
writeHSInitFile (String,String,String,String) := (tempInit, tempInput, tempGBOutput, tempHSOutput) -> (
   fil := openOut tempInit;
   fil << "(hilbert \"" << tempInput << "\" \"" << tempGBOutput << "\" \"" << tempHSOutput << "\")" << endl;
   fil << "(quit)" << endl << close;   
)

hsFromOutputFile = method()
hsFromOutputFile String := tempOutput -> (
   fil := openIn tempOutput;
   fileLines := lines get fil;
   fileLines
)

hilbertBergman = method(Options => {DegreeLimit => 0})  -- DegreeLimit = 0 means return rational function.
                                                        -- else return as a power series 
hilbertBergman NCQuotientRing := opts -> R -> (
  coeffRing := coefficientRing R;
  if coeffRing =!= QQ and coeffRing =!= ZZ/(char coeffRing) then
     error << "Can only handle coefficients over QQ or ZZ/p at the present time." << endl;
  -- prepare the call to bergman
  tempInit := temporaryFileName() | ".init";      -- init file
  tempInput := temporaryFileName() | ".bi";       -- gb input file
  tempGBOutput := temporaryFileName() | ".bgb";   -- gb output goes here
  tempHSOutput := temporaryFileName() | ".bhs";   -- hs output goes here
  tempTerminal := temporaryFileName() | ".ter";   -- terminal output goes here
  I := ideal R;
  gensI := gens ideal R;
  writeBergmanInputFile(gensI,tempInput,opts#DegreeLimit);
  writeHSInitFile(tempInit,tempInput,tempGBOutput,tempHSOutput);
  error "err";
  runCommand("bergman -i " | tempInit | " --silent > " | tempTerminal);
  I.cache#gb = gbFromOutputFile(tempGBOutput);
  hsFromOutputFile(tempHSOutput)
)

hilbertBergman NCRing := opts -> R -> (
)

------------------------------------------------------------------
--- End Bergman interface code
------------------------------------------------------------------

------------------------------------------------------------------
------- NCGroebnerBasis methods
------------------------------------------------------------------

leftNCGroebnerBasis = method()
leftNCGroebnerBasis List := genList -> (
)

rightNCGroebnerBasis = method()
rightNCGroebnerBasis List := genList -> (
)


ncGroebnerBasis = method(Options => {DegreeLimit => 100, InstallGB => false})
ncGroebnerBasis List := opts -> fList -> (
   if opts#InstallGB then new NCGroebnerBasis from apply(fList, f -> (f,leadMonomial f))
   else ncGroebnerBasis ncIdeal fList;
)

ncGroebnerBasis NCIdeal := opts -> I -> (
   if I.cache#?gb then return I.cache#gb;
   ncgb := if opts#InstallGB then new NCGroebnerBasis from apply(gens I, f -> (f,leadMonomial f))
           else twoSidedNCGroebnerBasisBergman(I, DegreeLimit=>opts#DegreeLimit);
   I.cache#gb = ncgb;
   ncgb   
)


net NCGroebnerBasis := ncgb -> (
   stack apply(ncgb, (pol,lt) -> (net pol) | net "; Lead Term = " | (net lt))
)

ZZ % NCGroebnerBasis := (n,ncgb) -> n
QQ % NCGroebnerBasis := (n,ncgb) -> n

basis(ZZ,NCRing,NCGroebnerBasis) := opts -> (n,A,ncgb) -> (
   basisList := {emptyMon};
   varsList := A.generatorSymbols;
   lastTerms := ncgb / last;
   for i from 1 to n do (
      basisList = flatten apply(varsList, v -> apply(basisList, b -> new NCMonomial from {v} | b));
      if ncgb =!= {} then
         basisList = select(basisList, b -> all(lastTerms, mon -> findSubstring(mon,b,CheckPrefixOnly=>true) == false));
   );
   basisList
)

multiplicationMap = method()
multiplicationMap(NCRingElement,ZZ) := (f,n) -> (
   -- Input : A form f of degree m, and a degree n
   -- Output : A matrix (over coefficientRing f.ring) representing the multiplication
   --          map from degree n to degree n+m.
   B := f.ring;
   nBasis := basis();
)

NCRingElement % NCGroebnerBasis := (f,ncgb) -> (
   if degree f <= 50 and #(f.terms) <= 50 then
      remainderFunction(f,ncgb)
   else
      first normalFormBergman({f},ncgb)
)

remainderFunction = (f,ncgb) -> (
   if #ncgb == 0 then return f;
   if (ncgb#0#0).ring =!= f.ring then error "Expected GB over the same ring.";
   newf := f;
   pairsf := sort pairs newf.terms;
   prefSuf := null;
   gbHit := null;
   coeff := null;
   for p in pairsf do (
      for q in ncgb do (
         prefSuf = findSubstring(q#1,p#0);
         gbHit = q;
         coeff = p#1;
         if prefSuf =!= null then break;
      );
      if prefSuf =!= null then break;
   );
   while prefSuf =!= null do (
      pref := new (f.ring) from {(symbol ring) => f.ring,
                                 (symbol terms) => new HashTable from {(new NCMonomial from prefSuf#0,1)}};
      suff := new (f.ring) from {(symbol ring) => f.ring,
                                 (symbol terms) => new HashTable from {(new NCMonomial from prefSuf#1,1)}};
      newf = newf - coeff*pref*(gbHit#0)*suff;
      pairsf = sort pairs newf.terms;
      prefSuf = null;
      gbHit = null;
      coeff = null;
      for p in pairsf do (
         for q in ncgb do (
            prefSuf = findSubstring(q#1,p#0);
            if prefSuf =!= null then (
               gbHit = q;
               coeff = p#1;
               break;
            )
         );
         if prefSuf =!= null then break;
      );
   );
   newf
)
---------------------------------------

----NCMatrix Commands -----------------
ncMatrix = method()
ncMatrix List := ncEntries -> (
   if not isTable ncEntries then error "Expected a rectangular matrix.";
   new NCMatrix from hashTable {(symbol ring, (ncEntries#0#0).ring), 
                                (symbol matrix, ncEntries)}
)

lift NCMatrix := opts -> M -> ncMatrix apply(M.matrix, row -> apply(row, entry -> promote(entry,(M.ring.ambient))))

NCMatrix * NCMatrix := (M,N) -> (
   if M.ring =!= N.ring then error "Expected matrices over the same ring.";
   B := M.ring;
   colsM := length first M.matrix;
   rowsN := length N.matrix;
   if colsM != rowsN then error "Maps not composable.";
   rowsM := length M.matrix;
   colsN := length first N.matrix;
   -- lift entries of matrices to tensor algebra
   if class B === NCQuotientRing then (
      MoverTens := lift M;
      NoverTens := lift N;
      prodOverTens := MoverTens*NoverTens;
      ncgb := B.ideal.cache#gb;
      reducedMatr := prodOverTens % ncgb;
      promote(reducedMatr,B)
   )
   else
      ncMatrix apply(toList (0..(rowsM-1)), i -> apply(toList (0..(colsN-1)), j -> sum(0..(colsM-1), k -> ((M.matrix)#i#k)*((N.matrix)#k#j))))
)

NCMatrix % NCGroebnerBasis := (M,ncgb) -> (
   -- this function should be only one call to bergman
   -- the nf for a list is there already, just need to do entries, nf, then unpack.
   colsM := #(first M.matrix);
   entriesM := flatten M.matrix;
   entriesMNF := normalFormBergman(entriesM, ncgb);
   ncMatrix pack(colsM,entriesMNF)
)

-- need to make this more intelligent(hah!) via repeated squaring and binary representations.
NCMatrix ^ ZZ := (M,n) -> product toList (n:M)

NCMatrix + NCMatrix := (M,N) -> (
   if M.ring =!= N.ring then error "Expected matrices over the same ring.";
   colsM := length first M.matrix;
   rowsN := length N.matrix;
   rowsM := length M.matrix;
   colsN := length first N.matrix;
   if colsM != colsN or rowsM != rowsN then error "Matrices not the same shape.";
   ncMatrix apply(toList(0..(rowsM-1)), i -> apply(toList(0..(colsM-1)), j -> M.matrix#i#j + N.matrix#i#j))
)

NCMatrix - NCMatrix := (M,N) -> (
   if M.ring =!= N.ring then error "Expected matrices over the same ring.";
   colsM := length first M.matrix;
   rowsN := length N.matrix;
   rowsM := length M.matrix;
   colsN := length first N.matrix;
   if colsM != colsN or rowsM != rowsN then error "Matrices not the same shape.";

   ncMatrix apply(toList(0..(rowsM-1)), i -> apply(toList(0..(colsM-1)), j -> M.matrix#i#j - N.matrix#i#j))
)

NCMatrix * ZZ := (M,r) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> entry*sub(r,M.ring.CoefficientRing)))
ZZ * NCMatrix := (r,M) -> M*r
NCMatrix * QQ := (M,r) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> entry*sub(r,M.ring.CoefficientRing)))
QQ * NCMatrix := (r,M) -> M*r
NCMatrix * RingElement := (M,r) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> entry*r))
RingElement * NCMatrix := (r,M) -> M*r
NCMatrix * NCRingElement := (M,r) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> entry*r))
NCRingElement * NCMatrix := (r,M) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> r*entry))

--- for printing out the matrices; taken from the core M2 code for
--- usual matrix printouts (though simplified)
net NCMatrix := M -> net expression M
expression NCMatrix := M -> MatrixExpression applyTable(M.matrix, expression)

------------------------------------------------------------
--- fast exponentiation via repeated squaring
-----------------------------------------------------------
quickExponentiate = method()
quickExponentiate (ZZ, NCRingElement) := (n, f) -> (
   if n == 0 then return promote(1,f.ring);
   expList := rebase(2,n);
   loopPower := f;
   product for i from 0 to #expList-1 list (
      oldLoopPower := loopPower;
      if i != #expList-1 then loopPower = loopPower * loopPower;  -- last time through no need to exp again
      if expList#i == 0 then continue else oldLoopPower
   )
)

quickExponentiate (ZZ, NCMatrix) := (n, M) -> (
   rowsM := length M.matrix;
   colsM := length first M.matrix;
   if rowsM != colsM then error "Expected a square matrix.";
   if n == 0 then return ncMatrix apply(0..(rowsM-1), r -> apply(0..(colsM-1), c -> if r == c then promote(1,M.ring) else promote(0,M.ring)));
   expList := rebase(2,n);
   loopPower := M;
   matrList := for i from 0 to #expList-1 list (
      oldLoopPower := loopPower;
      if i != #expList-1 then loopPower = loopPower * loopPower;  -- last time through no need to exp again
      if expList#i == 0 then continue else oldLoopPower
   );
   product matrList
)

-------------------------------------------------------------
------- end package code ------------------------------------

-------------------- timing code ---------------------------
wallTime = Command (() -> value get "!date +%s")
wallTiming = f -> (
    a := wallTime(); 
    r := f(); 
    b := wallTime();  
    << "wall time : " << b-a << " seconds" << endl;
    r);

end

--- other things too maybe:
--- anick          -- resolution
--- ncpbhgroebner  -- gb, hilbert series
--- NCModules (?) (including module gb, hilbert series, modulebettinumbers)
--- NCRingMap
--- Finding a k-basis of central elements in a given degree
--- Finding a k-basis of normal elements in a given degree
--- Factoring one (homogeneous) map through another

--- matrix factorizations over sklyanin algebra
restart
debug needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3}
Igb = ncGroebnerBasis I
normalFormBergman(-y^3-x*y*z+y*x*z+x^3,Igb)
B = A/I
g = -y^3-x*y*z+y*x*z+x^3
--- skip the next line if you want to work in the tensor algebra
h = x^2 + y^2 + z^2
isCentral h
isCentral g
M3 = ncMatrix {{x,y,z,0},
               {-y*z-2*x^2,-y*x,z*x-x*z,x},
               {x*y-2*y*x,x*z,-x^2,y},
               {-y^2-z*x,x^2,-x*y,z}}
M4 = ncMatrix {{-z*y,-x,z,y},
               {z*x-x*z,z,-y,x},
               {x*y,y,x,-z},
               {2*x*y*z-4*x^3,-2*x^2,2*y^2,2*x*y-2*y*x}}
M3' = M3^2
--- can now work in quotient ring!
M3*M4
M4*M3
M1 = ncMatrix {{x}}
M2 = ncMatrix {{y}}
M1*M2
--- apparently it is very important to reduce your entries along the way.
wallTiming (() -> M3^6)
wallTiming (() -> quickExponentiate(6,M3))
--- still much slower!  It seems that reducing all along the way is much more efficient.
wallTiming (() -> M3'^5)
wallTiming (() -> quickExponentiate(5,M3'))

--- or can work over free algebra and reduce later
M4*M3 % ncgb
M3*M4 % ncgb
M3' = M3 % ncgb'
M4' = M4 % ncgb'
M3'*M4' % ncgb
M4'*M3' % ncgb

M3+M4
2*M3
(g*M3 - M3*g) % ncgb
M3^4 % ncgb
wallTiming (() -> M3^4 % Igb)
---------------------------------------------

---- working in quantum polynomial ring -----
restart
needsPackage "NCAlgebra"
R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
A = R{x,y,z}
--- this is a gb of the poly ring skewed by a fifth root of unity.
I = ncIdeal {y*x - q*x*y, z*y - q*y*z, z*x - q*x*z}
ncgb = ncGroebnerBasis(I,InstallGB=>true)
B = A / I

-- get a basis of the degree n piece of A over the base ring
time bas = basis(100,A,ncgb);

--- we can verify that f is central in this ring, for example
f = x^5 + y^5 + z^5
g = x^4 + y^4 + z^4
isCentral f
isCentral g

-- example computation
h = f^3
------------------------------------------------------

--- testing out Bergman interface
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3}
Igb = twoSidedNCGroebnerBasisBergman I
wallTiming(() -> normalFormBergman(z^20,Igb))
time (z^20 % Igb)  -- still slow!
B = A / I
g = -y^3-x*y*z+y*x*z+x^3
isCentral g
hilbertBergman B

-----------
-- this doesn't work since it is not homogeneous unless you use degree q = 0, which is not allowed.
restart
needsPackage "NCAlgebra"
A = QQ{q,x,y,z}
I = ncIdeal {q^4+q^3+q^2+q+1, q*x-x*q, q*y-y*q, q*z-z*q, y*x - q*x*y, z*y - q*y*z, z*x - q*x*z}
Igb = twoSidedNCGroebnerBasisBergman I
