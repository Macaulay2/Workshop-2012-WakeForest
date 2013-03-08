newPackage("NCAlgebra",
     Headline => "Data types for Noncommutative algebras",
     Version => "0.2",
     Date => "March 8, 2013",
     Authors => {
	  {Name => "Frank Moore",
	   HomePage => "http://www.math.wfu.edu/Faculty/Moore.html",
	   Email => "moorewf@wfu.edu"},
	  {Name => "Andrew Conner",
	   HomePage => "http://www.math.wfu.edu/Faculty/Conner.html",
	   Email => "connerab@wfu.edu"}},
     DebuggingMode => true
     )

export { NCRing, NCQuotientRing, generatorSymbols, bergmanRing, -- can I get away with not exporting these somehow?
         NCRingElement,
         NCGroebnerBasis, ncGroebnerBasis,
         NCIdeal, NCLeftIdeal, NCRightIdeal,
         ncIdeal, ncLeftIdeal, ncRightIdeal,
         twoSidedNCGroebnerBasisBergman,
         ComputeNCGB,
         InstallGB,
         NumberOfBins,
         CheckPrefixOnly,
         normalFormBergman,
         hilbertBergman,
         isLeftRegular,
         isRightRegular,
         centralElements,
         leftMultiplicationMap,
         rightMultiplicationMap,
         rightHomogKernel,
         rHomogKerSmart,
         getLeftProductRows,
         NCMatrix, ncMatrix,
         NCMonomial,
         isCentral,
         wallTiming
}

bergmanPath = "~/bergman"

NCRing = new Type of Ring
NCQuotientRing = new Type of Ring
NCPolynomialRing = new Type of Ring
NCRingElement = new Type of HashTable
NCGroebnerBasis = new Type of List
NCMatrix = new Type of HashTable
NCMonomial = new Type of List
NCIdeal = new Type of HashTable
NCLeftIdeal = new Type of HashTable
NCRightIdeal = new Type of HashTable

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
                         CoefficientRing => R,
                         (symbol bergmanRing) => false};
   newGens := apply(varList, v -> v <- new A from {(symbol ring) => A,
                                                   (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   A#(symbol generators) = newGens;
   
   promote (ZZ,A) := (n,A) -> new A from {(symbol ring) => A,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,R))}};
   promote (QQ,A) := (n,A) -> new A from {(symbol ring) => A,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,R))}};
   promote (R,A) := (n,A) -> new A from {(symbol ring) => A,
                                         (symbol terms) => new HashTable from {(emptyMon,n)}};
   promote (NCMatrix,A) := (M,A) -> ncMatrix apply(M.matrix, row -> apply(row, entry -> promote(entry,A))); 
   promote (A,A) := (f,A) -> f;
   
   if R === QQ or R === ZZ/(char R) then A#(symbol bergmanRing) = true;
      
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

   A == A := (f,g) -> #(f.terms) == #(g.terms) and (sort pairs f.terms) == (sort pairs g.terms);
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
                                 (symbol bergmanRing) => false,
                                 (symbol ambient) => A,
                                 (symbol ideal) => I};
   newGens := apply(B.generatorSymbols, v -> v <- new B from {(symbol ring) => B,
                                                              (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   B#(symbol generators) = newGens;
   
   R := A.CoefficientRing;
   
   if R === QQ or R === ZZ/(char R) then B#(symbol bergmanRing) = true;

   promote (A,B) := (f,B) -> new B from {(symbol ring) => B,
                                         (symbol terms) => f.terms};
   promote (B,A) := (f,A) -> new A from {(symbol ring) => A,
                                         (symbol terms) => f.terms};
   promote (ZZ,B) := (n,B) -> new B from {(symbol ring) => B,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,A.CoefficientRing))}};
   promote (QQ,B) := (n,B) -> new B from {(symbol ring) => B,
                                          (symbol terms) => new HashTable from {(emptyMon,sub(n,A.CoefficientRing))}};
   promote (R,B) := (n,B) -> new B from {(symbol ring) => B,
                                         (symbol terms) => new HashTable from {(emptyMon,n)}};
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

putInRing = method()
putInRing (NCMonomial, NCRing) := (mon,A) ->
      new A from {(symbol ring) => A,
                  (symbol terms) => new HashTable from {(mon,1)}}
putInRing (NCMonomial, NCQuotientRing) := (mon,B) ->
      new B from {(symbol ring) => B,
                  (symbol terms) => new HashTable from {(mon,1)}}

NCMonomial _ List := (mon,substr) -> new NCMonomial from (toList mon)_substr

findSubstring = method(Options => {CheckPrefixOnly => false})
findSubstring (NCMonomial,NCMonomial) := opts -> (lt, mon) -> (
   deg := length lt;
   if opts#CheckPrefixOnly and take(toList mon, deg) == toList lt then
      return true
   else if opts#CheckPrefixOnly then
      return false;
   substrIndex := null;
   for i from 0 to #mon-1 do (
      if #mon - i < deg then break;
      if lt == mon_{i..i+deg-1} then (
         substrIndex = i;
         break;
      );
   );
   if substrIndex =!= null then (take(mon,substrIndex),take(mon,-#mon+deg+substrIndex)) else null
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

ring NCRingElement := f -> f.ring

coefficients NCRingElement := opts -> f -> (
   B := f.ring;
   if not isHomogeneous f then error "Extected a homogeneous element.";
   mons := if opts#Monomials === null then flatten entries monomials f else opts#Monomials;
   coeffs := transpose matrix {apply(mons, m -> (m' := first keys m.terms;
                                                 if (f.terms)#?m' then
                                                    promote((f.terms)#m',coefficientRing B)
                                                 else
                                                    promote(0,coefficientRing B)))}
   -- changed temporarily
   --(ncMatrix {mons},coeffs)
)

monomials NCRingElement := opts -> f -> ncMatrix {apply(sort keys f.terms, mon -> putInRing(mon,f.ring))}

toString NCRingElement := f -> toStringMaybeSort(f,"Sort"=>true)

degree NCRingElement := f -> (keys f.terms) / degree // max
leadTerm NCRingElement := f -> new (f.ring) from {(symbol ring) => f.ring,
                                                  (symbol terms) => new HashTable from {last sort (pairs f.terms)}};
leadMonomial NCRingElement := f -> putInRing(last sort (keys f.terms),f.ring);
leadCoefficient NCRingElement := f -> last last sort (pairs f.terms);
isConstant NCRingElement := f -> f.terms === hashTable {} or (#(f.terms) == 1 and f.terms#?{})
isHomogeneous NCRingElement := f -> (
    fTerms := keys f.terms;
    degf := degree first fTerms;
    all(fTerms / degree, d -> d == degf)
)

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
   if not opts#ComputeNCGB then
   (
      fil << "(load \"" << bergmanPath << "/lap/clisp/unix/hseries.fas\")" << endl;
      fil << "(setinterruptstrategy minhilblimits)" << endl;
      fil << "(setinterruptstrategy minhilblimits)" << endl;
      fil << "(sethseriesminima " << concatenate (maxDeg:"skipcdeg ") << ")" << endl;
   );
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

twoSidedNCGroebnerBasisBergman = method(Options=>{DegreeLimit=>10})
twoSidedNCGroebnerBasisBergman NCIdeal := opts -> I -> (
  if not I.ring.bergmanRing then
     error << "Bergman interface can only handle coefficients over QQ or ZZ/p at the present time." << endl;
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
   writeBergmanInputFile(genList,inputFileList#0,maxDeg, ComputeNCGB=>true);
   --- now set up the normal form computation
   fil := openOut inputFileList#1;
   for f in fList do (
      fil << "(readtonormalform)" << endl;
      fil << toStringMaybeSort f << ";" << endl;
   );
   fil << close;
)
writeNFInputFile (NCRingElement, NCGroebnerBasis, List, ZZ) := (f, ncgb, inputFileList, maxDeg) ->
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
   if not A.bergmanRing then 
      error << "Bergman interface can only handle coefficients over QQ or ZZ/p at the present time." << endl;
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
hilbertBergman NCQuotientRing := opts -> B -> (
  if not B.bergmanRing then 
     error << "Bergman interface can only handle coefficients over QQ or ZZ/p at the present time." << endl;
  -- prepare the call to bergman
  tempInit := temporaryFileName() | ".init";      -- init file
  tempInput := temporaryFileName() | ".bi";       -- gb input file
  tempGBOutput := temporaryFileName() | ".bgb";   -- gb output goes here
  tempHSOutput := temporaryFileName() | ".bhs";   -- hs output goes here
  tempTerminal := temporaryFileName() | ".ter";   -- terminal output goes here
  I := ideal B;
  gensI := gens ideal B;
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

basis(ZZ,NCRing) := opts -> (n,A) -> (
   basisList := {emptyMon};
   varsList := A.generatorSymbols;
   for i from 1 to n do (
      basisList = flatten apply(varsList, v -> apply(basisList, b -> new NCMonomial from {v} | b));
   );
   ncMatrix {apply(basisList, mon -> putInRing(mon,A))}
)

basis(ZZ,NCQuotientRing) := opts -> (n,B) -> (
   ncgb := ncGroebnerBasis B.ideal;
   basisList := {emptyMon};
   varsList := B.generatorSymbols;
   lastTerms := apply(ncgb / last, mon -> first keys mon.terms);
   for i from 1 to n do (
      basisList = flatten apply(varsList, v -> apply(basisList, b -> new NCMonomial from {v} | b));
      if ncgb =!= {} then
         basisList = select(basisList, b -> all(lastTerms, mon -> findSubstring(mon,b,CheckPrefixOnly=>true) == false));
   );
   ncMatrix {apply(basisList, mon -> putInRing(mon,B))}
)

leftMultiplicationMap = method()
leftMultiplicationMap(NCRingElement,ZZ) := (f,n) -> (
   -- Input : A form f of degree m, and a degree n
   -- Output : A matrix (over coefficientRing f.ring) representing the left multiplication
   --          map from degree n to degree n+m.
   B := f.ring;
   if not isHomogeneous f then error "Expected a homogeneous element.";
   m := degree f;
   nBasis := flatten entries basis(n,B);
   nmBasis := flatten entries basis(n+m,B);
   coeffList := apply(nBasis, m -> (if f*m==0 then transpose matrix{apply(toList(0..(#nmBasis-1)),i->0)}
                                    else transpose matrix {flatten entries last coefficients(f*m,Monomials=>nmBasis)}));
   matrix {coeffList}
)



rightMultiplicationMap = method()
rightMultiplicationMap(NCRingElement,ZZ) := (f,n) -> (
   -- Input : A form f of degree m, and a degree n
   -- Output : A matrix (over coefficientRing f.ring) representing the left multiplication
   --          map from degree n to degree n+m.
   B := f.ring;
   if not isHomogeneous f then error "Expected a homogeneous element.";
   m := degree f;
   nBasis := flatten entries basis(n,B);
   nmBasis := flatten entries basis(n+m,B);
   coeffList := apply(nBasis, m -> (if m*f==0 then transpose matrix{apply(toList(0..(#nmBasis-1)),i->0)}
                                    else transpose matrix {flatten entries last coefficients(m*f,Monomials=>nmBasis)}));
   matrix {coeffList}
)

centralElements = method()
centralElements(NCQuotientRing,ZZ) := (B,n) -> (
   -- This function returns a basis over R = coefficientRing B of the central
   -- elements in degree n.
   ringVars := gens B;
   diffMatrix := matrix apply(ringVars, x -> {leftMultiplicationMap(x,n) - rightMultiplicationMap(x,n)});
   nBasis := basis(n,B);
   kerDiff := ker diffMatrix;
   R := ring diffMatrix;
   if kerDiff == 0 then sub(matrix{{}},R) else nBasis * (gens kerDiff)
)

rightHomogKernel = method()
rightHomogKernel(NCMatrix, ZZ) := (M,d) -> (
   -- Assume (without checking) that the entries of M are homogeneous of the same degree n
   -- This function takes a NCMatrix M and a degree d and returns the left kernel in degree d over the tensor algebra
   rows := # entries M;
   cols := # first M.matrix;
   n := max apply(flatten entries M, i->degree i);
   degnBasis := flatten entries basis(n,M.ring);
   -- We compute the left multiplication maps once and for all. 
   -- In the future, maybe only compute them for elements actually appearing in the matrix.
   maps := apply(degnBasis, e->leftMultiplicationMap(e,d));
   B := basis(d,M.ring);
   dimB := #(flatten entries B); --the number of rows of K is dim*cols
   dimT := #(flatten entries basis(n+d,M.ring)); --the number of rows in multiplication map
   -- Make a big matrix of left multiplication maps for each row and get its kernel
   S := apply(toList(0..(rows-1)), i-> 
        ker matrix{apply(toList(0..(cols-1)), j->(
          if (M.matrix)#i#j==0 then matrix apply(toList(0..(dimT-1)), b->apply(toList(0..(dimB-1)),a->0))
          else
             coeffs := flatten entries last coefficients((M.matrix)#i#j,Monomials=>degnBasis);
             sum(0..(#degnBasis-1),k->(coeffs#k)*(maps#k)))
        )});
   Kscalar := gens intersect S;
   if Kscalar == 0 then return 0
   else
   K := ncMatrix apply(toList(0..(cols-1)), k-> flatten ((lift B)*submatrix(Kscalar,{k*dimB..(k*dimB+dimB-1)},)).matrix)
)

rHomogKerSmart = method(Options=>{NumberOfBins => 1, Verbosity=>0})
rHomogKerSmart(NCMatrix,ZZ):= opts -> (M,deg) -> (
   -- Assume (without checking) that the entries of M are homogeneous of the same degree n
   -- This function takes a NCMatrix M and a degree deg and returns the left kernel in degree deg over the tensor algebra. 
   -- Increasing bins can provide some memory savings if the degree deg part of the ring is large. Optimal bin size seems to be in the 1000-2000 range.
   bins := opts#NumberOfBins;
   rows := # entries M;
   cols := # first M.matrix;
   n := max apply(flatten entries M, i->degree i);

   bas := basis(deg,M.ring);
   fromBasis := flatten entries bas;
   toBasis := flatten entries basis(deg+n,M.ring);

   fromDim := #fromBasis; --the number of rows of K is dim*cols
   toDim := #toBasis; --the number of rows in multiplication map

   -- packing variables
   if toDim % bins != 0 then error "Basis doesn't divide evenly into that many bins";
   pn := toDim//bins; -- denominator is number of bins
   pB := pack(toBasis,pn);

   -- zero vectors
   fromZeros := apply(toList(0..(fromDim-1)),i->0);
   toZeros := transpose matrix{apply(toList(0..(#(pB#0)-1)),i->0)};
   zeroMat := matrix{apply(fromZeros, i-> toZeros)};
 
   -- get left product rows (no need for separate function call)
   U:=unique select(flatten entries M, c->c!=0);
   if opts#Verbosity > 0 then
      << "Building hash table." << endl;
   L:= hashTable apply(U,e->{e,flatten entries (e*bas)}); --returns a hash table of product rows for nonzero entries of M (slow, but a one-time cost)

   --initialize (in an effort to save space, we're going to overwrite these variables in the loops below)
   Kscalar := (coefficientRing M.ring)^(fromDim*cols);
   nextKer := 0;  

   for row from 0 to (rows-1) when Kscalar!=0 do (
       if opts#Verbosity > 0 then 
          << "Computing kernel of row " << row+1 << " of " << rows << endl; 

       for ind from 0 to (#pB-1) when Kscalar!=0 do (
       	   if opts#Verbosity > 0 then
              << "Converting to coordinates" << endl;
	   -- the following is the most expensive step in the calculation time-wise. 
           coeffs := matrix{ flatten apply((M.matrix)#row,i-> (
	   	    	    	           if i==0 then
                                              return zeroMat
	   	    	    	           else 
				              apply(L#i,j-> (if j == 0 then return toZeros else coefficients(j,Monomials=>pB#ind)))  
				           ))};

       	   nextKer = ker coeffs;
	   if opts#Verbosity > 0 then
              << "Updating kernel" << endl;
	   Kscalar = intersect(Kscalar,nextKer);
	   );
   );

   if Kscalar == 0 then
      return 0
   else
      if opts#Verbosity > 0 then << "Kernel computed. Reverting to ring elements." << endl;
   ncMatrix apply(toList(0..(cols-1)), k-> {bas*submatrix(gens Kscalar,{k*fromDim..(k*fromDim+fromDim-1)},)})
)

isLeftRegular = method()
isLeftRegular (NCRingElement, ZZ) := (f,d) -> (
   A := ring f;
   if not isHomogeneous f then error "Expected a homogeneous element.";
   r := rank rightMultiplicationMap(f,d);
   s := #(flatten entries basis(d,A));
   r == s
)

isRightRegular = method()
isRightRegular (NCRingElement, ZZ) := (f,d) -> (
   A := ring f;
   if not isHomogeneous f then error "Expected a homogeneous element.";
   r := rank leftMultiplicationMap(f,d);
   s := #(flatten entries basis(d,A));
   r == s
)

NCRingElement % NCGroebnerBasis := (f,ncgb) -> (
   if (degree f <= 5000 and #(f.terms) <= 5000) or not f.ring.bergmanRing then
      remainderFunction(f,ncgb)
   else
      first normalFormBergman({f},ncgb)
)


remainderFunction = (f,ncgb) -> (
   if #ncgb == 0 then return f;
   if (ncgb#0#0).ring =!= f.ring then error "Expected GB over the same ring.";
   ncgb = apply(ncgb, p -> (p#0, first keys (p#1).terms));
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
--- Would like to have the option of creating a matrix whose entries are matrices.
--- Also, really should have graded maps if possible.
ncMatrix = method()
ncMatrix List := ncEntries -> (
   if #ncEntries == 0 then error "Expected a nonempty list.";
   if not isTable ncEntries then error "Expected a rectangular matrix.";
   rows := #ncEntries;
   cols := #(ncEntries#0);
   --- here, we need to find a common ring to promote all the entries to before checking anything else.
   ringList := (flatten ncEntries) / ring;
   B := (ringList)#(position(ringList, r -> class r === NCQuotientRing or class r === NCRing));
   ncEntries = applyTable(ncEntries, e -> promote(e,B));
   types := ncEntries // flatten / class // unique;
   if #types != 1 then error "Expected a table of either NCRingElements over the same ring or NCMatrices.";
   if ancestor(NCRingElement,types#0) then (
      new NCMatrix from hashTable {(symbol ring, (ncEntries#0#0).ring), 
                                   (symbol matrix, ncEntries)}
   )
   else if types#0 === NCMatrix then (
      -- this block of code handles a matrix of matrices and creates a large matrix from that
      blockEntries := applyTable(ncEntries, entries);
      -- this is a hash table with the sizes of the matrices in the matrix
      sizeHash := new HashTable from flatten apply(rows, i -> apply(cols, j -> (i,j) => (#(blockEntries#i#j), #(blockEntries#i#j#0))));
      -- make sure the blocks are of the right size, and all matrices are defined over same ring.
      if not all(rows, i -> #(unique apply(select(pairs sizeHash, (e,m) -> e#0 == i), (e,m) -> m#0)) == 1) then
         error "Expected all matrices in a row to have the same number of rows.";
      if not all(cols, j -> #(unique apply(select(pairs sizeHash, (e,m) -> e#1 == j), (e,m) -> m#1)) == 1) then
         error "Expected all matrices in a column to have the same number of columns.";
      rings := unique apply(flatten ncEntries, m -> m.ring);
      if #rings != 1 then error "Expected all matrices to be defined over the same ring.";
      -- now we may perform the conversion.
      newEntries := flatten for i from 0 to rows-1 list
                            for k from 0 to (sizeHash#(i,0))#0-1 list (
                               flatten for j from 0 to cols-1 list
                                       for l from 0 to (sizeHash#(0,j))#1-1 list blockEntries#i#j#k#l
                            );
      new NCMatrix from hashTable {(symbol ring, (ncEntries#0#0).ring), 
                                   (symbol matrix, newEntries)}
   )
)

ring NCMatrix := M -> M.ring

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
      -- not sure which of the below is faster
      -- ncMatrix apply(toList (0..(rowsM-1)), i -> apply(toList (0..(colsN-1)), j -> sum(0..(colsM-1), k -> ((M.matrix)#i#k)*((N.matrix)#k#j))))
      ncMatrix table(toList (0..(rowsM-1)), toList (0..(colsN-1)), (i,j) -> sum(0..(colsM-1), k -> ((M.matrix)#i#k)*((N.matrix)#k#j)))
)

NCMatrix * Matrix := (M,N) -> (
   N' := sub(N,coefficientRing M.ring);
   N'' := ncMatrix applyTable(entries N, e -> promote(e,M.ring));
   M*N''
)

Matrix * NCMatrix := (N,M) -> (
   N' := sub(N,coefficientRing M.ring);
   N'' := ncMatrix applyTable(entries N, e -> promote(e,M.ring));
   N''*M
)

NCMatrix % NCGroebnerBasis := (M,ncgb) -> (
   -- this function should be only one call to bergman
   -- the nf for a list is there already, just need to do entries, nf, then unpack.
   coeffRing := coefficientRing M.ring;
   colsM := #(first M.matrix);
   entriesM := flatten M.matrix;
   entriesMNF := if true or (coeffRing =!= QQ and coeffRing =!= ZZ/(char coeffRing)) then 
                    apply(entriesM, f -> f % ncgb)
                 else
                    normalFormBergman(entriesM, ncgb);
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
NCMatrix * RingElement := (M,r) -> M*(promote(r,M.ring))
RingElement * NCMatrix := (r,M) -> (promote(r,M.ring)*M)
NCMatrix * NCRingElement := (M,r) -> (
   B := M.ring;
   s := promote(r,B);
   -- lift entries of matrices to tensor algebra
   if class B === NCQuotientRing then (
      MOverTens := lift M;
      sOverTens := lift s;
      prodOverTens := MOverTens*sOverTens;
      ncgb := B.ideal.cache#gb;
      reducedMatr := prodOverTens % ncgb;
      promote(reducedMatr,B)
   )
   else
      ncMatrix applyTable(M.matrix, m -> m*s)
)
NCRingElement * NCMatrix := (r,M) -> (
   B := M.ring;
   s := promote(r,B);
   -- lift entries of matrices to tensor algebra
   if class B === NCQuotientRing then (
      MOverTens := lift M;
      sOverTens := lift s;
      prodOverTens := sOverTens*MOverTens;
      ncgb := B.ideal.cache#gb;
      reducedMatr := prodOverTens % ncgb;
      promote(reducedMatr,B)
   )
   else
      ncMatrix applyTable(M.matrix, m -> s*m)
)

entries NCMatrix := M -> M.matrix
transpose NCMatrix := M -> ncMatrix transpose M.matrix


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
wallTime = Command (() -> value get "!date +%s.%N")
wallTiming = f -> (
    a := wallTime(); 
    r := f(); 
    b := wallTime();  
    << "wall time : " << b-a << " seconds" << endl;
    r);
------------------------------------------------------------
end

--- other things too maybe:
--- anick          -- resolution
--- ncpbhgroebner  -- gb, hilbert series
--- NCModules (?) (including module gb, hilbert series, modulebettinumbers)
--- NCRingMap
--- Use Bergman to compute module generators of kernels of NCMatrix?
--- Ore extensions
--- Free resolutions of koszul algebras
--- Finding a k-basis of normal elements in a given degree (not even a k-space!  How to do this?)
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
centralElements(B,3)
g = -y^3-x*y*z+y*x*z+x^3
isLeftRegular(g,6)
M=ncMatrix{{z,-x,-y},{-y,z,-x},{x,y,z}}
rightHomogKernel(M,1)
rHomogKerSmart(basis(1,B),10,1)
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
time bas = basis(10,B);
coefficients(x*y+q^2*x*z)
bas2 = flatten entries basis(2,B)
(mons,coeffs) = coefficients(x*y+q^2*x*z, Monomials => bas2)
first flatten entries (mons*coeffs)
-- yay!
ncMatrix {{coeffs, coeffs},{coeffs,coeffs}}
basis(2,B)
basis(3,B)
leftMultiplicationMap(x,2)
rightMultiplicationMap(x,2)
centralElements(B,4)
centralElements(B,5)

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
wallTiming(() -> normalFormBergman(z^10,Igb))
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
coefficients (I.gens)#1
Igb = twoSidedNCGroebnerBasisBergman I

---- ore extensions
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,z,w}}
M2 = rHomogKerSmart(M1,1)
M3 = rHomogKerSmart(M2,1)
M4 = rHomogKerSmart(M3,1)
M5 = rHomogKerSmart(M4,1)
M6 = rHomogKerSmart(M5,1)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M4A
M6A

---- ore extensions
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,z,w}}
M2 = rHomogKerSmart(M1,1)
M3 = rHomogKerSmart(M2,1)
M4 = rHomogKerSmart(M3,1)
M5 = rHomogKerSmart(M4,1)
M6 = rHomogKerSmart(M5,1)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M4A
M6A

---- ore extension of skew ring
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
M2 = rHomogKerSmart(M1,1)
M2 = rHomogKerSmart(M1,2)
M2 = rHomogKerSmart(M1,3)
M3 = rHomogKerSmart(M2,1)
M4 = rHomogKerSmart(M3,1)
M5 = rHomogKerSmart(M4,1)
M6 = rHomogKerSmart(M5,1)
M7 = rHomogKerSmart(M6,1)
M8 = rHomogKerSmart(M7,1)
M9 = rHomogKerSmart(M8,1)
M10 = rHomogKerSmart(M9,1)
M3A = promote(M3,A)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M7A = promote(M7,A)
M8A = promote(M8,A)
M9A = promote(M9,A)
M10A = promote(M10,A)

---- ore extension of sklyanin
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
I = ncIdeal {f1,f2,f3,x*w-w*y,y*w-w*z,z*w-w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
M2 = rHomogKerSmart(M1,1)
M2 = rHomogKerSmart(M1,2)
M2 = rHomogKerSmart(M1,3)
M2 = rHomogKerSmart(M1,4)
M3 = rHomogKerSmart(M2,1)
M4 = rHomogKerSmart(M3,1)
M5 = rHomogKerSmart(M4,1)
M6 = rHomogKerSmart(M5,1)
M7 = rHomogKerSmart(M6,1)
M8 = rHomogKerSmart(M7,1)
M9 = rHomogKerSmart(M8,1)
M10 = rHomogKerSmart(M9,1)
M3A = promote(M3,A)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M7A = promote(M7,A)
M8A = promote(M8,A)
M9A = promote(M9,A)
M10A = promote(M10,A)

---- ore extension of skew ring with infinite automorphism
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-2*w*y,y*w-2*w*z,z*w-2*w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
M2 = rHomogKerSmart(M1,1)
M2 = rHomogKerSmart(M1,2)
M3 = rHomogKerSmart(M2,1)
M4 = rHomogKerSmart(M3,1)
M5 = rHomogKerSmart(M4,1)
M6 = rHomogKerSmart(M5,1)
M7 = rHomogKerSmart(M6,1)
M8 = rHomogKerSmart(M7,1)
M9 = rHomogKerSmart(M8,1)
M10 = rHomogKerSmart(M9,1)
M3A = promote(M3,A)
M4A = promote(M4,A)
M5A = promote(M5,A)
M6A = promote(M6,A)
M7A = promote(M7,A)
M8A = promote(M8,A)
M9A = promote(M9,A)
M10A = promote(M10,A)

--- test for speed of reduction code
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z,w}
I = ncIdeal {x*y+y*x,x*z+z*x,y*z+z*y,x*w-2*w*y,y*w-2*w*z,z*w-2*w*x,w^2}
B = A/I
M1 = ncMatrix {{x,y,w}}
time M2 = rHomogKerSmart(M1,7,Verbosity=>1);
time M3 = rHomogKerSmart(M2,3);

