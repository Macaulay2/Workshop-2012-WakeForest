newPackage("NCAlgebra",
     Headline => "Data types for Noncommutative algebras",
     Version => "0.1",
     Date => "December 13, 2012",
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
         NCMatrix, ncMatrix,
         NCMonomial,
         isCentral
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

--- NCRing methods --------------
new NCRing from List := (NCRing, inits) -> new NCRing of NCRingElement from new HashTable from inits

Ring List := (R, varList) -> (
   A := new NCRing from {(symbol generators) => {},
                         (symbol generatorSymbols) => varList,
                         CoefficientRing => R};
   newGens := apply(varList, v -> v <- new A from {(symbol ring) => A,
                                                   (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   A#(symbol generators) = newGens;
   
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
                            (symbol terms, removeZeroes applyValues(f.terms, v -> sub(r,QQ)*v))}      
   );
   A * QQ := (f,r) -> r*f;
   ZZ * A := (r,f) -> (
      if r == 0 then return new A from hashTable {(symbol ring, f.ring), 
                                                  (symbol terms, new HashTable from {})};

      new A from hashTable {(symbol ring, f.ring), 
                            (symbol terms, removeZeroes applyValues(f.terms, v -> sub(r,ZZ)*v))}      
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
   B := new NCQuotientRing from {(symbol generators) => {},
                                 (symbol generatorSymbols) => A.generatorSymbols,
                                 CoefficientRing => A.CoefficientRing,
                                 (symbol ambient) => A,
                                 (symbol ideal) => I};
   newGens := apply(B.generatorSymbols, v -> v <- new B from {(symbol ring) => B,
                                                              (symbol terms) => new HashTable from {(new NCMonomial from {v},1)}});
   B#(symbol generators) = newGens;
   
   ncgb := ncGroebnerBasis I;
   R := A.CoefficientRing;
   
   lift B := opts -> f -> new A from {(symbol ring) => A,
                              (symbol terms) => f.terms};
   
   push := f -> (
      temp := f % ncgb;
      new B from {(symbol ring) => B,
                  (symbol terms) => temp.terms}
   );
   B * B := (f,g) -> push ((lift f)*(lift g));
   B ^ ZZ := (f,n) -> push((lift f)^n);
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
   B == ZZ := (f,n) -> (f = (lift f) % ncgb; (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
   ZZ == B := (n,f) -> f == n;
   B == QQ := (f,n) -> (f = (lift f) % ncgb; (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
   QQ == B := (n,f) -> f == n;
   B == R := (f,n) -> (f = (lift f) % ncgb; (#(f.terms) == 0 and n == 0) or (#(f.terms) == 1 and ((first pairs f.terms)#0 === emptyMon) and ((first pairs f.terms)#1 == n)));
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

NCMonomial _ List := (mon,substr) -> new NCMonomial from (toList mon)_substr

findSubstring = method()
findSubstring (NCMonomial,NCMonomial) := (lt, mon) -> (
   deg := length lt;
   substrIndex := null;
   for i from 0 to #mon-deg do (
      if lt == mon_{i..(i+(deg-1))} then (
         substrIndex = i;
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

leadTerm NCRingElement := f -> new (f.ring) from {(symbol ring) => f.ring,
                                                  (symbol terms) => new HashTable from {last sort (pairs f.terms)}};
leadMonomial NCRingElement := f -> first last sort (pairs f.terms);
leadCoefficient NCRingElement := f -> last last sort (pairs f.terms);
isConstant NCRingElement := f -> f.terms === hashTable {} or (#(f.terms) == 1 and f.terms#?{})

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

------- NCGroebnerBasis methods --------

-- For now, one must create this with a program that can compute noncommutative GBs, like Bergman.
-- The code assumes that the list is a GB in the deglex order

leftNCGroebnerBasis = method()
leftNCGroebnerBasis List := genList -> (
)

rightNCGroebnerBasis = method()
rightNCGroebnerBasis List := genList -> (
)

twoSidedNCGroebnerBasis = method()
twoSidedNCGroebnerBasis List := genList -> (
)

ncGroebnerBasis = method()
ncGroebnerBasis List := gbList -> (
   new NCGroebnerBasis from apply(gbList, f -> (f,leadMonomial f))
)

ncGroebnerBasis NCIdeal := I -> (
   if I.cache#?gb then return I.cache#gb;
   ncgb := new NCGroebnerBasis from apply(gens I, f -> (f,leadMonomial f));
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
   scan(n, i -> basisList = flatten apply(varsList, v -> apply(basisList, b -> new NCMonomial from {v} | b)));
   leadTerms := ncgb / last;
   select(basisList, b -> all(leadTerms, mon -> findSubstring(mon,b) === null))
)

NCRingElement % NCGroebnerBasis := (f,ncgb) -> (
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

NCMatrix * NCMatrix := (M,N) -> (
   if M.ring =!= N.ring then error "Expected matrices over the same ring.";
   colsM := length first M.matrix;
   rowsN := length N.matrix;
   if colsM != rowsN then error "Maps not composable.";
   rowsM := length M.matrix;
   colsN := length first N.matrix;
   ncMatrix apply(toList (0..(rowsM-1)), i -> apply(toList (0..(colsN-1)), j -> sum(0..(colsM-1), k -> ((M.matrix)#i#k)*((N.matrix)#k#j))))
)

NCMatrix % NCGroebnerBasis := (M,ncgb) -> (
   ncMatrix apply(M.matrix, row -> apply(row, entry -> entry % ncgb))
)

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

-------------------------------------------------------------
------- end package code ------------------------------------

end

--- other things too maybe:
--- compute GB (up to a certain limit) in free algebra
--- ask Bergman to compute GB and import it?
--- compute kernels and images of graded maps over graded algebra (even if just a k-basis in each degree...)
--- factor one map through another

--- matrix factorizations over sklyanin algebra
restart
needsPackage "NCAlgebra"
A = QQ{x,y,z}
f1 = y*z + z*y - x^2
f2 = x*z + z*x - y^2
f3 = z^2 - x*y - y*x
f4 = y*x^2 - x^2*y
f5 = y^2*x - x*y^2
g = -y^3-x*y*z+y*x*z+x^3
I = ncIdeal {f1,f2,f3,f4,f5}
ncgb = ncGroebnerBasis I
--- skip the next line if you want to work in the tensor algebra
B = A/I
M3 = ncMatrix {{x,y,z,0},
               {-y*z-2*x^2,-y*x,z*x-x*z,x},
               {x*y-2*y*x,x*z,-x^2,y},
               {-y^2-z*x,x^2,-x*y,z}}
M4 = ncMatrix {{-z*y,-x,z,y},
               {z*x-x*z,z,-y,x},
               {x*y,y,x,-z},
               {2*x*y*z-4*x^3,-2*x^2,2*y^2,2*x*y-2*y*x}}
--- can now work in quotient ring!
M3*M4
M4*M3

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
M3^3 % ncgb
time (M3^4 % ncgb)
---------------------------------------------

---- working in quantum polynomial ring -----
restart
needsPackage "NCAlgebra"
R = QQ[q]/ideal{q^4+q^3+q^2+q+1}
A = R{x,y,z}
--- this is a gb of the poly ring skewed by a fifth root of unity.
I = ncIdeal {y*x - q*x*y, z*y - q*y*z, z*x - q*x*z}
B = A / I

-- get a basis of the degree n piece of A over the base ring
basis(3,A,ncgb)

--- we can verify that f is central in this ring, for example
f = x^5 + y^5 + z^5
g = x^4 + y^4 + z^4
isCentral f
isCentral g

-- example computation
h = f^3
