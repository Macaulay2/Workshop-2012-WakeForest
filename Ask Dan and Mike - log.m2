
+ /Users/dan/src/M2/trunk/M2/BUILD/dan/builds.tmp/mac64.production/M2 --no-readline --print-width 97
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : hello there
stdio:1:1:(3): error: no method for adjacent objects:
--            hello (of class Symbol)
--    SPACE   there (of class Symbol)

i2 : x

o2 = x

o2 : Symbol

i3 : "x"

o3 = x

i4 : x_3

o4 = x
      3

o4 : IndexedVariable

i5 : class o2

o5 = Symbol

o5 : Type

i6 : class "x"

o6 = String

o6 : Type

i7 : x

o7 = x

o7 : Symbol

i8 : dictionaryPath 

o8 = {SimpleDoc.Dictionary, User#"private dictionary", User.Dictionary, Elimination.Dictionary,
     --------------------------------------------------------------------------------------------
     LLLBases.Dictionary, IntegralClosure.Dictionary, PrimaryDecomposition.Dictionary,
     --------------------------------------------------------------------------------------------
     Classic.Dictionary, TangentCone.Dictionary, ReesAlgebra.Dictionary,
     --------------------------------------------------------------------------------------------
     ConwayPolynomials.Dictionary, Core.Dictionary, OutputDictionary, PackageDictionary}

o8 : List

i9 : keys Elimination.Dictionary

o9 = {Elimination$discriminant, discriminant, eliminate, Elimination$eliminate, sylvesterMatrix,
     --------------------------------------------------------------------------------------------
     Elimination$sylvesterMatrix, resultant, Elimination$resultant}

o9 : List

i10 : x

o10 = x

o10 : Symbol

i11 : mutable\dictionaryPath 

o11 = {false, true, true, false, false, false, false, false, false, false, false, false, true,
      -------------------------------------------------------------------------------------------
      true}

o11 : List

i12 : dictionaryPath

o12 = {SimpleDoc.Dictionary, User#"private dictionary", User.Dictionary, Elimination.Dictionary,
      -------------------------------------------------------------------------------------------
      LLLBases.Dictionary, IntegralClosure.Dictionary, PrimaryDecomposition.Dictionary,
      -------------------------------------------------------------------------------------------
      Classic.Dictionary, TangentCone.Dictionary, ReesAlgebra.Dictionary,
      -------------------------------------------------------------------------------------------
      ConwayPolynomials.Dictionary, Core.Dictionary, OutputDictionary, PackageDictionary}

o12 : List

i13 : x=3

o13 = 3

i14 : dictionary symbol x

o14 = User#"private dictionary"

o14 : GlobalDictionary

i15 : dictionary local x

i16 : local x, global x

o16 = (x, x)

o16 : Sequence

i17 : dictionary symbol res

o17 = Core.Dictionary

o17 : GlobalDictionary

i18 : getSymbol "res"

o18 = res

o18 : Symbol

i19 : dictionary oo

o19 = User#"private dictionary"

o19 : GlobalDictionary

i20 : res

o20 = res

o20 : Symbol

i21 : dictionaryPath 

o21 = {SimpleDoc.Dictionary, User#"private dictionary", User.Dictionary, Elimination.Dictionary,
      -------------------------------------------------------------------------------------------
      LLLBases.Dictionary, IntegralClosure.Dictionary, PrimaryDecomposition.Dictionary,
      -------------------------------------------------------------------------------------------
      Classic.Dictionary, TangentCone.Dictionary, ReesAlgebra.Dictionary,
      -------------------------------------------------------------------------------------------
      ConwayPolynomials.Dictionary, Core.Dictionary, OutputDictionary, PackageDictionary}

o21 : List

i22 : newPackage "Foo"
--loading configuration for package "Foo" from file /Users/dan/Library/Application Support/Macaulay2/init-Foo.m2
--new configuration options for package Foo
--backup file created: /Users/dan/Library/Application Support/Macaulay2/init-Foo.m2.bak
--storing configuration for package Foo in /Users/dan/Library/Application Support/Macaulay2/init-Foo.m2

o22 = Foo

o22 : Package

i23 : dictionaryPath 

o23 = {SimpleDoc.Dictionary, Foo#"private dictionary", Foo.Dictionary, Elimination.Dictionary,
      -------------------------------------------------------------------------------------------
      LLLBases.Dictionary, IntegralClosure.Dictionary, PrimaryDecomposition.Dictionary,
      -------------------------------------------------------------------------------------------
      Classic.Dictionary, TangentCone.Dictionary, ReesAlgebra.Dictionary,
      -------------------------------------------------------------------------------------------
      ConwayPolynomials.Dictionary, Core.Dictionary, OutputDictionary, PackageDictionary}

o23 : List

i24 : dictionary x

i25 : dictionary symbol x

i26 : x=3

o26 = 3

i27 : dictionary symbol x

i28 : keys Foo#'private dictionary"
stdio:28:10:(2): error: invalid character

i28 : keys Foo#"private dictionary"

o28 = {}

o28 : List

i29 : "
      

i29 : keys Foo#"private dictionary"

o29 = {}

o29 : List

i30 : f = () -> ()

o30 = f

o30 : FunctionClosure

i31 : keys Foo#"private dictionary"

o31 = {f}

o31 : List

i32 : symbol xxx

o32 = xxx

o32 : Symbol

i33 : keys Foo#"private dictionary"

o33 = {xxx, f}

o33 : List

i34 : symbol x

o34 = x

o34 : Symbol

i35 : keys Foo#"private dictionary"

o35 = {xxx, f}

o35 : List

i36 : symbol xx

o36 = xx

o36 : Symbol

i37 : vars 23

o37 = x

o37 : Symbol

i38 : dictionary vars 23

i39 : endPackage "Foo"
--warning: symbol "res" in Core.Dictionary is shadowed by a symbol in User#"private dictionary"
--  use one of the synonyms Core$res, Core$resolution, resolution
stdio:41:1:(2): error: mutable unexported unset symbol(s) in package Foo: 'xxx', 'xx'
stdio:34:8-34:11: here is the first use of 'xxx'
stdio:38:8-38:10: here is the first use of 'xx'

i40 : dictionary vars 23

o40 = User#"private dictionary"

o40 : GlobalDictionary

i41 : newPackage "Foo"
stdio:43:1:(3): error: package Foo not reloaded; try Reload => true

i42 : newPackage "Fooo"

o42 = Fooo

o42 : Package

i43 : rr = 1

o43 = 1

i44 : ss := 2

o44 = 2

i45 : export {"tt"}

o45 = {tt}

o45 : List

i46 : tt = 3

o46 = 3

i47 : endPackage "Fooo"

o47 = Fooo

o47 : Package

i48 : rr,ss,tt

o48 = (rr, 2, 3)        ------- 2

o48 : Sequence

i49 : newPackage "Foooo"

o49 = Foooo

o49 : Package

i50 : export "f"

o50 = {f}

o50 : List

i51 : f = () -> ( QQ(monoid [ getSymbol "x" ] ) )

o51 = f

o51 : FunctionClosure

i52 : endPackage "Foooo"

o52 = Foooo

o52 : Package

i53 : f()

o53 = QQ[x]

o53 : PolynomialRing

i54 : x

o54 = 3

i55 : use o53

o55 = QQ[x]

o55 : PolynomialRing

i56 : x

o56 = 3         -- oops

i57 : R = QQ[a..e]

o57 = R

o57 : PolynomialRing

i58 : R_2

o58 = c

o58 : R

i59 : R_"c"

o59 = c

o59 : R

i60 : 3_R

o60 = 3

o60 : R

i61 : symbol c

o61 = c

o61 : Symbol

i62 : value oo

o62 = c

o62 : R

i63 : S = QQ( monoid [ e_1 .. e_5 ] )
stdio:65:19:(3):[1]: error: no method for binary operator _ applied to objects:
--            e (of class R)
--      _     1 (of class ZZ)

i64 : S = QQ( monoid [ symbol e_1 .. symbol e_5 ] )
warning: clearing value of symbol e to allow access to subscripted variables based on it
       : debug with expression   debug 3903   or with command line option   --debug 3903

o64 = S

o64 : PolynomialRing

i65 : e_1

o65 = e
       1

o65 : S

i66 : T := QQ( monoid [ symbol f_1 .. symbol f_5 ] )

o66 = QQ[f , f , f , f , f ]
          1   2   3   4   5

o66 : PolynomialRing

i67 : f_1

o67 = {*Function[../../trunk/M2/Macaulay2/m2/classes.m2:66:44-66:59]*}

o67 : FunctionClosure

i68 : f

o68 = f

o68 : FunctionClosure

i69 : symbol f_1

o69 = f
       1

o69 : IndexedVariable

i70 : value oo 

o70 = f
       1

o70 : IndexedVariable

i71 : use T
warning: clearing value of symbol f to allow access to subscripted variables based on it
       : debug with expression   debug 3406   or with command line option   --debug 3406
stdio:73:1:(3): error: assignment to protected variable 'f'

i72 : restart
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : T := QQ( monoid [ symbol f_1 .. symbol f_5 ] )

o1 = QQ[f , f , f , f , f ]
         1   2   3   4   5

o1 : PolynomialRing

i2 : f_1

o2 = f
      1

o2 : IndexedVariable

i3 : value oo

o3 = f
      1

o3 : IndexedVariable

i4 : use T

o4 = QQ[f , f , f , f , f ]
         1   2   3   4   5

o4 : PolynomialRing

i5 : value o2

o5 = f
      1

o5 : QQ[f , f , f , f , f ]
         1   2   3   4   5

i6 : newPackage "Foooo"

o6 = Foooo

o6 : Package

i7 : x = getSymbol "x"

o7 = x

o7 : Symbol

i8 : f = () -> x

o8 = f

o8 : FunctionClosure

i9 : export "f" 

o9 = {f}

o9 : List

i10 : endPackage "Foooo"
--warning: symbol "f" in User#"private dictionary" is shadowed by a symbol in Foooo.Dictionary
--  use the synonym f$0

o10 = Foooo

o10 : Package

i11 : f()

o11 = x

o11 : Symbol

i12 : oo===x

o12 = true

i13 : R := QQ(monoid[r_1 .. r_5 ])

o13 = QQ[r , r , r , r , r ]
          1   2   3   4   5

o13 : PolynomialRing

i14 : r_1

o14 = r
       1

o14 : IndexedVariable

i15 : R_(symbol r_2)

o15 = r
       2

o15 : QQ[r , r , r , r , r ]
          1   2   3   4   5

i16 : x := local x

o16 = x

o16 : Symbol

i17 : U = QQ[x]

o17 = U

o17 : PolynomialRing

i18 : x

o18 = x

o18 : U

i19 : symbol x

o19 = x

o19 : Symbol

i20 : global x

o20 = x

o20 : Symbol

i21 : symbol x === global x

o21 = false

i22 : hash symbol x, hash global x

o22 = (1202132, 1202086)

o22 : Sequence

i23 : x := getSymbol "x"
stdio:23:1:(3): warning: local declaration of x shields variable with same name

o23 = x

o23 : Symbol

i24 : aa := getSymbol "bb"

o24 = bb

o24 : Symbol

i25 : aa = 5

o25 = 5

i26 : value getSymbol "bb"

o26 = bb

o26 : Symbol

i27 : bb = 5555

o27 = 5555

i28 : value getSymbol "bb"

o28 = 5555

i29 : aa

o29 = 5

i30 : o24

o30 = bb

o30 : Symbol

i31 : value oo

o31 = 5555

i32 : o24

o32 = bb

o32 : Symbol

i33 : o24 <- 878787

o33 = 878787

i34 : bb

o34 = 878787

i35 : aa

o35 = 5

i36 : o24

o36 = bb

o36 : Symbol

i37 : o24 = 100!

o37 = 9332621544394415268169923885626670049071596826438162146859296389521759999322991560894146397
      6156518286253697920827223758251185210916864000000000000000000000000

i38 : o24

o38 = 9332621544394415268169923885626670049071596826438162146859296389521759999322991560894146397
      6156518286253697920827223758251185210916864000000000000000000000000

i39 : o40

o39 = o40

o39 : Symbol

i40 : o40

o40 = o40

o40 : Symbol

i41 : o40

o41 = o40

o41 : Symbol

i42 : o39

o42 = o40

o42 : Symbol

i43 : (o43=7;asdf)

o43 = asdf

o43 : Symbol

i44 : o43

o44 = 7            -- ???????????????

i45 : ooo

o45 = asdf

o45 : Symbol

i46 : o43

o46 = 7

i47 : dictionary symbol o43 , dictionary symbol o44

o47 = (User#"private dictionary", OutputDictionary)

o47 : Sequence

i48 : dictionaryPath 

o48 = {Foooo.Dictionary, SimpleDoc.Dictionary, User#"private dictionary", User.Dictionary,
      -------------------------------------------------------------------------------------------
      Elimination.Dictionary, LLLBases.Dictionary, IntegralClosure.Dictionary,
      -------------------------------------------------------------------------------------------
      PrimaryDecomposition.Dictionary, Classic.Dictionary, TangentCone.Dictionary,
      -------------------------------------------------------------------------------------------
      ReesAlgebra.Dictionary, ConwayPolynomials.Dictionary, Core.Dictionary, OutputDictionary,
      -------------------------------------------------------------------------------------------
      PackageDictionary}

o48 : List

i49 : M = ZZ^5

        5
o49 = ZZ

o49 : ZZ-module, free

i50 : peek M

o50 = Module of Vector{cache => CacheTable{...2...}                           }
                       numgens => 5
                       RawFreeModule => free(rank 5 degrees = {1, 1, 1, 1, 1})
                       ring => ZZ

i51 : mutable M

o51 = false

i52 : M#foo = bar
stdio:52:7:(3): error: attempted to modify an immutable hash table

i53 : mutable ideal 4

o53 = false

i54 : mutable Ideal

o54 = true

i55 : unique { ZZ^5, ZZ^4, ZZ^5 }

         5    4
o55 = {ZZ , ZZ }

o55 : List

i56 : unique { QQ[x], QQ[x] }

o56 = {QQ[x], QQ[x]}

o56 : List

i57 : unique { QQ[x], QQ[x,y], QQ[x,x,x] }

o57 = {QQ[x], QQ[x, y], QQ[x, x, x]}

o57 : List

i58 : R = QQ[x]

o58 = QQ[x]

o58 : PolynomialRing

i59 : R[y]

o59 = QQ[x][y]

o59 : PolynomialRing

i60 : degrees oo

o60 = {{1, 0}}

o60 : List

i61 : degree y

o61 = {1, 0}

o61 : List

i62 : degree x_o59

o62 = {0, 1}

o62 : List

i63 : R[z,Join=>false]

o63 = QQ[x][z]

o63 : PolynomialRing

i64 : degree z

o64 = {1}

o64 : List

i66 : options betti

o66 = OptionTable{Weights => null}

o66 : OptionTable

i67 : use R

o67 = QQ[x]

o67 : PolynomialRing

i68 : x

o68 = x

o68 : Symbol         -- ?????

i69 : restart
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : QQ[a..e]

o1 = QQ[a, b, c, d, e]

o1 : PolynomialRing

i2 : res coker vars o1

                        1                        5                        10                        10                        5                        1
o2 = (QQ[a, b, c, d, e])  <-- (QQ[a, b, c, d, e])  <-- (QQ[a, b, c, d, e])   <-- (QQ[a, b, c, d, e])   <-- (QQ[a, b, c, d, e])  <-- (QQ[a, b, c, d, e])  <-- 0
                                                                                                                                                              
     0                        1                        2                         3                         4                        5                        6

o2 : ChainComplex

i3 : betti oo

            0 1  2  3 4 5
o3 = total: 1 5 10 10 5 1
         0: 1 5 10 10 5 1

o3 : BettiTally

i4 : peek oo

o4 = BettiTally{(0, {0}, 0) => 1 }
                (1, {1}, 1) => 5
                (2, {2}, 2) => 10
                (3, {3}, 3) => 10
                (4, {4}, 4) => 5
                (5, {5}, 5) => 1

i5 : R = QQ[a,b, Degrees => {{1,0},{0,2}}]

o5 = R

o5 : PolynomialRing

i6 : betti res coker vars R

            0 1 2
o6 = total: 1 2 1
         0: 1 1 .
         1: . 1 1

o6 : BettiTally

i7 : peek oo

o7 = BettiTally{(0, {0, 0}, 0) => 1}
                (1, {0, 2}, 2) => 1
                (1, {1, 0}, 1) => 1
                (2, {1, 2}, 3) => 1

i8 : heft R

o8 = {1, 1}

o8 : List

i9 : ideal vars R

o9 = ideal (a, b)

o9 : Ideal of R

i11 : o9^0

o11 = ideal 1

o11 : Ideal of R

i12 : monomialIdeal  oo

o12 = monomialIdeal 1

o12 : MonomialIdeal of R

i13 : oo^0
stdio:13:3:(3): error: missing unit element

i14 : errorDepth

o14 = 3

i15 : errorDepth=1

o15 = 1

i16 : errorDepth=2

o16 = 2

i17 : o12^0
stdio:17:4:(3): error: missing unit element

i18 : errorDepth=1

o18 = 1

i19 : o12^0
../trunk/M2/Macaulay2/m2/monideal.m2:44:49:(1):[1]: error: missing unit element
../../trunk/M2/Macaulay2/m2/monideal.m2:44:49:(1):[1]: --entering debugger (type help to see debugger commands)
../../trunk/M2/Macaulay2/m2/monideal.m2:44:49-44:69: --source code:
MonomialIdeal ^ ZZ := MonomialIdeal => (I,n) -> SimplePowerMethod(I,n)

ii20 : debug Core

ii21 : SimplePowerMethod

oo21 = SimplePowerMethod

oo21 : CompiledFunction

ii22 : code oo

oo22 = function 'SimplePowerMethod': source code not available

ii23 : restart
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : R = QQ[x]

o1 = R

o1 : PolynomialRing

i2 : monomialIdeal x

o2 = monomialIdeal(x)

o2 : MonomialIdeal of R

i3 : oo^0

o3 = monomialIdeal 1

o3 : MonomialIdeal of R

i4 : oo^-1
stdio:4:3:(3): error: you dummy!

i5 : apropos "local"

o5 = {local, localDictionaries, localize}

o5 : List

i6 : apropos "init"

o6 = {InfiniteNumber, infinity, isFinite, isInfinite}

o6 : List

i7 : apropos "ath"

o7 = {dictionaryPath, mathML, path, prefixPath, realpath, rootPath, searchPath, texMath,
     --------------------------------------------------------------------------------------------
     toAbsolutePath}

o7 : List

i8 : apropos "nit"

o8 = {getNonUnit, InfiniteNumber, infinity, isFinite, isInfinite, isUnit, SelfInitializingType}

o8 : List

i9 : applicationDirectory()

o9 = /Users/dan/Library/Application Support/Macaulay2/

i10 : path

o10 = {./, /Users/dan/Library/Application Support/Macaulay2/code/, /Users/dan/Library/Application
      -------------------------------------------------------------------------------------------
      Support/Macaulay2/local/share/Macaulay2/, /Users/dan/Library/Application
      -------------------------------------------------------------------------------------------
      Support/Macaulay2/local/common/share/Macaulay2/, ../../trunk/M2/Macaulay2/packages/,
      -------------------------------------------------------------------------------------------
      ../../trunk/M2/BUILD/dan/builds.tmp/mac64.production/Macaulay2/packages/,
      -------------------------------------------------------------------------------------------
      ../../trunk/M2/BUILD/dan/builds.tmp/mac64.production/StagingArea/common/share/Macaulay2/}

o10 : List

i11 : f = () -> (
      

i11 : apropos "init"

o11 = {InfiniteNumber, infinity, isFinite, isInfinite}

o11 : List

i12 : -- (global-set-key [ f9 ] 'comint-previous-matching-input-from-input)
      -- (setq M2-indent-level 58)
      
      6

o12 = 6

i13 : 
      
      
      

Process M2 finished


+ /Users/dan/src/M2/trunk/M2/BUILD/dan/builds.tmp/mac64.production/M2 --no-readline --print-width 97
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : 

Process M2<1> finished

+ ssh u00 M2 --no-readline --print-width 97
Macaulay2, version 1.3.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, SchurRings, TangentCone

i1 : 100!
100!

o1 = 93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976
     156518286253697920827223758251185210916864000000000000000000000000

i2 : run "hostname"
run "hostname"
u00.math.uiuc.edu

o2 = 0

i3 : run "type M2"
run "type M2"
M2 is /home/25/dan/local.Linux/bin/M2

o3 = 0

i4 : run "ls -l /home/25/dan/local.Linux/bin/M2"
run "ls -l /home/25/dan/local.Linux/bin/M2"
lrwxrwxrwx 1 dan graysoft 31 Jun  1  2011 /home/25/dan/local.Linux/bin/M2 -> ../encap/Macaulay2-1.3.1/bin/M2

o4 = 0

i5 : run "ls -lL /home/25/dan/local.Linux/bin/M2"
run "ls -lL /home/25/dan/local.Linux/bin/M2"
-rwxr-xr-x 1 dan academic 9097172 Sep  2  2010 /home/25/dan/local.Linux/bin/M2

o5 = 0

i6 : -- we did C-U f12 and edited the command line to be:
     -- "ssh u00 M2 --no-readline --print-width 97 "
     -- by adding "ssh u00 " to the front

Process M2<1> finished

+ ssh u00
u00$ hostname
u00.math.uiuc.edu
u00$ M2 --no-readline --print-width 97 
Macaulay2, version 1.3.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, SchurRings, TangentCone

i1 : -- (global-set-key [ f11 ] 'M2-send-to-program)
     path

o1 = {./, .Macaulay2/code/, .Macaulay2/local/share/Macaulay2/,
     --------------------------------------------------------------------------------------------
     .Macaulay2/local/common/share/Macaulay2/, local.Linux/share/Macaulay2/}

o1 : List

i2 : 
u00$ !! -q
M2 --no-readline --print-width 97  -q
Macaulay2, version 1.3.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, SchurRings, TangentCone

i1 : path

o1 = {./, local.Linux/share/Macaulay2/}

o1 : List

i2 : peek loadedFiles 

o2 = MutableHashTable{0 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/version.m2                                     }
                      1 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/command.m2
                      2 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/classes.m2
                      3 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/option.m2
                      4 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/methods.m2
                      5 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/profile.m2
                      6 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/autoload.m2
                      7 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/system.m2
                      8 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/debugging.m2
                      9 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/remember.m2
                      10 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/set.m2
                      11 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/files.m2
                      12 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/fold.m2
                      13 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/max.m2
                      14 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/structure.m2
                      15 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/combinatorics.m2
                      16 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/lists.m2
                      17 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/nets.m2
                      18 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/robust.m2
                      19 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/content.m2
                      20 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/html0.m2
                      21 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/validate.m2
                      22 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/expressions.m2
                      23 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/peek.m2
                      24 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/printing.m2
                      25 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/gateway.m2
                      26 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/rings.m2
                      27 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/integers.m2
                      28 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/engine.m2
                      29 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/enginering.m2
                      30 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/rationals.m2
                      31 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/reals.m2
                      32 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/quotient.m2
                      33 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/powers.m2
                      34 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/orderedmonoidrings.m2
                      35 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/variables.m2
                      36 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/indeterminates.m2
                      37 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/ofcm.m2
                      38 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/tables.m2
                      39 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/modules.m2
                      40 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/matrix.m2
                      41 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/matrix1.m2
                      42 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/mutablemat.m2
                      43 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/quotring.m2
                      44 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/multilin.m2
                      45 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/genmat.m2
                      46 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/modules2.m2
                      47 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/statuscodes.m2
                      48 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/gb.m2
                      49 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/matrix2.m2
                      50 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/colon.m2
                      51 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/galois.m2
                      52 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/ringmap.m2
                      53 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/newring.m2
                      54 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/matrix3.m2
                      55 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/ext.m2
                      56 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/tor.m2
                      57 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/duals.m2
                      58 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/gradedmodules.m2
                      59 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/chaincomplexes.m2
                      60 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/res.m2
                      61 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/monideal.m2
                      62 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/radical.m2
                      63 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/factor.m2
                      64 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/integrate.m2
                      65 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/http.m2
                      66 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/minPres.m2
                      67 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/monomcurve.m2
                      68 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/fano.m2
                      69 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/schubert.m2
                      70 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/code.m2
                      71 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/dotdot.m2
                      72 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/local.m2
                      73 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/packages.m2
                      74 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/document.m2
                      75 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/hypertext.m2
                      76 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/texhtml.m2
                      77 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/html.m2
                      78 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/varieties.m2
                      79 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/mathml.m2
                      80 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/texmacs.m2
                      81 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/pretty.m2
                      82 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/undoc.m2
                      83 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/obsolete.m2
                      84 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/exports.m2
                      85 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/tvalues.m2
                      86 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/typicalvalues.m2
                      87 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/installedpackages.m2
                      88 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Text.m2
                      89 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/SimpleDoc.m2
                      90 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Elimination.m2
                      91 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/LLLBases.m2
                      92 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/PrimaryDecomposition/GTZ.m2
                      93 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/PrimaryDecomposition/Shimoyama-Yokoyama.m2
                      94 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/PrimaryDecomposition/Eisenbud-Huneke-Vasconcelos.m2
                      95 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/PrimaryDecomposition/radical.m2
                      96 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/PrimaryDecomposition.m2
                      97 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/ReesAlgebra.m2
                      98 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/IntegralClosure.m2
                      99 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Parsing.m2
                      100 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Classic.m2
                      101 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/SchurRings.m2
                      102 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/TangentCone.m2
                      103 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/ConwayPolynomials.m2
                      104 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/last.m2
                      105 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/loads.m2
                      106 => /home/25/dan/local.Linux/encap/Macaulay2-1.3.1/share/Macaulay2/Core/setup.m2

i3 : 
u00$ logout
Connection to u00.math.uiuc.edu closed.

Process M2<1> finished

+ /foo/bar --print-width 97
/bin/sh: /foo/bar: No such file or directory

Process M2<1> exited abnormally with code 127


+ /Users/dan/src/M2/trunk/M2/BUILD/dan/builds.tmp/mac64.production/M2 --print-width 97
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition,
               ReesAlgebra, TangentCone

i1 : 