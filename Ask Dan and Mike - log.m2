
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

i60 : 