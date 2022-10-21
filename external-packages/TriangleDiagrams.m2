-- DONE Better method of constructing one by hand.
-- DONE: Function to take a TriangleDiagram, and return a CohomologyTally.

-- TODO: (in another package, TODO: which one is it) generic extremal curve, generic subextremal curve, generic lex component curve.
-- we have this somewhere, just need to find it.

-- TODO: check whether a TriangleDiagram is Borel fixed.

-- TODO: (harder) enumerate tentative TriangleDiagrams with certain properties (e.g. given d,g)

-- TODO: do some testing too

-- TODO: hasSharedColumns D

-- TODO: acm D: saturate D written DONE
-- TODO: lambdaInvariants
-- TODO: isCompatible(Module, TriangleDiagram) => Boolean
-- TODO: triangleDiagram Module.

-- TODO: constructions: given M annihilated by x and y, produce a curve.
--   minimal curve, then bilink.
--   Rich's construction produces sparser results: proop 4.1.3 in Rich's thesis.

-- TODO: examples
--   examples of all ideals of degree 2, 3, 4, (d=5, g=0)
--
-- *** MES TODO: given a finite length module M, find
-- the lowest twist of M s.t. Tor_1(M, S/(z,w)) embeds into k[x,y]/J, for some homog ideal J.
-- From that, a short hop to figure out how to construct the curve!

newPackage(
        "TriangleDiagrams",
        Version => "0.2", 
        Date => "6 Dec 2019",
        Authors => {
            {Name => "Kristine Jones", 
                Email => "", 
                HomePage => ""},
            {Name => "Rich Liebling", 
                Email => "", 
                HomePage => ""},
            {Name => "Michael Stillman", 
                Email => "", 
                HomePage => ""}
            },
        Headline => "triangle diagrams of LCM space curves",
        PackageImports => {
            "Elimination",
            "MinimalPrimes"
            },
        PackageExports => {
            "BGG", -- for cohomologyTable
            "BoijSoederberg" -- for CohomologyTally
            },
        DebuggingMode => true
        )

export {
    "TriangleDiagram",
    "Triangle",

    "checkGeneric",
    "triangle",
    "lowerMonomials",
    "upperMonomials",
    "triangleDiagram",
    "isACM",
    "isWeaklyBorel",
    "lambdaInvariants",

    -- generation
    "lowerTriangleDiagrams",
    "possibleDiagrams",

    -- cohomology dim
    "h1FromDiagram",
    "h1Extremal",
    "h1Subextremal",
            
    -- display needs cleaning up still
    "tridiag",
    "PrintZeros",

    "circle",
    "tikz",
    "tikzpic",
    "wrapLatex",
    "displayTriangles",
    "displayDiagram",
    "latex",
    
    -- groebnerDegeneration
    "groebnerDegeneration",

    -- Helper for constructing the free resolution of H^1_*(IC) over k[z,w]
    "smithNF",
        
    -- Floystad construction
    "initialForms",
    "initialModule",
    "floystadTriangleDiagram",
    
    -- Triangle diagram from M
    "Lower",
    "Upper"
    
    
    }

protect FineGraded
protect InitialFormMap

-- also defined here are the methods:
-- genus, degree, saturate, isBorel, isWellDefined, cohomologyTable

triangleDiagram = method()

upperTriangle = method()

Triangle = new Type of List
TriangleDiagram = new Type of List

isWellDefined TriangleDiagram := (D) -> (
    result1 := isWellDefined D#0;
    result2 := isWellDefined D#1;
    result3 :=  (
        -- check that they mesh together
        result := true;
        ncommonrows := min(#D#0, #D#1);
        for d from 1 to ncommonrows-1 do (
            for j from 0 to d do (
                test := (D#0#d#j == infinity and D#1#d#j != infinity)
                  or (D#0#d#j != infinity and D#1#d#j == infinity);
                if not test then (
                    result = false;
                    if debugLevel > 0 then
                      << "triangle upper and lower do not mesh at position (i,j) = " 
                      << (d-j,j) << " (exactly one must be infinity)" << endl;
                    )
                )
            );
        -- now make sure that no more infinities exist in the lower diagram
        for d from ncommonrows to #D#0-1 do (
            test := any(D#0#d, x -> x == infinity);
            if test then (
                result = false;
                if debugLevel > 0 then
                    << "triangle lower diagram: no element in row " 
                    << d << " can be infinity" << endl;
                )
            );
        result
        );
    result1 and result2 and result3
    )

isWellDefined Triangle := (T) -> (
    -- check: number of elements in T matches a triangle
    --   #(row i) == i+1
    result := true;
    for d from 0 to #T-1 do (
        if #T#d != d+1 then (
            if debugLevel > 0 then 
              << "triangle: row " 
                << d << " which should have " 
                << d+1 << " elements, but has " 
                << #T#d << endl;
            result = false;
            )
        );
    -- check: last row is all zeros (if (0,0) entry is infinity)
    --   or all infinities (if (0,0) is 0)
    --   AND no earlier row has this property
    endvalue := if T#0#0 == infinity then 0 else infinity;
    for d from 0 to #T-2 do (
        if all(T#d, a -> a == endvalue)
        then (
            if debugLevel > 0 then 
              << "triangle should be done at row " << d << endl;
            result = false;
            );
        );
    if not all(T#(#T-1), x -> x == endvalue)
    then (
        if debugLevel > 0 then
          << "the elements in the last row of triangle should all be " << endvalue << endl;
        result = false;
        );
    -- TODO also check ideal property: for all (i,j)
    --  T(i,j) >= T(i-1,j), T(i,j-1) (or opposite for upper triangle).
    -- perhaps check: all entries are 0, positive integers, infinity.
    result
    )

checkGeneric = method()
checkGeneric List := (exponentVectorList) -> (
    -- This version is meant to be an internal function.
    -- check: R_0^r is in I, R_1^s is in I, R_3 never occurs., R_2^N never occurs.
    r := position(exponentVectorList, e -> e#1 == 0 and e#2 == 0);
    s := position(exponentVectorList, e -> e#0 == 0 and e#2 == 0);
    t := position(exponentVectorList, e -> e#0 == 0 and e#1 == 0);
    w := position(exponentVectorList, e -> e#3 != 0);
    if r === null then error "expected a power of first variable in ideal";
    if s === null then error "expected a power of second variable in ideal";
    if t =!= null then error "expected no power of third variable in ideal";
    if w =!= null then error "expected last variable to not appear in any generator";
    )
checkGeneric MonomialIdeal := (I) -> (
    R := ring I;
    if numgens R =!= 4 then error "expected a ring with 4 variables";
    exps := (flatten entries gens I)/exponents/first;
    checkGeneric exps
    )
checkGeneric Ideal := (I) -> (
    R := ring I;
    if numgens R =!= 4 then error "expected a ring with 4 variables";
    if dim(I + ideal(R_2, R_3)) > 0 then 
        error "ideal does not miss line defined by the last two variables";
    checkGeneric monomialIdeal leadTerm I
    )

triangle = method()
triangle MonomialIdeal := Triangle => (I) -> (
    -- translate an ideal which is "generic" (has x^r, y^s, some r, s, no z^power, 
    --    and the last variable doesn't even appear)
    -- to a (lower triangle).
    R := ring I;
    exps := (flatten entries gens I)/exponents/first;
    checkGeneric exps;
    E := hashTable for e in exps list (e#0,e#1) => e#2;
    T := new MutableHashTable;
    T#(0,0) = infinity;
    zvalue := (i,j) -> (
        T#(i,j) = if E#?(i,j) then 
                  E#(i,j) 
              else
                  min(if i > 0 then T#(i-1,j) else infinity, 
                      if j > 0 then T#(i,j-1) else infinity)
        );
    r := (keys E)/first//max;
    s := (keys E)/last//max;
    L := for d from 0 to r+s-1 list (
        if d == 0 then 
            {T#(0,0)}
        else if all(d, j -> T#(j,d-1-j) == 0) then break
        else 
            for j from 0 to d list zvalue(d-j,j)
        );
    new Triangle from L
    )

lowerMonomials = method()
lowerMonomials(Triangle, Ring) := List => (lower, S) -> (
    flatten for d from 1 to #lower - 1 list (
        for j from 0 to d list (
            zv := lower#d#j;
            if j == d and zv == lower#(d-1)#(j-1) then continue;
            if j == 0 and zv == lower#(d-1)#j then continue;
            if j =!= 0 and j != d and zv == min(lower#(d-1)#(j-1), lower#(d-1)#j) then continue;
            if zv == infinity then continue;
            S_{d-j,j,zv,0}
            )
        )
    )
lowerMonomials(TriangleDiagram, Ring) := List => (D,S) -> lowerMonomials(D#0, S)

upperMonomials = method()
upperMonomials(TriangleDiagram, Ring) := List => (D,S) -> (
    U := D#1;
    flatten for d from 0 to #U-1 list (
        for j from 0 to #U#d-1 list
          if U#d#j =!= infinity and U#d#j =!= 0 then S_{d-j,j,U#d#j,0} else continue
        )
    )

TEST ///
-*
  restart
*-
  debug needsPackage "TriangleDiagrams"
  R = ZZ/32003[x,y,z,w]
  I = monomialIdeal"x2x2, x4, y4, xyz3, x3y3"
  assert(triangle I == new Triangle from {
      {infinity}, 
      {infinity, infinity}, 
      {infinity, 3, infinity}, 
      {infinity, 3, 3, infinity}, 
      {0, 3, 3, 3, 0}, 
      {0, 0, 3, 3, 0, 0}, 
      {0, 0, 0, 0, 0, 0, 0}
      })
  T = triangle I
  debugLevel = 1
  isWellDefined T
  assert(set lowerMonomials(T, R) === set I_*)
  assert(monomialIdeal lowerMonomials (T, R) == I)

  I = monomialIdeal"x2x2, x4, y4, xyz3, x3y3w"
  assert try (triangle I; false) else true

  I = monomialIdeal"x2x2, x4, y4, z7, xyz3, x3y3w"
  assert try (triangle I; false) else true

  I = monomialIdeal"x2x2, x4, xyz3, x3y3"
  assert try (triangle I; false) else true
///

findCI = (I) -> (
    R := ring I;
    gbI := flatten entries gens gb I;
    F := select (1, gbI, f -> support leadTerm f === {R_0});
    G := select (1, gbI, f -> support leadTerm f === {R_1});
    if #F == 0 or #G == 0 then 
        error "the ideal does not miss the line defined by the last two variables";
    ideal(F#0,G#0)
    )

linkedTriangle = method()
linkedTriangle Ideal := (IC) -> linkedTriangle(IC, findCI IC)
linkedTriangle(Ideal, Ideal) := (IC, IX) -> (
    ID := IX : IC;
    inID := ideal leadTerm ID;
    triangle monomialIdeal inID
    )

upperTriangle(Triangle, ZZ, ZZ) := (T, r, s) -> (
    -- find last top row which is all infinities
    entry := (i,j) -> (
        if i < 0 or j < 0 then error "internal error: indices out of range";
        d := i+j;
        if T#?d then T#d#j else 0
        );
    toprow := max positions(T, row -> all(row, x -> x == infinity));
    U := for d from 0 to r+s-2-toprow list (
        for j from 0 to d list (
            i := d-j;
            if r-1-i < 0 or s-1-j < 0 then infinity else entry(r-1-i, s-1-j)
            ));
    new Triangle from U
    )

triangleDiagram Ideal := TriangleDiagram => (I) -> (
    IX := findCI I;
    (r,s) := (first degree IX_0, first degree IX_1);
    lower := triangle monomialIdeal leadTerm I;
    upper := linkedTriangle(I, IX);
    D := new TriangleDiagram from {lower, upperTriangle(upper, r, s)};
    --assert isWellDefined D;
    D
    )

TEST ///
-*
  restart
*-
  needsPackage "LCMSpaceCurves"
  debug needsPackage "TriangleDiagrams"
  R = ZZ/32003[x,y,z,w]
  I = extremalCurve(5, -3, R)
  triangle monomialIdeal leadTerm I
  assert isWellDefined oo
  linkedTriangle I
  assert isWellDefined oo
  
  needsPackage "SpaceCurves"
  elapsedTime I = minimalSpaceCurveIdeal coker matrix"x2,xy,y2,w2,z2"
  elapsedTime I' = minimalCurve coker matrix"x2,xy,y2,w2,z2"
  assert(degree I == degree I')
  assert(genus I == genus I')

  triangle monomialIdeal leadTerm I
  T = linkedTriangle I  
  D = triangleDiagram I
  assert isWellDefined T
  assert isWellDefined D
  T1 = new Triangle from {
      {infinity}, 
      {infinity, infinity}, 
      {infinity, infinity, infinity}, 
      {2, 2, infinity, infinity}, 
      {0, 0, 2, infinity, 0}, 
      {0, 0, 0, 0, 0, 0}
      }
  assert(T1 == T)
  assert(upperMonomials(D, R) == {x*y*z^2, x*y^2*z^2, y^3*z^2})
  assert not isACM D
  assert isACM saturate D
  acmI = monomialIdeal lowerMonomials(saturate D, R)
  assert(genus acmI == 6)
  assert(genus saturate D == genus acmI)
///

-- This version is an internal function for triangleDiagram
-- and is in old form (but seems correct) REWRITE.
upperTriangle(List, Triangle) := (upper, lower) -> (
    upper = upper/exponents/first;
    d1 := hashTable for u in upper list (u#0, u#1) => u#2;
    isDone := false;
    e := 0; -- degree, i.e. the row we are on
    result := {};
    while not isDone do (
        row := for j from 0 to e list (
            i := e-j;
            if lower#(i+j)#j != infinity then infinity
            else if d1#?(i,j) then d1#(i,j) else 0
            );
        isDone = all(row, a -> a == infinity);
        result = append (result,row);
        e = e+1;
        );
    new Triangle from result
    )

triangleDiagram(List, List) := TriangleDiagram => (lower, upper) -> (
    if #lower == 0 then error "expected monomials for the lower diagram";
    R := ring lower#0;
    if numgens R != 4 then error "expected a polynomial ring in 4 variables";
    if not all(lower, f -> instance(f, RingElement) and ring f === R and size f == 1)
       or not all(upper, f -> instance(f, RingElement) and ring f === R and size f == 1)
       then error "expected lists of monomials in the same ring";
    if radical monomialIdeal lower != monomialIdeal(R_0, R_1) then 
      error "expected the lower ideal to be supported on the first two variables";
    L := triangle monomialIdeal lower;
    D := new TriangleDiagram from {L, upperTriangle(upper, L)};
    if not isWellDefined D then << "warning: this triangle diagram is not well formed" << endl;
    D
    )

TEST ///
-*
  restart
  needsPackage "TriangleDiagrams"
*-  
  S = ZZ/32003[x,y,z,w]
  D = triangleDiagram({x^2, x*y, y^3*z, y^5}, {x*z, y*z})

  D = triangleDiagram({x^2*z^2, x^3, x^2*y, x*y^2, y^3}, {x*y*z, y^2*z})
  assert(toList(D_0) == {{infinity}, {infinity, infinity}, {2, infinity, infinity}, {0, 0, 0, 0}})
  assert(toList(D_1) == {{0}, {0, 0}, {infinity, 1, 1}, {infinity, infinity, infinity, infinity}})  
///

net Triangle := (T) -> (
    spaces := (n) -> concatenate(n : " ");
    nspaces := -1;
    S := reverse for t in reverse T list (
        nspaces = nspaces + 1;
        spaces nspaces | concatenate for a in t list(
            if a === infinity then ". "
            else (toString a) |" " 
            )
        );
    fold (S, (a,b) -> a || b)
    )

net TriangleDiagram := (D) -> (
     netList {toList D}
     )

degree Triangle := (T) -> (tally flatten T)#infinity -- number of infinities...

genus Triangle := (T) -> (
    g := 0;
    for d from 1 to #T - 1 do (
        for a in T#d do (
            if a == infinity then g = g - 1 + d
            else if a > 0 then g = g - a;
            )
        );
    g
    )

degree TriangleDiagram := D -> degree first D

genus TriangleDiagram := D -> genus first D

isACM = method()
isACM Triangle := Boolean => T ->  all(flatten T, a -> a == infinity or a == 0)
isACM TriangleDiagram := Boolean => D ->  isACM D#0 and isACM D#1

isBorel Triangle := Boolean => T -> (
    -- is the lower diagram T Borel fixed?
    -- need weakly increasing along a row.
    -- need strict increase along an x-column (unless both are infinity or zero).
    result := true;
    for d from 1 to #T - 1 do (
        for j from 1 to #T#d-1 do if T#d#j < T#d#(j-1) then result = false;
        for j from 1 to #T#d-1 do (
            a := T#d#j;
            b := T#(d-1)#(j-1);
            if a == infinity and b == infinity then continue;
            if a == 0 and b == 0 then continue;
            if a >= b then result = false;
            )
        );
    result
    )

isWeaklyBorel = method()
isWeaklyBorel TriangleDiagram := Boolean => D -> (
    if not isBorel D#0 then return false;
    result := true;
    U := D#1;
    for d from 0 to #U -2 do (
        for j from 0 to #U#d-1 do (
            a := U#d#j;
            b := U#(d+1)#(j+1);
            c := U#(d+1)#j;
            if a != 0 and a != infinity then (
                if a >= b then result = false;
                if a >= c then result = false;
                );
            );
        );
    result
    )

isBorel TriangleDiagram := Boolean => D -> (
    if not isWeaklyBorel D then return false;
    result := true;
    U := D#1;
    for d from 1 to #U - 1 do (
        for j from 1 to #U#d-1 do if U#d#j > U#d#(j-1) then result = false;
        );
    result
    )

cleanTriangle = (T) -> (
    -- remove all unneeded rows
    endvalue := if T#0#0 == infinity then 0 else infinity;
    toprow := position(T, row -> all(row, x -> x == endvalue));
    if toprow === null then error ("expected a triangle which ends with a row of " | endvalue);
    new Triangle from take(T, toprow+1)
    )

saturate Triangle := Triangle => opts -> T -> (
    cleanTriangle new Triangle from for d from 0 to #T-1 list 
      for a in T#d list if a > 0 and a != infinity then 0 else a
    )

saturate TriangleDiagram := TriangleDiagram => opts -> D -> (
    new TriangleDiagram from {saturate D#0, saturate D#1}
    )

lambdaInvariants = method()
lambdaInvariants Triangle := (T) -> (
    reverse for d from 0 to #T-1 list (
        if T#d#0 != infinity then continue;
        j := 0;
        while T#(d+j)#j == infinity do j = j+1;
        j
        )
    )
lambdaInvariants TriangleDiagram := (D) -> lambdaInvariants D#0

-------------------------------------------
-- CohomologyTally of a triangle diagram --
-- remember: this is in P^3 ---------------
-------------------------------------------
h1FromDiagram = method()
h1FromDiagram(TriangleDiagram, ZZ, ZZ) := List => (D, lo, hi) -> (
    -- returns a list of pairs: {deg, dim H^1(I(deg))}
    -- the default is to consider lo..hi for
    d0 := toList D#0;
    d1 := toList D#1;
    h1Top := hashTable flatten for i from 0 to #d1-1 list for j from 0 to #d1#i - 1 list if d1#i#j === infinity or d1#i#j === 0 then continue else (i-j,j) => d1#i#j;
    h1Bottom := hashTable flatten for i from 0 to #d0-1 list for j from 0 to #d0#i - 1 list if d0#i#j === infinity or d0#i#j === 0 then continue else (i-j,j) => d0#i#j;
    dim1 := (n) -> (
        topdim := sum(pairs h1Top, (k,v) -> min(v, max(n + 1 + v - plus k, 0)));
        bottomdim := sum(pairs h1Bottom, (k,v) -> min(v, max(n + 1 - plus k, 0)));
        topdim - bottomdim
        );
    for i from lo to hi list {i, dim1 i}
    )

h1FromDiagram TriangleDiagram := List => (D) -> (
    g := genus D;
    d := degree D;
    lo := g - binomial(d-2,2) + 1;
    hi := binomial(d-1,2) - g - 1;
    h1FromDiagram(D, lo, hi)
    )

hh(ZZ, TriangleDiagram) := (i,D) -> (
    if i == 1 then 
        h1FromDiagram D 
    else 
        error "only implemented for hh^1"
    )

h1Extremal = method()
h1Extremal(ZZ, ZZ) := (d,g) -> (
    -- returns a list of pairs as in h1FromDiagram, but for the extremal curve with
    -- degree d and genus g.
    a := binomial(d-2,2) - g;
    b := binomial(d-1,2) - g;
    if a <= 0 then error "there is no extremal curve if g >= binomial(d-2,2)";
    p1 := for n from -a+1 to -1 list {n, a+n};
    p2 := for n from 0 to d-2 list {n, a};
    p3 := for n from d-1 to b-1 list {n, b-n};
    flatten{p1,p2,p3}
    )

h1Subextremal = method()
h1Subextremal(ZZ, ZZ) := (d,g) -> (
    -- returns a list of pairs as in h1FromDiagram, but for the subextremal curve with
    -- degree d and genus g.
    -- require: d >= 4, g <= binomial(d-3,2) (otherwise a subextremal curve doesn't exist)
    a := binomial(d-3,2) - g;
    b := binomial(d-2,2) - g;
    c := binomial(d-1,2) - g;
    if d < 4 or a < 0 then error "there is no subextremal curve if d < 4 or g > binomial(d-3,2)";
    p0 := for n from -b+1 to -a list {n,0};
    p1 := for n from -a+1 to 0 list {n, a+n};
    p2 := for n from 1 to d-3 list {n, a+1};
    p3 := for n from d-2 to b list {n, b-n+1};
    p4 := for n from b+1 to c-1 list {n,0};
    flatten{p0,p1,p2,p3,p4}
    )

cohomologyTable(TriangleDiagram, ZZ, ZZ) := (D, lo, hi) -> (
    d0 := toList D#0;
    d1 := toList D#1;
    Atable := tally flatten for i from 0 to #d1-1 list for j from 0 to #d1#i - 1 list if d1#i#j === infinity then continue else i-d1#i#j;
    Btable := tally flatten for i from 0 to #d0-1 list for j from 0 to #d0#i - 1 list if d0#i#j === infinity then continue else i+d0#i#j;
    h1Top := hashTable flatten for i from 0 to #d1-1 list for j from 0 to #d1#i - 1 list if d1#i#j === infinity or d1#i#j === 0 then continue else (i-j,j) => d1#i#j;
    h1Bottom := hashTable flatten for i from 0 to #d0-1 list for j from 0 to #d0#i - 1 list if d0#i#j === infinity or d0#i#j === 0 then continue else (i-j,j) => d0#i#j;
    A := (n) -> if Atable#?n then Atable#n else 0;
    B := (n) -> (
        num := if n >= #d0 then n+1 else 0;
        if Btable#?n then Btable#n + num else num
        );
    dim0 := (n) -> sum for k from 0 to n list ((n-k+1) * B k);
    dim2 := (n) -> sum for k in keys Atable list (
        if k >= n+2 and Atable#?k 
        then (k-n-1) * Atable#k 
        else 0
        );
    dim1 := (n) -> (
        topdim := sum(pairs h1Top, (k,v) -> min(v, max(n + 1 + v - plus k, 0)));
        bottomdim := sum(pairs h1Bottom, (k,v) -> min(v, max(n + 1 - plus k, 0)));
        topdim - bottomdim
        );
    cohom0 := for n from lo to hi list (
        ndim := dim0 n;
        if ndim === 0 then continue
        else 
            (0,n) => ndim
        );
    cohom1 := for n from lo to hi list (
        ndim := dim1 (n-1);
        if ndim === 0 then continue
        else
            (1, n-1) => ndim
        );
    cohom2 := for n from lo to hi list (
        ndim := dim2 (n-2);
        if ndim === 0 then continue
        else
            (2, n-2) => ndim
        );
    cohom3 := for n from lo to hi list (
        if n >= 0 then continue 
        else
            (3, n-3) => binomial(2-n, 3)
        );
    new CohomologyTally from join(cohom0, cohom1, cohom2, cohom3)
    )

TEST ///
 -- test of isBorel, isWeaklyBorel
-*
  restart
  needsPackage "TriangleDiagrams"
*-
  S = ZZ/32003[x,y,z,w]
  D = triangleDiagram({x^3*z, x^2*y, x*y*z, x^4, y^4}, {x^2*z^2})
  assert not isBorel D#0
  assert not isBorel D
  assert not isWeaklyBorel D

  L = flatten entries gens borel monomialIdeal(x^3*z, x^4, y^5)
  T = triangle monomialIdeal L
  isBorel T
  D = triangleDiagram(L, {x^2*z})
  assert isBorel D#0
  assert not isBorel D
  assert not isWeaklyBorel D
  assert isBorel monomialIdeal lowerMonomials(D, S)
///
    
TEST ///
-*
  restart
  needsPackage "TriangleDiagrams"
*-
  needsPackage "LCMSpaceCurves"
  needsPackage "SpaceCurves"

  S = ZZ/32003[x,y,z,w]
  I = extremalCurve(5, 0, S)
  M = HH^1((sheaf module I)(>=0))
  M
  for i from -4 to 10 list hilbertFunction(i, M)
  D = triangleDiagram I
  isBorel D#0
  isWeaklyBorel D
  isBorel D

  assert isWellDefined D
  assert(degree D == degree I)
  assert(genus D == genus I)
  C1 = cohomologyTable(D, -3, 9)
  C2 = cohomologyTable(sheaf module I, -3, 5)
  assert(C1 == C2)

  M = coker matrix {{x,y,z^2,w^3}} ++ coker matrix{{x,y,z,w^4}}
  elapsedTime I = minimalSpaceCurveIdeal M -- takes a while...
  elapsedTime I1 = minimalCurve M -- takes a while...
  assert(degree I == degree I1)
  assert(genus I == genus I1)
  assert(minimalBetti I == minimalBetti I1)
  assert(triangleDiagram I == triangleDiagram I1)

  E = triangleDiagram I1
  degree I1 == degree E
  genus I1 == genus E

  --displayDiagram E
  C1 = cohomologyTable(E, -5, 9)
  C2 = cohomologyTable(sheaf module I, -5, 5)
  assert(C1 == C2)
///

TEST ///
-*
  restart
  needsPackage "TriangleDiagrams"
*-
  needsPackage "LCMSpaceCurves"
  R = ZZ/32003[x,y,z,w]
  I = extremalCurve(5,0,R)
  Is = subextremalCurve(5,0,R)
  D = triangleDiagram I
  Ds = triangleDiagram Is
  hh^1 D
  assert(matrix h1FromDiagram D == matrix h1Extremal(5,0))
  assert(matrix h1FromDiagram Ds == matrix h1Subextremal(5,0))

  -- need g < binomial(d-2,2) in order for extremal curves to exist.  
  checkextremal = (d,g) -> (
      I := extremalCurve(d, g, R);
      D := triangleDiagram I;
      --print matrix h1FromDiagram D;
      assert(matrix h1FromDiagram D == matrix h1Extremal(d,g));
      )
  for g from -5 to -1 do checkextremal(2,g)
  for g from -5 to -1 do checkextremal(3,g)
  for g from -5 to 0 do checkextremal(4,g)
  for g from -5 to 2 do checkextremal(5,g)
  for g from -5 to 5 do checkextremal(6,g)
  for g from -5 to 9 do checkextremal(7,g)

  -- need d > 4, g <= binomial(d-3,2) in order for subextremal curves to exist.  
  checksubextremal = (d,g) -> (
      I := subextremalCurve(d, g, R);
      D := triangleDiagram I;
      --print matrix h1FromDiagram D;
      assert(matrix h1FromDiagram D == matrix h1Subextremal(d,g));
      )

  matrix h1Extremal(4,0)  
  matrix h1Subextremal(4,0)  
  for g from -5 to 0 do checksubextremal(4,g)
  for g from -5 to 1 do checksubextremal(5,g)
  for g from -5 to 3 do checksubextremal(6,g)
  for g from -5 to 6 do checksubextremal(7,g)
///
-----------------------------------------------------
-- generation of upper and lower triangle diagrams --
-----------------------------------------------------
replaceElt = (L, i, e) -> (
  take(L, i) | {e} | drop(L, i+1)
)

findFirstPositionOnRow = (upper, row) -> (
  (row, position(upper#(row), v -> v != infinity))
)

sumEntries = (LTri) -> (
  fold(LTri, 0, (r,acc)-> fold(r, acc, (t, acc2) -> acc2 + (if t == infinity then 0 else t)))
)

trimExtraRows = upper -> (
  trimmed := {};
  for r in upper do (
    trimmed = append(trimmed, r) ;
    if all(r, t->t==infinity) then
      break
  ) ;
--  print trimmed ;
  trimmed
)

possibleDiagrams = method()
possibleDiagrams Triangle := List => (LTri) -> (
  upperTriangles(LTri)/(ut->new TriangleDiagram from (LTri, ut))
)

upperTriangles = LTri -> (
  upper := for r in LTri list (
    for t in r list (
      if t === infinity then 0 else infinity
    )
  );
  upper = trimExtraRows(upper) ;
--  << "ltri: " << LTri << endl ;
  numLeftToFill := sumEntries(LTri) ;
  startingRow := #upper - 1 - position(reverse(upper), r->any(r, t->t!=infinity)) ;
--  << "after startingRow: " << startingRow << endl ;
  startingPosition := findFirstPositionOnRow(upper, startingRow) ;
--  << "startingPosition: " << startingPosition << endl ;
  result := fillInUpperDiagram(numLeftToFill, LTri, startingPosition, upper) ;
  result / (l->new Triangle from l)
)

checkDiagram = (diagram, ltri) -> (
  D := new TriangleDiagram from { ltri, new Triangle from diagram } ;
  if false == isWellDefined( D) then return false ;

  -- shamelessly copied from isWeaklyBorel in TriangleDiagrams.m2
  -- TODO: refactor to avoid the copy&paste
    U := diagram;
    for d from 0 to #U -2 do (
        for j from 0 to #U#d-1 do (
            a := U#d#j;
            b := U#(d+1)#(j+1);
            c := U#(d+1)#j;
            if a != 0 and a != infinity then (
                if a >= b then return false ;
                if a >= c then return false;
                );
            );
        );

  maxDeg := max(#diagram-1, #ltri - 1) ;
  runningSumUpper := reverse accumulate(reverse(toList U),0,(r, acc)->fold(r, acc, (t,acc2)->acc2+if t!=infinity then t else 0)) ;
  runningSumLower := reverse accumulate(reverse(toList ltri),0,(r, acc)->fold(r, acc, (t,acc2)->acc2+if t!=infinity then t else 0)) ;

  if #runningSumUpper < #runningSumLower then (
    repeatThis := last(runningSumUpper) ;
    runningSumUpper = runningSumUpper | toList((#runningSumLower-#runningSumUpper):repeatThis)
  ) ;

  test := any(runningSumUpper - runningSumLower, i->i<0) ;
  not test
)

-- lTri is the lower triangle diagram for use in testing compatibility
-- numLeftToFill is the sum of the value left to be filled into the upper diagram
-- nextPosition is {d,j} where d is the row number (degree) and j is the position from left to right (0-based)
-- diagram is the diagram so far completed, with 0s as default

fillInUpperDiagram = (numLeftToFill, ltri, nextPosition, diagram) -> (
  if nextPosition#0 == 0 then
    return {} ; -- only 0 allowed at apex

  result := {};
  changingRow := diagram#(nextPosition#0);
--  << "changingRow is " << changingRow << endl;
--  << "numLeftToFill is " << numLeftToFill << endl;
  -- maxValueToFill applies only if restricting to BorelFixed upper diagrams
  maxValueToFill := min(numLeftToFill, if nextPosition#1>0 then changingRow#(nextPosition#1 - 1) else infinity) ;
  for a in reverse(0..maxValueToFill) do (
--    << "a is " << a << endl ;
    newRow := replaceElt(changingRow, nextPosition#1, a);
    newDiagram := replaceElt(diagram, nextPosition#0, newRow);
--    << "newRow is " << newRow << endl ;
--    << "newDiagram is " << newDiagram << endl ;
    if numLeftToFill == a then (
      if checkDiagram(newDiagram, ltri) then (
        result = append(result, newDiagram);
      );
      continue;
    );

--    << "find new position nextPosition currently " << nextPosition << " parts " << nextPosition#0 << ", " << nextPosition#1 << endl ;
    newNextPosition := if nextPosition#1 < nextPosition#0 then
                        (nextPosition#0, nextPosition#1 + 1)
                      else if nextPosition#0 > 0 then
                        (nextPosition#0 - 1, position(diagram#(nextPosition#0 - 1), v -> v != infinity))
                      else
                        continue;
--    << "new position=" << newNextPosition << endl ;
    more := fillInUpperDiagram(numLeftToFill-a, ltri, newNextPosition, newDiagram) ;
    result = result | more
  );
  result
)

-------------------------------------------
-- generation of lower triangle diagrams --
-------------------------------------------
lowerTriangleFromLambda = (lambda) -> (
  l := for d from 0 to max(lambda) + 4 list (
    -- (d+1-j) is the min length lambda must have to cover the j-th column of row of deg d
    -- revlambda starts with the 0th element describing the length of the column where d=j
    -- that is, revlambda#i is the column in the diagram representing x^i
    -- so revlambda(d-j) + (d-j) is the max degree of the upper triangle in y-column (d-j) from the right
    revlambda := reverse lambda ;
    for j from 0 to d list (
      if #lambda >= d+1-j and revlambda#(d-j) + (d-j) > d then infinity else 0
    )
  ) ;
  new Triangle from l
)

fillInLowerDiagram = (numLeftToFill, diagram, nextPosition) -> (
  if numLeftToFill == 0 then return {diagram};
  result := {};
  changingRow := diagram#(nextPosition#0);
  -- << "changingRow is " << changingRow << endl;
  -- maxValueToFill applies only if restricting to BorelFixed upper diagrams
  maxValueToFill := min(numLeftToFill, 
      if nextPosition#1 < nextPosition#0 
      then changingRow#(nextPosition#1 + 1) 
      else infinity
      ) ;
  -- << "numLeftToFill is " << numLeftToFill << " maxValueToFill=" << maxValueToFill << endl;
  for a in reverse(0..maxValueToFill) do (
    newRow := replaceElt(changingRow, nextPosition#1, a);
    if not any(newRow, i -> i!=0) then continue ;

    newDiagram := replaceElt(diagram, nextPosition#0, newRow);
    -- << "newRow is " << newRow << endl ;
    -- << "newDiagram is " << newDiagram << endl ;
    if numLeftToFill == a then (
      if checkLowerDiagram newDiagram then (
        -- << "adding newDiagram " << newDiagram << endl ;
        result = append(result, newDiagram);
      );
      continue;
    );

   -- << "find new position nextPosition currently " << nextPosition << " parts " << nextPosition#0 << ", " << nextPosition#1 << endl ;
    newNextPosition := if nextPosition#1 > 0 then
                        (nextPosition#0, nextPosition#1 - 1)
                      else if nextPosition#0 < #diagram - 1 then (
                        p := position(diagram#(nextPosition#0 + 1), v -> v == infinity) ;
                        (nextPosition#0 + 1, if(p=!=null) then p - 1 else nextPosition#0 + 1)
                      ) else
                        continue;
    -- << "new position=" << newNextPosition << " numLeft=" << numLeftToFill-a << endl ;
    more := fillInLowerDiagram(numLeftToFill-a, newDiagram, newNextPosition) ;
    result = result | more
  );
  result
)

-- TODO: what type is this taking?
checkLowerDiagram = (diagram) -> (
  L := diagram ;
  for d from 0 to #L -2 do (
    for j from 0 to #L#d-1 do (
      a := L#d#j;
      b := L#(d+1)#(j+1);
      c := L#(d+1)#j;
      if a != infinity then (
        if a < b then return false ;
        if a < c then return false ;
        if a!=0 then (
          if a==b then return false ;
          if a==c then return false ;
        ) ;
      );
    );
  );
  true
)

checkIsValidLambdaInvariant = method()
checkIsValidLambdaInvariant(ZZ, List) := (deg, lambda) -> (
    -- check that lambda is a well-defined lambda invariant for an LCM curve of degree d.
    if deg != sum lambda then error("expected a list of increasing positive integers, summing to the degree"|deg);
    for a in lambda do (
        if not instance(a, ZZ) or a <= 0 then error("expected a list of increasing positive integers, summing to the degree"|deg);
        );
    for i from 0 to #lambda-2 do (
        if lambda#i >= lambda#(i+1) then error("expected a list of increasing positive integers, summing to the degree"|deg);
        );
    )

lowerTriangleDiagrams = method()
lowerTriangleDiagrams(ZZ, ZZ, List) := List => (d,g,lambda) -> (
  checkIsValidLambdaInvariant(d, lambda);
  
  lower := lowerTriangleFromLambda lambda ;
  assert( sum(lambda) == number(flatten lower, i -> i == infinity)) ;

  acmGenus := genus lower ;
  numLeftToFill := acmGenus - g ;

  startingRow := position(lower, r -> any(r, i -> i != infinity)) ;
  startingPosition := (startingRow, number(lower#startingRow, i -> i != infinity) - 1 ) ;
  -- << "starting pos = " << startingPosition << endl ;

  result := fillInLowerDiagram(numLeftToFill, lower, startingPosition) ;
  result / (l -> cleanTriangle new Triangle from l)
)


------------------------------------------------------------------
-- latex/tikz code to display upper and lower triangle diagrams --
------------------------------------------------------------------
-- tridiag -- TODO
tridiag = method(Options => {PrintZeros => false})
tridiag Triangle := opts -> (T) -> (
    prelude := "\\tridiag{\n";
    postlude := "\n}";
    t := #T;
    L := flatten for d from 0 to #T - 1 list (
	    line := for j from 0 to #T#d - 1 list (
            if T#d#j === infinity then (
                s1 := if j > 0 and T#d#(j-1) =!= infinity then "\\ " else "";
                s2 := if not opts.PrintZeros then "{{}}" else "0";
                s1 | s2
                )
            else (
                (if T#d#j === 0 and not opts.PrintZeros then "{{}}" else toString T#d#j)
                 )
            );
        concatenate between(" ",line)
        );
    L1 := concatenate between(" ;\n",L);
    prelude | L1 | postlude
    )    

-- \[
--   \tridiag{
--    . ;
--    {} . ;
--    {} 1\ 2
--   }
-- \]

tridiag TriangleDiagram := opts -> (D) -> (
    prelude := "\\tridiag{\n";
    postlude := "\n}";
    T := D#0;
    U := D#1;
    t := #T;
    L := flatten for d from 0 to #T - 1 list (
	    line := for j from 0 to #T#d - 1 list (
            if T#d#j === infinity then (
                s1 := if j > 0 and T#d#(j-1) =!= infinity then "\\ " else "";
                s2 := if U#d#j == 0 and not opts.PrintZeros then "{{}}" else toString U#d#j;
                s1 | s2
                )
            else (
                (if T#d#j === 0 and not opts.PrintZeros then "{{}}" else toString T#d#j)
                 )
            );
        concatenate between(" ",line)
        );
    L1 := concatenate between(" ;\n",L);
    prelude | L1 | postlude
    )    

str1 = /// \shade[ball color=$color] ($x,$y) circle($rpt) node {$label};///
str2 = /// \draw ($x,$y) circle($rpt) node {$label};///
circle = (x,y,r,color,label) -> (
    s := if color === "" then str2 else str1;
    s = replace("\\$x",toString x, s);
    s = replace("\\$y", toString y, s);
    s = replace("\\$r", toString r, s);
    s = replace("\\$color", color, s);
    replace("\\$label", label, s)
    )

prelude = ///
\documentclass{article}
\usepackage{tikz}
\begin{document}
///

postlude = ///
\end{document}
///

wrapLatex = method()
wrapLatex String := (s) -> concatenate(prelude, s, postlude)

tikz = method()
tikz Triangle := (T) -> (
     t := #T;
     L := flatten for i from 0 to #T - 1 list (
	  for j from 0 to #T#i - 1 list (
	       if T#i#j == infinity then circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "", "")
	       else if T#i#j > 0 then circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "yellow", toString(T#i#j))
	       else circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "yellow", "")
	  ));
     concatenate between("\n",L)
     --concatenate between("\n",join({prelude},L,{postlude}))
     )

tikz TriangleDiagram := (D) -> (
     T := D#0;
     U := D#1;
     t := #T;
     L := flatten for i from 0 to #T - 1 list (
	  for j from 0 to #T#i - 1 list (
	       if T#i#j == infinity then (
		    if U#i#j == 0 then 
			circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "", "")
		    else circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "", toString(U#i#j))
		    )
	       else if T#i#j > 0 then circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "yellow", toString(T#i#j))
	       else circle(.35 * (t-i) + .7 * j, .65 * (t-i), 10, "yellow", "")
	  ));
     concatenate between("\n",L)
     --concatenate between("\n",join({prelude},L,{postlude}))
     )



tikzpic1 = ///
\begin{tikzpicture}
///

tikzpic2 = ///
\end{tikzpicture}
///

tikzpic = method()
tikzpic Triangle := (T) -> concatenate(tikzpic1, tikz T, tikzpic2)

tikzpic TriangleDiagram := (D) -> concatenate(tikzpic1, tikz D, tikzpic2)

displayTriangles = (npack,L) -> (
     -- npack: how many to place on a line
     -- L is a list of ideals
     L = apply(L, x -> {{tikzpic triangle x},{latex x}});
     L1 := pack(npack, L);
     latex L1
     )

latex = method()

tabular1 = ///
\begin{tabular}{$head}
$body
\end{tabular}
///

latex String := (s) -> s


latex Ideal := (I) -> tex I -- replace("text", "mbox", tex I)

latex List := (L) -> (
     r := #L#0;
     hd := concatenate(r : "l");
     bod := concatenate for p in L list (
	  concatenate between(" & ", for q in p list latex q)
     	  |
	  /// \\ ///
	  );
     replace("\\$body", bod,
      replace("\\$head", hd, tabular1))
     )

displayDiagram = method()
displayDiagram TriangleDiagram := (D) -> (
    -- this writes to "foo.tex" by default
    fil := openOut "foo.tex";
    fil << wrapLatex tikzpic D << endl << close;
    run "pdflatex foo.tex";
    run "open foo.pdf"
    )

-----------------------------------------------
-- Code for Groebner degeneration.
-- Given: a list of lists of polynomials, all in the same ring,
--  such that each set of polynomials is a GB in that order.
--  (1) Find a weight vector which gives this order.
--  (2) Find the corresponding graded ring in one more variable
--  (3) Homogenize the equations with respect to this ring (and new variable).
-- also, consider using marked polynomials too...

findHeft1 = (degs) -> (
     A := transpose matrix degs;
     needsPackage "FourierMotzkin";
     B := ((value getGlobalSymbol "fourierMotzkin") A)#0;
     r := rank source B;
     f := (matrix{toList(r:-1)} * transpose B);
     if f == 0 then return;
     heft := first entries f;
     g := gcd heft;
     if g > 1 then heft = apply(heft, h -> h // g);
     minheft := min heft;
     if minheft <= 0 then heft = apply(heft, a -> a - minheft + 1);
     heftvals := apply(degs, d -> sum apply(d, heft, times));
     if not all(heftvals, d -> d > 0) then return null;
     (heft, heftvals)
     )

findWeightVector = method ()
findWeightVector(List) := (L) -> (
    -- input: a list of polynomials.
    -- output: a weight vector which matches the monomial order.
    if #L == 0 then error "expected at least one polynomial";
    R := ring L#0;
    if not all(L, f -> instance(f, RingElement) and ring f === R)
    then error "expected polynomials all in the same ring";
    D := flatten for f in L list (
        e := exponents f;
        for i from 1 to #e-1 list e#0 - e#i
        );
    ans := findHeft1 D;
    if ans === null then error "need to use a monomial order";
    first ans
    )

groebnerDegeneration = method()
groebnerDegeneration Ideal := (I) -> groebnerDegeneration(I, findWeightVector flatten entries gens gb I)
groebnerDegeneration(Ideal, List) := (I, wtvec) -> (
    if not all(wtvec, w -> instance(w, ZZ) and w > 0) then error "expected a list of positive integers";
    S := ring I;
    if #wtvec != numgens S then error ("expected a list of length " | (numgens S));
    G := flatten entries gens gb I;
    K := findCI I;
    ST := (coefficientRing S)[gens S, getSymbol "t", Degrees => append(wtvec, 1)];
    t := ST_(numgens S);
    IT := ideal homogenize(sub(gens gb I, ST), t);
    KT := ideal homogenize(sub(gens gb K, ST), t);
    JT := KT : IT;
    (IT, KT, JT)
    )

----------------------------
-- Floystad coonstruction --
----------------------------

-- Need a function which takes a matrix over a fine grading, and returns the matrix whose columns are multigraded lead terms (not nec monomial)
  regrade = method()
  regrade ChainComplex := (C) -> (
      -- assumption: C is a free resolution.
      R := ring C;
      F0 := C_0;
      chainComplex for i from 1 to length C list  (
          f := map(F0,,C.dd_i);
          F0 = source f;
          f
          )
      )

-- Multi-graded image module (i.e. columns of a matrix), with a fine-graded target module.
-- compute in(M).
-- notation: F = target M, twisted to be all non-negative
-- Order of events:
--  0. tensor M by the min degree, so that all degs are >= 0.
--  1. create a new ring S in n+r variables (n=numvars (R = ring M, r=numgens target M)
--     product order: grevlex on gens of R, then grevlex or whatever on the r variables
--     degrees: all degrees are in ZZ^(n+1), but perhaps degree of the y_i are e.g. (0,...,0,100).
--     heft: sum of all degrees.
--  2. create a vector d: S^1 <-- F corresponding to the degrees of F * y_i, i.e. x^(degree i th row) * y_i
--     multiply d*M.
--  3. compute a GB for this ideal, up to a certain degree (so that we don't get quadratics in y variables)
--  4. leadTerm(1, oo)
--  5. Now translate that back to a matrix whose target is F.

makeFineGradedRing = method()
makeFineGradedRing Module := (F) -> (
    -- assumptions: 
    --  (1) R = ring F is a fine graded polynomial ring with, say, n variables.
    --  (2) F is a free module of rank, say, r.
    -- We create a new polynomial ring and a one row matrix corresponding to the degrees of F.
    R := ring F;
    degs := degrees F;
    mindeg := degs//transpose/min;
    degs = degs/(d -> d - mindeg);
    e := local e;
    S := (coefficientRing R)[gens R, e_0..e_(#degs-1), 
        MonomialOrder => {numgens R, #degs},
        Degrees => splice {numgens R: 1, #degs: 100} --,
        ];
    phi := map(S,R,take(gens S, numgens R));
    matrix {for i from 0 to #degs-1 list (phi R_(degs#i)) * e_i}
    )

initialForms = method()
initialForms Matrix := (M) -> (
    F := target M;
    J := if F.cache.?InitialFormMap then F.cache.InitialFormMap else 
      F.cache.InitialFormMap = makeFineGradedRing F;
    S := ring J;
    L := ideal(J * (sub(M, S)));
    P := leadTerm(1, gens gb(L, DegreeLimit => 199));
    -- TODO: assert something to make sure this 100/199 hack is working.
    map(F,,sub(contract(transpose J, P), ring M))
    )

initialModule = method()
initialModule Ideal := (IC) -> (
    -- returns 3 (image) modules: B2, inK2, Z2.
    -- Step 1. Create the free resolution over IT.
    -- Step 2. Get F2^*, and then submodules of it: B2, Z2, and K2
    -- Step 3. inK2 = initialForms(gens inK2).
    -- return answer.
    S := ring IC;
    if not S.?FineGraded then 
        S.FineGraded = (coefficientRing S)[gens S, DegreeRank=>numgens S];
    Sf := S.FineGraded;
    (It, Kt, Jt) := groebnerDegeneration IC;
    St := ring It;
    C := res It;
    f0 := map(S, St, {S_0, S_1, S_2, S_3, 0});
    f1 := map(S, St, {S_0, S_1, S_2, S_3, 1});
    f2 := map(Sf, S);
    C0 := regrade f0 C;
    C1 := regrade f1 C;
    Cf := regrade f2 C0;
    F := dual Cf_2;
    Z2 := ker ((dual Cf).dd_-2);
    B2 := image ((dual Cf).dd_-1);
    K2 := image map(F,, sub(syz ((dual C1).dd_-2), Sf));
    D2 := image map(F,, sub(((dual C1).dd_-1), Sf)); -- not needed.
    inB2 := image initialForms (gens B2); -- not needed
    inZ2 := image initialForms (gens Z2); -- not needed
    inK2 := image initialForms (gens K2);
    inD2 := image initialForms (gens D2); -- not needed
    ----------------------------------------------
    -- now we do some checks, then return the answer.
    assert(ring B2 === Sf);
    assert(ring Z2 === Sf);
    assert(isHomogeneous B2);
    assert(isHomogeneous Z2);    
    assert(isHomogeneous inK2);
    assert(isHomogeneous inD2);
    assert(inB2 == B2);
    assert(inZ2 == Z2);
    assert(inD2 == B2);
    assert(isSubset(B2, inK2));
    assert(isSubset(inK2, Z2));
    -- The following is not needed for Floystad
    if false then (
        -- we want: regraded 
        ZT1 := f0 syz dual C.dd_3;
        ZT1 = map(F,,sub(ZT1,Sf));
        BT1 := f0 dual C.dd_2;
        BT1 = map(F,,sub(BT1,Sf));
        ET1 := ((ker dual C.dd_3)/(image dual C.dd_2)) ** St^1/St_4;
        return (B2, inK2, Z2, BT1, ZT1, ET1, C);
        );
    (B2, inK2, Z2)
    )

initialModule(Ideal, Thing) := (IC,notused) -> (
    -- returns 3 (image) modules: B2, inK2, Z2.
    -- Step 1. Create the free resolution over IT.
    -- Step 2. Get F2^*, and then submodules of it: B2, Z2, and K2
    -- Step 3. inK2 = initialForms(gens inK2).
    -- return answer.
    S := ring IC;
    if not S.?FineGraded then 
        S.FineGraded = (coefficientRing S)[gens S, DegreeRank=>numgens S];
    Sf := S.FineGraded;
    (It, Kt, Jt) := groebnerDegeneration IC;
    St := ring It;
    C := res It;
    f0 := map(S, St, {S_0, S_1, S_2, S_3, 0});
    f2 := map(Sf, S);
    C0 := regrade f0 C;
    Cf := regrade f2 C0;
    F := dual Cf_2;
    (map(F,,f2 f0 syz dual C.dd_3),
            map(F,,f2 f0 dual C.dd_2))
    )

floystadTriangleDiagram = method()
floystadTriangleDiagram Ideal := (I) -> (
    lower := triangle monomialIdeal leadTerm I;
    (B2, inK2, Z2) := initialModule I;
    degs := degrees prune(inK2/B2);
    topval := position(lower, x -> all(x, a -> instance(a, ZZ)));
    if topval === null then error "logic error on my part";
    findentry := (i,j) -> (
        -- NOTE: this can probably be simplified tremendously!
        possibles := for d in degs list if (-d#0 - 1 >= i and -d#1 - 1 >= j)
          then d#2 else continue;
        if #possibles === 0 then error "this should not happen";
        min possibles
        );
    upper := new Triangle from for d from 0 to topval list (
        for j from 0 to d list (
            if instance(lower#d#j, ZZ)
            then infinity
            else findentry(d-j,j)
            )
        );
    D := new TriangleDiagram from {lower, upper};
    assert isWellDefined D;
    D
    )

----------------------------------
-- Given a finite dimensional module M over S = k[x,y,z,w]
-- (a) compute the resolution of M over k[z,w].
--     this should be in the same form as the one for Rich's thesis.
-- (b) determine the corresponding triangle diagram
-- (c) if (x,y) M = 0, then construct a curve for this module (Rich's construction)

findQN = method()
findQN(Module, RingElement, RingMap) := (M, w, f) -> (
    -- returns presentation of ker w, coker w, in
    -- the ring `source f` which should have one variable.
    R := ring M;
    if R =!= target f then error "expected ring map to map to the ring of module";
    Q := prune(M ** coker w);
    N := prune Tor_1(M, coker w);
    (pushForward(f,N), pushForward(f,Q))
    )

smithNF = method()
smithNF Matrix := (m) -> (
    (D,P,Q) := smithNormalForm m;
    assert(D == P * m * Q);
    Q = map(source m,,Q);
    P = transpose  map(dual target m,,transpose P);
    D = map(target P, source Q, D);
    assert isHomogeneous Q;
    assert isHomogeneous P;
    assert isHomogeneous D;
    (D,P,Q)
    )

smithNF ChainComplex := (C) -> (
    -- suppose that C is a (graded) complex over R = kk[z,w]
    -- and that it has length 2.
    -- return a new complex, such tath when setting w=0,
    -- the resulting matrix C.dd_2 is in Smith normal form.
    CMR := C; -- TODO: correct?
    R := ring C;
    if numgens R != 2 then error "expected a polynomial ring in 2 variables";
    A := (coefficientRing R)[R_0];
    diffC := (map(A,R,{A_0,0})) C.dd_2;
    (D,P,Q) := smithNF diffC;
    P = sub(P, R);
    Q = sub(Q, R);
    d2 := P * CMR.dd_2 * Q;
    d1 := CMR.dd_1 * P^-1;
    chainComplex{d1,d2}
    )

twists = method()
twists Module := (M) -> (
    -- M is a graded module in one variable.
    -- return a list of {d_i, p_i},
    -- where the d_i are the degrees of the generators
    --  (and M is the direct sum of these generators (in the degrees d_i))
    --  and the p_i is the power of the variable annihilating this generator
    m := relations M;
    (D,P,Q) := smithNF m;
    degs := (degrees target D)/first;
    srcdegs := (degrees source D)/first;
    for i from 0 to #degs-1 list {degs#i, srcdegs#i-degs#i}
    )

-*
triangleDegrees = method()
triangleDegrees(Module, RingElement, RingMap) := (M, w, f) -> (
    (NA, QA) := findQN(M, w, f);
    lower := twists NA;
    upper := twists QA;
    upper = for i from 0 to #upper-1 list {upper#i#0 + upper#i#1, upper#i#1};
    H := new HashTable from {Lower => lower, Upper => upper};
    d := #lower + #upper - 1;
    basedeg := min(min(lower/first), min(upper/first));
    topdeg := max(max(lower/first), max(upper/first));
    -- build lower and upper
    newlower := new MutableList;
    newupper := new MutableList;
    for i from 0 to d-1 do (
        newlower#i = for j from 0 to i list infinity;
        newupper#i = for j from 0 to i list 0;
        );
    new TriangleDiagram from {new Triangle from newlower, new Triangle from newupper}
    )


    lower := triangle monomialIdeal leadTerm I;
    upper := linkedTriangle(I, IX);
    D := new TriangleDiagram from {lower, upperTriangle(upper, r, s)};
    --assert isWellDefined D;
    D
*-

-- input:
--   given M as S-module
-- output:
--   compute a curve (if possible) that has as Rao module
--   M pushed forward to R, with x,y annihilating it.
-- steps:
--   res of M_R (R = k[z,w])
--   smithNF
--   determine mons, get these in the correct order
--   compute mons0
--   return ideal
curveSupportedOnLine = method()
curveSupportedOnLine Module := (M) -> (
    -- M is a module in S (4 variables).
    -- annihilated by x,y (the first 2 variables).
    -- output: an ideal I supported in line x=y=0,
    --  with the same Rao module, or an error if no such curve cna exist.
    S := ring M;
    R := (coefficientRing S)[S_2, S_3];
    A := (coefficientRing S)[S_2];
    w := S_3;
    phi := map(S, R, {S_2, S_3}); -- z,w
    psi := map(R, A, {R_0}); -- z
    MR := pushForward(phi, M);
    CMR := res MR;
    Csmith := smithNF CMR;
    -- to be finished...
    )

beginDocumentation()

doc ///
Key
  TriangleDiagrams
Headline
  triangle diagrams of locally Cohen-Macaulay space curves
Description
  Text
    This package provides functionality to investigate locally
    Cohen-Macaulay (LCM) space curves (i.e. projective
    equi-dimensional, possibly non-reduced or not connected, curves in
    projective 3-space), via their triangle diagrams.

    {\bf Constructing triangle diagrams}
    Suppose $C$ is a curve in $\PP^3$ (actually, any subscheme of equidimension 1),
    such that $C$ does not meet the line $L = (z = w = 0)$, where the ring of $\PP^3$ is in
    variables $x, y, z, w$.

    See @TO (triangleDiagram, Ideal)@ for the definition and examples of the 
    lower triangle diagram of $C$.

  Text
    As a first example, we consider the curve defined by $x^2 z^2 - x y z w - y^2 w^2$, and all monomials of degree 3 in $x$ and $y$.
  Example      
    S = ZZ/32003[x,y,z,w]
    I = ideal(x^3, x^2*y, x*y^2, y^3, x^2*z^2-x*y*z*w-y^2*w^2)
    D = triangleDiagram I
  Text
    {\bf Working with triangle diagrams, e.g. obtaining invariants}
    
    Many numerical invariants of the curve $C$ can be computed
    from its triangle diagram.
  Example
    degree D
    genus D
    degree D == degree I
    genus D == genus I
    lambdaInvariants D
  Text
    If the curve is in sufficiently general position, its initial ideal
    and its triangle diagram are Borel fixed.
  Example
    assert isBorel D
    assert isWeaklyBorel D
  Text
    The curve is arithmetically Cohen-Macaulay (ACM) if the only number
    in the lower diagram is 0.  This curve is not ACM.
  Example
    assert not isACM D
    saturate D
    isACM saturate D
    displayDiagram D
  Text
    See @TO "triangleDiagram"@ for the definition and examples of the 
    upper triangle diagram of $C$.

    {\bf Enumerating all triangle diagrams with specific invariants}
    
    {\bf Latex for displaying triangle diagrams}
    This package also has code for creating tikz/latex code 
    to display these triangles.
///

doc ///
  Key
    TriangleDiagram
  Headline
    triangle diagram of a LCM (equidimensional) space curve
  Description
    Text
      Here we will define the triangle diagram, and give examples how to construct them.
      XXX Not done yet!
  SeeAlso
    Triangle
///

doc ///
  Key
    (triangleDiagram, Ideal)
  Headline
    the lower and upper triangles of an ideal defining an equidimensional space curve in projective 3-space
  Usage
    D = triangleDiagram I
  Inputs
    I:Ideal
      a homogeneous ideal in a polynomial ring with 4 variables, defining a locally Cohen-Macaulay (LCM)
      space curve, that is, an equidimensional scheme of dimension one in $\PP^3$.
  Outputs
    D:TriangleDiagram
  Description
    Text
      Given the ideal $I$ of a (LCM) curve $C \subset \PP^3$ in sufficiently
      general position, this function returns the triangle diagram
      of this ideal (consisting of both the lower and upper triangles).
    Text
      Sufficiently generic means: The scheme defined by the ideal $I$ must be such that no
      component meets the line $S_2 = S_3 = 0$, where $S$ is the ring
      of $I$.  This condition is equivalent to the condition that the
      saturation of the ideal $I + (S_2, S_3)$ is the homogeneous
      maximal ideal $(S_0, S_1, S_2, S_3)$.
    Text
      See @TO "TriangleDiagram"@ for the definition of the triangle diagram of $I$.
    Text
      As a first example, we consider the curve defined by $x^2 z^2 - x y z w - y^2 w^2$, and all monomials of degree 3 in $x$ and $y$.
    Example      
      S = ZZ/32003[x,y,z,w]
      I = ideal(x^3, x^2*y, x*y^2, y^3, x^2*z^2-x*y*z*w-y^2*w^2)
      D = triangleDiagram I
    Text
      As a more complicated example, we construct an extremal curve of degree 6 and genus 3.
    Example
      needsPackage "LCMSpaceCurves"
      S = ZZ/32003[a..d]
      I = extremalCurve(6,3,S)
      betti res I
      checkGeneric I
      D = triangleDiagram I
    Text
      One can obtain various numeric information about $I$ from $D$.
    Example
      degree D
      genus D
      lambdaInvariants D
      assert isBorel D
      assert isWeaklyBorel D
      assert not isACM D
      saturate D
    Text
      The dimensions of the cohomology group $H^i(I(j-i))$ is displayed in
      the next table, at row $i$ and column $j$.
    Example
      cohomologyTable(D, -3, 10)
    Text
      One can translate back to the initial lead term of $I$ (under graded reverse lex order),
      and get back the monomials corresponding to the upper diagram too.
    Example
      lowerMonomials(D, S)
      upperMonomials(D, S)
    Text
      There are two ways to obtain tex for a triangle diagram, and then display these.
    Example
      tridiag D
      tikzpic D
    Text
      One can also call the following to create a tex file, run latex, and display the
      resulting pdf file.
    Pre
      displayDiagram(D, Balls => true, FileName => "foo.tex")
      displayDiagram(D, Balls => false, FileName => "foo.tex")
  SeeAlso
    checkGeneric
    lambdaInvariants
    (degree, TriangleDiagram)
    (genus, TriangleDiagram)
    (isBorel, TriangleDiagram)
    (isWeaklyBorel, TriangleDiagram)
    (isACM, TriangleDiagram)
    "BGG::(cohomologyTable, TriangleDiagram)"
    (lowerMonomials, TriangleDiagram, Ring)
    (upperMonomials, TriangleDiagram, Ring)
///

doc ///
  Key
    (degree, TriangleDiagram)
    (degree, Triangle)
  Headline
    degree of any curve with this triangle diagram
  Usage
    degree D
  Inputs
    D:TriangleDiagram
  Outputs
    :ZZ
  Description
    Text
      Given a triangle diagram, a number of numerical invariants of any
      LCM space curve (not meeting the line $z=w=0$) are determined, including the
      degree, the genus (and therefore the Hilbert polynomial), but also
      including the Hilbert function of the Rao module, and other cohomology 
      dimensions.
      
      As an example, we show an example of a degree 7 and genus 1 curve in $P^3$.
    Example
      R = ZZ/32003[x,y,z,w]
      IC = ideal"x3,x2y,xy2z4-x2z3w2-y3w4,xy3,y4"
      D = triangleDiagram IC
      degree D
      genus D
  SeeAlso
    (genus, TriangleDiagram)
    (cohomologyTable, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram)
    (hh, ZZ, TriangleDiagram)
///

doc ///
  Key
    (genus, TriangleDiagram)
    (genus, Triangle)
  Headline
    arithmetic genus of any curve with this triangle diagram
  Usage
    genus D
  Inputs
    D:TriangleDiagram
     or @ofClass Triangle@, a lower triangle diagram
  Outputs
    :ZZ
      the arithmetic genus of a curve with this triangle diagram
  Description
    Text
      Given a triangle diagram, a number of numerical invariants of any
      LCM space curve (not meeting the line $S_2=S_3=0$, where $S$ is the polynomial ring in
          4 variables of projective 3-space) are determined, including the
      degree, the genus (and therefore the Hilbert polynomial), but also
      including the Hilbert function of the Rao module, and other cohomology 
      dimensions.
      
      As an example, we show an example of a degree 7 and genus 1 curve in $P^3$.
    Example
      R = ZZ/32003[x,y,z,w]
      IC = ideal"x3,x2y,xy2z4-x2z3w2-y3w4,xy3,y4"
      D = triangleDiagram IC
      genus D
      degree D
  SeeAlso
    (degree, TriangleDiagram)
    (cohomologyTable, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram)
    (hh, ZZ, TriangleDiagram)
///

doc ///
  Key
    h1FromDiagram
    (h1FromDiagram, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram)
    (hh, ZZ, TriangleDiagram)
  Headline
    the Hilbert function of the Rao module
  Usage
    h1FromDiagram D
    h1FromDiagram(D, lo, hi)
    hh^1 D
  Inputs
    D:TriangleDiagram
    lo:ZZ
    hi:ZZ
  Outputs
    :List
      of pairs of integers: each pair is of the form {\tt \{ d, dim H^1(I_C(d)) \}},
      and the $d$ ranges from {\tt lo} to {\tt hi} (in order).
  Description
    Text
      If the bounds are not given, they are set to be so that for any curve of the same
      degree and genus, all curves will have zero {\tt H^1} outside of this range.
      The extremal curve has non-zero values in precisely this range.  This allows
      easier comparing between curves or diagrams with the same degree and genus.

      As an example, we show an example of a degree 7 and genus 1 curve in $P^3$.
    Example
      R = ZZ/32003[x,y,z,w]
      IC = ideal"x3,x2y,xy2z4-x2z3w2-y3w4,xy3,y4"
      D = triangleDiagram IC
      h1FromDiagram D
      cohomologyTable(D, -7, 14)
      h1FromDiagram(D, 0,5)
    Text
      A shorthand is to use {\tt hh^1}. (Note: {\tt hh^i} for {\tt i} not one is not 
      (yet) implemented.
    Example
      assert(hh^1 D == h1FromDiagram D)
    Text
      The extremal curve of a given degree and genus has the largest {\tt hh^1} in 
      every degree (i.e. if a curve is not minimal, then it's {\tt hh^1(I_C(d))} is strictly
          smaller than that for the extremal curve (unless for that {\tt d}, it is
              already zero.)
    Example
      needsPackage "LCMSpaceCurves"
      IC2 = extremalCurve(7, 1, R)
      D2 = triangleDiagram IC2
      h1FromDiagram D2
      netList transpose oo
      cohomologyTable(D2, -8, 15)
      assert(h1Extremal(7,1) == h1FromDiagram D2)
      h1Subextremal(7,1)
  SeeAlso
    (cohomologyTable, TriangleDiagram, ZZ, ZZ)
    (h1Extremal, ZZ, ZZ)
    (h1Subextremal, ZZ, ZZ)
///

doc ///
  Key
    h1Extremal
    (h1Extremal, ZZ, ZZ)
  Headline
    the Hilbert function of the Rao module of the extremal curve
  Usage
    h1Extremal(d, g)
  Inputs
    d:ZZ
      the degree of the curve
    g:ZZ
      the arithmetic genus of the curve
  Outputs
    :List
      of pairs of integers: each pair is of the form {\tt \{ d, dim H^1(I_C(d)) \}}
  Description
    Text
      A (non-planar) extremal curve (of degree $d$ and genus $g$) is an LCM space curve
      whose $dim H^1(I_{extremal}(j))$ matches exactly the output of this function.
      
      It is know that extremal curves exist if and only if $g < binomial(d-2,2)$.
      Further, any other non-extremal LCM curve of degree $d$ and genus $g$ has, for each degree $j$,
      $dim H^1(I(j)) \le max(0, dim H^1(I_{extremal}(j)) - 1)$.
      
      In fact, if $C$ is an LCM space curve, but not extremal, and $d \ge 4$, then there
      is a stronger upper bound on the $h^1$-vector, see @TO (h1Subextremal, ZZ, ZZ)@.
      
      Note, the extremal curve has the highest regularity of any LCM space curve of the same
      degree and genus.  The regularity of the quotient $S/E$ is $binomial(d-1,2) - g$
    Example
      h1Extremal(3,-1)
      h1Extremal(4,0)
      h1Extremal(5,2)
      h1Extremal(5,0)
      h1Extremal(6,5)
      h1Extremal(7,9)
      h1Extremal(7,0)
  SeeAlso
      (h1Subextremal, ZZ, ZZ)
      h1FromDiagram
      cohomologyTable
///

doc ///
  Key
    h1Subextremal
    (h1Subextremal, ZZ, ZZ)
  Headline
    the Hilbert function of the Rao module of a subextremal curve
  Usage
    h1Subextremal(d, g)
  Inputs
    d:ZZ
      the degree of the curve
    g:ZZ
      the arithmetic genus of the curve
  Outputs
    :List
      of pairs of integers: each pair is of the form {\tt \{ d, dim H^1(I_{subsectremal}(d)) \}}
  Description
    Text
      A (non-planar) subextremal curve (of degree $d \ge 4$ and genus $g \le binomial(d-3,2)$) 
      is an LCM space curve $C$ whose $dim H^1(I_C(j))$ matches exactly the output of this function, for
      all $j$.
      
      It is know that subextremal curves exist if and only if $d \ge 4$ and $g \le binomial(d-3,2)$.
      Further, any other non-extremal and non-sub-extremal LCM curve of degree $d$ and genus $g$ has, 
      for each degree $j$,
      $dim H^1(I(j)) \le max(0, dim H^1(I_{subextremal}(j))$.
      
      Note, the subextremal curve has the maximum regularity of any
      non extremal LCM space curve of the same degree and genus.  The
      regularity of the quotient $S/E$ is $binomial(d-2,2) - g + 1$

    Example
      h1Subextremal(4,0)
      h1Subextremal(5,1)
      h1Subextremal(6,3)
      h1Subextremal(7,6)

      matrix append((transpose h1Subextremal(7,2)), last transpose h1Extremal(7,2))
  SeeAlso
      (h1Extremal, ZZ, ZZ)
      h1FromDiagram
      cohomologyTable
///

doc ///
  Key
    (cohomologyTable, TriangleDiagram, ZZ, ZZ)
  Headline
    the cohomology (of many twists) of the ideal sheaf
  Usage
    cohomologyTable(D, lo, hi)
  Inputs
    D:TriangleDiagram
    lo:ZZ
    hi:ZZ
  Outputs
    :CohomologyTally
      the (i,j) entry is $dim H^i(I_C(j-i))$, where $I_C$ is the ideal sheaf
      of any LCM curve with this triangle diagram.  Only columns from {\tt lo} to {\tt hi}
      are computed and displayed
  Description
    Text
      Given a triangle diagram, the dimensions of the sheaf cohomology groups 
      of the ideal sheaf of any LCM curve with this triangle diagram is determined.
      
      As an example, we show an example of a degree 7 and genus 1 curve in $P^3$.
    Example
      kk = ZZ/32003
      R = kk[x,y,z,w]
      IC = ideal"x3,x2y,xy2z4-x2z3w2-y3w4,xy3,y4"
      D = triangleDiagram IC
      cohomologyTable(D, -3, 7)
    Text
      To read this table, the (i,j)th entry of this table is $dim H^i(I_C(i-j))$.
      Here are a few examples, and checks via the Macaulay2 built in cohomology routines.
    Example
      I = sheaf module IC
      HH^0(I(5))
      HH^1(I)
      HH^1(I(2))
      HH^2(I(-1))
  SeeAlso
    (h1FromDiagram, TriangleDiagram, ZZ, ZZ)
    (h1FromDiagram, TriangleDiagram)
    (hh, ZZ, TriangleDiagram)
///

doc ///
  Key
    lowerTriangleDiagrams
    (lowerTriangleDiagrams, ZZ, ZZ, List)
  Headline
    generate all possible Borel-fixed lower triangle diagrams with given lambda invariants
  Usage
    lowerTriangleDiagrams(d,g,lambda)
  Inputs
    d:ZZ
    g:ZZ
    lambda:List
  Outputs
    :List
      of @TO Triangle@'s
  Description
    Text
      Let's generate all possible lower diagrams for degree 5, genus 0 LCM space curves.
    Example
      L23 = lowerTriangleDiagrams(5, 0, {2,3})
      L14 = lowerTriangleDiagrams(5, 0, {1,4})
      assert all(L23, t -> (degree t, genus t) == (5, 0))
      assert all(L14, t -> (degree t, genus t) == (5, 0))
      assert all(L23, isBorel)
      Lall = sort(L23 | L14)
    Text
      Not all of these can occur as lower diagrams.
    Example
      R = ZZ/32003[x,y,z,w]
      Lall/(t -> lowerMonomials(t, R))/ideal
      oo/minimalBetti
    Text
      Another way to generate lower diagrams
    Example
      needsPackage "LCMSpaceCurves"
      Lall' = sort for I in spaceCurveBorels(5, 0, R) list triangle I
      assert(sort Lall == sort Lall')
    Text
      Let's now try to find all of the triangle diagrams for this degree and genus.
    Example
      Dall = Lall/possibleDiagrams//flatten
      #Dall == 30
      H1E = h1Extremal(5,0)
      H1e = H1E/last
      select(Dall, D -> last first h1FromDiagram(D, -2, -2) == 0)
  Caveat
    It is possible that some of the ideals or triangles on the list do not occur
    as lower triangles for LCM curves.  This happens especially often for so-called
    "hook" diagrams: lambda invariants of the form {\tt \{ 1, deg-1 \}}
  SeeAlso
///

doc ///
  Key
    possibleDiagrams
    (possibleDiagrams, Triangle)
  Headline
    find all possible triangle diagrams extending a lower triangle
  Usage
    possibleDiagrams T
  Inputs
    T:Triangle
  Outputs
    :List
      of @ofClass TriangleDiagram@
  Description
    Text
      This function enumerates a list of triangle diagrams which
      include all of the possible triangle diagrams extending a lower
      triangle, in general coordinates.  Some of these might not
      correspond to any LCM space curve.  Indeed, one of the uses of
      this function is to try to characterize which do occur as the
      triangle diagram of an LCM space curve, in general coordinates.

    Example
      R = ZZ/32003[x,y,z,w]
      I = monomialIdeal(x^3, x^2*y, x*y^2, y^3, x^2*z^2)
      (degree I, genus I)
      T = triangle I
      Ds = possibleDiagrams T
      cohomologyTable(Ds_0, -5, 5)
      cohomologyTable(Ds_1, -5, 5)
      -- XXX not done here yet.
  Caveat
    This is a superset of all possible triangle diagrams in generic position, as smoe
    might not occur.
  SeeAlso
    (lowerTriangleDiagrams, ZZ, ZZ, List)
///

doc ///
  Key
    "degree 6 curves"
  Headline
    example: (d,g) = (6,g), g >= 0
  Description
    Text
      In this example, we find all of the triangle diagrams
      for LCM space curves of $(d,g) = (6,g)$, for $g \ge 0$.
    Example
      (d,g) = (6,4)
      R = ZZ/32003[x,y,z,w]
      Lall = lowerTriangleDiagrams(d,g,{1,5})
      Dall = Lall/possibleDiagrams//flatten
      set1 = transpose h1Extremal(d,g)
      (lo,hi) = (min first set1, max first set1)
      set2 = {}
      set3 = Dall/(D -> last transpose h1FromDiagram(D, lo, hi))
      matrix(join(set1, set2, set3))
    Example
      (d,g) = (6,3)
      R = ZZ/32003[x,y,z,w]
      L1 = lowerTriangleDiagrams(d,g,{1,5})
      L2 = lowerTriangleDiagrams(d,g,{2,4})
      L3 = lowerTriangleDiagrams(d,g,{1,2,3})
      Lall = sort join(L1,L2,L3)
      Dall = Lall/possibleDiagrams//flatten
      set1 = transpose h1Extremal(d,g)
      (lo,hi) = (min first set1, max first set1)
      set2 = {last transpose h1Subextremal(d,g)}
      set3 = Dall/(D -> last transpose h1FromDiagram(D, lo, hi))

      matrix(join(set1, set2, set3))

      Ds = select(Dall, D -> all((last transpose h1Subextremal(d,g) -  last transpose h1FromDiagram D), a -> a >= 0))
      -- which of these actually occur?
      Ds/(D -> cohomologyTable(D, -3, 7))      
      Ds/(D -> lowerMonomials(D, R))/ideal/minimalBetti
    Text
    Example
      (d,g) = (6,2)
      R = ZZ/32003[x,y,z,w]
      L1 = lowerTriangleDiagrams(d,g,{1,5})
      L2 = lowerTriangleDiagrams(d,g,{2,4})
      L3 = lowerTriangleDiagrams(d,g,{1,2,3})
      Lall = sort join(L1,L2,L3)
      Dall = Lall/possibleDiagrams//flatten
      set1 = transpose h1Extremal(d,g)
      (lo,hi) = (min first set1, max first set1)
      set2 = {last transpose h1Subextremal(d,g)}
      set3 = Dall/(D -> last transpose h1FromDiagram(D, lo, hi))

      matrix(join(set1, set2, set3))

      Ds = select(Dall, D -> all((last transpose h1Subextremal(d,g) -  last transpose h1FromDiagram D), a -> a >= 0))
      -- which of these actually occur?
      Ds/(D -> cohomologyTable(D, -3, 7))      
      Ds/(D -> lowerMonomials(D, R))/ideal/minimalBetti

    Example
      (d,g) = (5,0)
      R = ZZ/32003[x,y,z,w]
      L1 = lowerTriangleDiagrams(d,g,{1,4})
      L2 = lowerTriangleDiagrams(d,g,{2,3})
      Lall = sort join(L1,L2)
      Dall = Lall/possibleDiagrams//flatten
      set1 = transpose h1Extremal(d,g)
      (lo,hi) = (min first set1, max first set1)
      set2 = {last transpose h1Subextremal(d,g)}
      set3 = Dall/(D -> last transpose h1FromDiagram(D, lo, hi))

      matrix(join(set1, set2, set3))

      Ds = select(Dall, D -> all((last transpose h1Subextremal(d,g) -  last transpose h1FromDiagram D), a -> a >= 0))
      -- which of these actually occur?
      Ds/(D -> cohomologyTable(D, -3, 7))      
      Ds/(D -> lowerMonomials(D, R))/ideal/minimalBetti
    
    Text
      We see there are 7possible triangle diagrams: one for the extremal,
      one for the subextremal, one for an ACM curve, and 4 others.
      Which occur?
  SeeAlso
///

-- XXX

TEST ///
-*
  restart
*-
  needsPackage "LCMSpaceCurves"
  needsPackage "TriangleDiagrams"
  R = ZZ/32003[x,y,z,w]
  IC = ideal"x3,x2y,xy2z4-x2z3w2-y3w4,xy3,y4"
  assert isPrimary IC
  assert(degree IC == 7)
  assert(genus IC == 1)
  D = triangleDiagram IC
  assert(lambdaInvariants D == {1,2,4})
  assert(genus D == genus IC)
  h1FromDiagram D -- XX
  matrix h1FromDiagram(D,0,5) -- XX
  matrix oo
  HH^1((sheaf module IC)(>=-7)) == Ext^4(Ext^3(R^1/IC, R^{-4}), R^{-4})
  tridiag D
  tridiag D#0
  
  BS = spaceCurveBorels(5, 0, R)
  BS/monomialIdeal/triangle

  BS = spaceCurveBorels(6, 0, R)
  netList pack(BS/monomialIdeal/triangle, 4)
  
  partition(lambdaInvariants, BS/monomialIdeal/triangle)
///

TEST ///
  -- testing triangle
-*
  restart
*-
  needsPackage "LCMSpaceCurves"
  needsPackage "TriangleDiagrams"
  R = ZZ/32003[x,y,z,w]
  M = coker matrix{{x,y,z^2, w^3, z*w^2}}  
  I = minimalSpaceCurveIdeal M    
  res I
  M' = Ext^3(R^1/I, R)
  Ext^4(M', R) == M
  
  D = triangleDiagram I
  assert((degree I, genus I) == (6, 1))
  assert(degree I == degree D)
  assert(genus I == genus D)
  I == radical I
  isPrime I
  minimalPrimes I
  oo/dim
  
  --displayDiagram D
///



TEST ///
  -- testing triangleDiagram
-*
  restart
*-
  needsPackage "LCMSpaceCurves"
  needsPackage "TriangleDiagrams"
  R = ZZ/32003[x,y,z,w]
  M = coker matrix{{x,y,z^2, w^3, z*w^2}}  
  I = minimalSpaceCurveIdeal M
  assert((degree I, genus I) == (6, 1))
  assert(I == radical I)

  D = triangleDiagram I
  assert(degree D == degree I)
  assert(genus D == genus I)
  Dlower = new Triangle from {{infinity}, {infinity, infinity}, {infinity, infinity, infinity}, {0, 0, 1, 1}, {0, 0, 0, 0, 0}}
  Dupper = new Triangle from {{0}, {0, 0}, {2, 0, 0}, {infinity, infinity, infinity, infinity}}
  assert(D#0 == Dlower)
  assert(D#1 == Dupper)
  D' = new TriangleDiagram from {Dlower, Dupper}
  assert(D' == D)
  
  L1 = lowerMonomials(D#0, R)
  L = lowerMonomials(D, R)
  U = upperMonomials(D, R)
  assert(L1 == L)
  assert(L == {x^3, x^2*y, x*y^2*z, y^3*z, x*y^3, y^4})
  assert(U == {x^2*z^2})
  D1 = triangleDiagram(L, U)
  assert(D1 == D)

  res I
  M' = Ext^3(R^1/I, R)
  Ext^4(M', R) == M
  
  --displayDiagram D
///

TEST ///
  -- running example for the paper
-*
  restart
*-
  needsPackage "LCMSpaceCurves"
  needsPackage "TriangleDiagrams"
  S = ZZ/32003[x,y,z,w]
  subextremalCurve(4, -1, S)
  spaceCurveBorels(4, -1, S)
  I = (ideal(x,y))^3 + ideal(x^2*z-x*y*w, x*y*z-y^2*w)
  (degree I, genus I) == (4,-1)
  D = triangleDiagram I
  assert(degree D == degree I)
  assert(genus D == genus I)

  J = (ideal(x^3, y^3)) : I
  E = triangleDiagram J
  assert(degree E == degree J)
  assert(genus E == genus J)
  
  HH^1((sheaf module I)(>=0))
  HH^1((sheaf module J)(>=0))
///

TEST ///
  -- test generation of lower triangles
-*
  restart
  needsPackage "TriangleDiagrams"
*-
  needsPackage "LCMSpaceCurves"
  
  -- first we construct a function to help us check the answer.
  testLowerTriangles = (d,g) -> (
    R := QQ[x,y,z,w];
    elapsedTime lowerTriangles := spaceCurveBorels(d, g, R)/triangleDiagram/first;
    allL := partition(lambdaInvariants, lowerTriangles);
    << "number for each lambda invariant: " << (for k in keys allL list k => #allL#k) << endl;
    print allL;
    print lowerTriangles;
    elapsedTime for k in keys allL do assert(#allL#k == # lowerTriangleDiagrams(d,g,k))
    )

  lowerTriangleDiagrams(3,0,{1,2})
  
  testLowerTriangles(2, 0)
  testLowerTriangles(2, -1)
  testLowerTriangles(2, -2)
  testLowerTriangles(2, -3)

  testLowerTriangles(3, 0) -- assertion failed previously
  testLowerTriangles(3, -1)
  testLowerTriangles(3, -2)

  testLowerTriangles(4, 1)
  testLowerTriangles(4, 0)
  testLowerTriangles(4, -1)

  testLowerTriangles(5,3)
  testLowerTriangles(5,2)    
  testLowerTriangles(5,1)
  testLowerTriangles(5,0)  
  testLowerTriangles(5,-1)  
  testLowerTriangles(5,-2)

  testLowerTriangles(6,4)  
  testLowerTriangles(6,3) -- failed previously
  testLowerTriangles(6,2)
  testLowerTriangles(6,1)
///

TEST /// 
     -- Floystad construction
    -- Running example.
    needsPackage "SpaceCurves"
    kk = ZZ/32003
    S = kk[x,y,z,w]
    I = ideal"x3,x2y,xy2,y3,x2z2-xyzw-y2w2"
    DL = floystadTriangleDiagram I
    DF = triangleDiagram I
    assert(DL == DF)
    use S
    J1 = eliminate(I + ideal(w), w)
    J2 = eliminate(I + ideal(z,w), {z,w})
    J3 = eliminate((saturate(J1,z)) + ideal(z), {z})
    -- The following 3 are the same
    Ext^2(comodule J1, S)
    Ext^2(comodule J3, S)
    Ext^2(comodule ideal leadTerm I, S)
    -- This one is different:
    Ext^2(comodule J2, S)
    saturate(ideal leadTerm I, z*w)
    A = kk[x,y, DegreeRank=>2]
    L = comodule ideal"x2,y3,xy2"
    Ext^2(L, A^{{-1,-1}}) -- this is isomorphic to Hom_k(L, k)
    
    -- see also runngineg-example.m2
///

TEST ///    
    -- Example 1. Borel, but not generic coordinates
    needsPackage "SpaceCurves"
    kk = ZZ/32003
    S = kk[x,y,z,w]
    I = ideal"x3,x2y,xy2,y3,x2z-y2w"
    DL = floystadTriangleDiagram I
    DF = triangleDiagram I
    assert(DL == DF)

    -- Example 2. Same as example 1, but in generic coordinates
    kk = ZZ/32003
    S = kk[x,y,z,w]
    I = ideal"x3,x2y,xy2,y3,x2z-y2w"
      rand = map(S,S,random(S^1, S^{4:-1}))
      I = trim rand I
    DL = floystadTriangleDiagram I
    DF = triangleDiagram I
    assert(DL == DF)
    (B2,inK2,Z2) = initialModule I

    -- Example 3.  (d,g) = (6,2) -- TODO: Floystad diagram takes long time here...
    kk = ZZ/32003
    S = kk[x,y,z,w]
    M = S^1/(x,y,z^2,z*w,w^4)
    I = minimalCurve M
    res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I
    --assert(DL == DF)

    -- Example 4.
    kk = ZZ/32003
    S = kk[x,y,z,w]
    M = S^1/(x,y,z^2,z*w,w^4)
    C = curve(7,2)
    I = ideal C
    S = ring I
      rand = map(S,S,random(S^1, S^{4:-1}))
      I = trim rand I
    res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I -- TODO: too long.
    --assert(DL == DF)

    C = curve(7,4)
    I = ideal C
    S = ring I
      rand = map(S,S,random(S^1, S^{4:-1}))
      I = trim rand I
    betti res I
    DL = triangleDiagram I
    DF = floystadTriangleDiagram I
    assert(DL == DF)

    C = curve(7,0)
    I = ideal C
    S = ring I
      rand = map(S,S,random(S^1, S^{4:-1}))
      I = trim rand I
    betti res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I -- TODO: does it, but takes too long
    --assert(DL == DF) -- TODO: incorrectly says they are different.
///

TEST ///
    needsPackage "SpaceCurves"
    kk = ZZ/32003
    S = kk[x,y,z,w]
    M = S^1/(x,y,z,w^7)
    I = minimalCurve M -- extremal curve?
    assert((degree I, genus I) == (8,14))
    res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I
    --assert(DL == DF)
///


TEST ///
    needsPackage "SpaceCurves"
    kk = ZZ/32003
    S = kk[x,y,z,w]
    M = S^1/(x,y,z^3,z^2*w^2,w^7)
    I = minimalCurve M -- extremal curve?
    assert((degree I, genus I) == (9,9))
    res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I -- too long
    --assert(DL == DF)
///

TEST ///
    needsPackage "SpaceCurves"
    kk = ZZ/32003
    S = kk[x,y,z,w]
    M = (S^1/(x,y,z,w)) ++ S^1/(x,y,z^2,w^2)
    I = minimalCurve M -- extremal curve?
    assert((degree I, genus I) == (10,9))
    betti res I
    DL = triangleDiagram I
    --DF = floystadTriangleDiagram I -- too long
    --assert(DL == DF)
///

-- TODO: this function is not working yet...
///
  -- of the triangle diagram from the module M.
-*
  restart
  debug needsPackage "TriangleDiagrams"
*-
  S = ZZ/32003[x,y,z,w]
  I = ideal(x^2*z-x*y*w,x*y^2,x^2*y,x^3,y^3*z-x^2*w^2,y^4)
  --I = ideal (x^3,x*y^2,y^4,x^2*z-x*y*w,y^3*z-x^2*w^2)
  assert((degree I, genus I) == (5,0))
  M = HH^1((sheaf module I)(>=0))
  D = triangleDiagram I
  M2 = Ext^3(comodule I, S) -- try this for M too...

  -- now let's take M and construct the free resolution
  -- over k[z,w] of it.
  -- XXX
  A = ZZ/32003[z]
  R = ZZ/32003[z,w]
  phi = map(S,R,{S_2, S_3})
  f = map(S,A,{S_2})
  MR = pushForward(phi, M)

  CMR = res MR
  CMR.dd
  CMR1 = smithNF CMR
  CMR1.dd
  assert isHomogeneous CMR1

  -- given phi (and of course a module M), here is the res
  -- of M over 2 variables z,w, with powers of z correct (I think).
  C = smithNF res pushForward(phi, M)
  C2 = smithNF res pushForward(phi, M2) -- dual of first?

  -- step 2: from this, extract the info about the compatible diagrams.
  -- actually, this just needs Q, N, and their decompositions.
  triangleDegrees(MR, R_1, map(R, A, {R_0}))
  killz = map(A, R, {A_0,0})
  f = map(R, A, {R_0})
  findQN(MR, R_1, f)
  killz CMR
  N
///

end--

restart
uninstallAllPackages()
uninstallPackage "TriangleDiagrams"
restart
installPackage "LCMSpaceCurves"
installPackage "TriangleDiagrams"

check "TriangleDiagrams"
help (triangleDiagram, Ideal)
peek loadedFiles
viewHelp
restart
needsPackage "TriangleDiagrams"
needsPackage "LCMSpaceCurves"

doc ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  Caveat
  SeeAlso
///




TEST ///
  -- example for seeing if the diagram of a curve in general coords is Borel.
-*  
  restart
  needsPackage "TriangleDiagrams"
*-
  needsPackage "LCMSpaceCurves"
  S = ZZ/32003[x,y,z,w]
  M = coker map(S^1 ++ S^{1},,matrix{{x,y,0,0,w,-z, 0},
                   {0,0,x,y,0,w^2, z^2}})
  isHomogeneous M
  I = last minimalSpaceCurve M
  degree I
  genus I
  triangleDiagram I
  X = ideal select(flatten entries gens gb I, f -> leadTerm f == x^3 or leadTerm f == y^3)
  J = X : I
  triangleDiagram J
  isBorel monomialIdeal leadTerm J
  leadTerm J
  triangleDiagram J
  HH^1((sheaf module I)(>=0))
  HH^1((sheaf module J)(>=0))
///


restart
needsPackage "TriangleDiagrams"



doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
  -- Rich Liebling thesis
  -- prop 4.1.3, pg 82
  -- start with a triangle diagram, with no shared columns.
  -- one should be able to construct a LCM curve supported on V(x,y)
  -- with a Rao module consistent with this diagram.
  restart
  needsPackage "TriangleDiagrams"
  S = ZZ/32003[x,y,z,w]
  I = ideal"x3,x2y,xy2,y3,x2z2-xyzw+y2w2"
  isPrimary I
  res I
  triangleDiagram I
  M = HH^1((sheaf module I)(>=-5))
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///


  restart
  needsPackage "TriangleDiagrams"
  S = ZZ/32003[a..d]
  f = map(S,S,random(S^1, S^{4:-1}));
  I = monomialCurveIdeal(S, {1,3,4})
  J = trim f(I);
  D = triangleDiagram J
  cohomologyTable(D, -3, 4)
  displayDiagram D
  tikz D
  tridiag D

  needsPackage "LCMSpaceCurves"
  spaceCurveBorels(4,1,S)
  spaceCurveBorels(4,2,S)
  spaceCurveBorels(4,0,S, Filter=>false)




inID = linkedInitialIdeal (J, findCI J)
upperTriangle(inID, 2, 4)
T = triangle J
"foo.tex" << wrapLatex tikzpic T << close
run "pdflatex foo.tex"
run "open foo.pdf"

inJ = ideal leadTerm J
T = triangle inJ
"foo.tex" << wrapLatex latex {{tikzpic T, latex inJ}, {tikzpic T, latex inJ}} << close
"foo.tex" << wrapLatex latex {{{{tikzpic T}, {latex inJ}}}, {{{tikzpic T, latex inJ}}}} << close

displayTriangles(2, {ideal leadTerm J, ideal leadTerm J})
"foo.tex" << wrapLatex oo << close;


B = spaceCurveBorels(5,0,S)
B/(b -> triangle b)

example = method()
example Ideal := (I) -> (
     concatenate(
	  /// \begin{example} ///,
     	  replace("\\*", "", toString I),
     	  /// \end{example} ///
	  )
     )

for I in B list (
     T := triangle I;
     wrapLatex concatenate(example I, "\n", tikz T)
     )

T = new LowerTriangle from { {infinity}, {infinity, infinity}, {0,1,infinity}, {0,0,0,0}}


S = ZZ/32003[x,y,z,w]

I = ideal (x^3,x*y^2,y^4,x^2*z-x*y*w,y^3*z-x^2*w^2)
degree I
I = saturate I
genus I
res I
Ext^3(comodule I, S)
codim oo
degree I
f = map(S,S,random(S^1, S^{4:-1}))
I = trim f(I)
triangleDiagram I

eliminate (I, x)

findCI I


inID = linkedInitialIdeal (I, findCI I)
upperTriangle(inID, 3, 4)
triangle I

triangleDiagram J


///
-- What is the point of this code?  Simply to remind us how it works?
-- Probably also to see what cohomologyTable looks like.
  restart
  needsPackage "BGG"
  kk = ZZ/32003
  S = kk[x,y,z,w]
  E = kk[e_0..e_3, SkewCommutative => true]
  I = ideal (x^3,x*y^2,y^4,x^2*z-x*y*w,y^3*z-x^2*w^2)
  presentation module I
  cohomologyTable(sheaf module I, -3, 8)
  T = tateResolution(presentation module I, E, -3, 4)
  T = T ** E^{1}
  beilinson(T.dd_2, S)
  beilinson(T.dd_1, S)
  beilinson(T.dd_0, S)

  beilinson(T.dd_4, S) * beilinson(T.dd_5, S)
  beilinson(T.dd_5, S) * beilinson(T.dd_6, S)
  beilinson(T.dd_6, S) * beilinson(T.dd_7, S)
  beilinson(T.dd_7, S) * beilinson(T.dd_8, S)

  m1 = beilinson(T.dd_5, S)
  m2 = beilinson(T.dd_6, S)
  m3 = beilinson(T.dd_7, S)
  m4 = beilinson(T.dd_8, S)
  prune((ker m1) / (image m2))
  prune((ker m2) / (image m3))
  prune((ker m3) / (image m4))
  beilinson(T.dd_7, S)
  beilinson(T.dd_8, S)
///



///
  -- XXX
  restart
  debug needsPackage "TriangleDiagrams"
  A = ZZ/32003[z]
  R = ZZ/32003[z,w]
  S = ZZ/32003[x,y,z,w]
  M = S^1/(x, y, z^4, z^3*w, w^4)
  phi = map(S,R,{S_2, S_3})

  MR = pushForward(phi, M)
  minimalBetti MR
  prune (MR ** R^1/R_1)

  Q = prune(MR ** R^1/R_1)
  N = prune Tor_1(MR, R^1/R_1)

  psi = map(R,A,{R_0})
  QA = pushForward(psi, Q)
  NA = pushForward(psi, N)

  psi = map(R,A,{R_0})
  findQN(MR, R_1, psi)
  
  psi = map(S,A,{S_2})
  findQN(M, S_3, psi)
  
  use S
  M = S^1/(x, y, z^4-w^4, z^3*w-z^2*w^2, w^5)
  M = S^1/(x, y^2, z^4-w^4, z^3*w-z^2*w^2, w^5)
  phi = map(S,R,{S_2, S_3})
  MR = pushForward(phi, M)
  CMR = res MR
  CMR.dd
  CMR1 = smithNF CMR
  CMR1.dd
  assert isHomogeneous CMR1
  
  psi = map(S,A,{S_2})
  (NA, QA) = findQN(M, S_3, psi)
  (D,P,Q) = smithNF presentation NA
  twists NA
  triangleDegrees(M, S_3, psi)

  use R
  sub(CMR.dd_2, {w => 0})
  (D,P,Q) = smithNF(oo)
  f2 = sub(P,R) * CMR.dd_2 * sub(Q, R)
  f1 = CMR.dd_1 * sub(P^-1, R)

  use S
  mons = matrix{{x^2, y^3 ,x*y}}
  mons0 = matrix{{x^3, x^2*y, x*y^2, y^4}}
  I = ideal(mons * sub(f2, S)) + ideal mons0
  res I
  triangleDiagram I
  primaryDecomposition I

  mons = join({x^5, x^3*y^3, x^2*y^4, y^7}, {x*y^5, x^4*y})
  mons0 = flatten entries gens (trim(ideal(x,y) * ideal mons))

  ideal(matrix{mons} * sub(f2,S)) + ideal mons0

    
  needsPackage "LCMSpaceCurves"
  needsPackage "SpaceCurves"
  minimalCurve M

  
  smithNormalForm presentation NA
  m = presentation NA
  (D,P,Q) = smithNormalForm m
  D == P * m * Q
  Q = map(source m,,Q)
  P = transpose  map(dual target m,,transpose P)
  isHomogeneous P
  isHomogeneous Q
  map(target P, source Q, D)
  isHomogeneous oo

mons = matrix{{y^2, x^2, x*y}}
mons0 = matrix{{x^3, x^2*y, x*y^2, y^3}}
        
-- need to get the upper and lower monomials from this.
B = (res MR).dd_2
I = ideal(mons * sub(B, S)) + ideal mons0
triangleDiagram I

///



