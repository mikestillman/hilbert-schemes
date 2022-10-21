newPackage(
    "LCMSpaceCurves",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", 
            Email => "", 
            HomePage => ""}},
    Headline => "examples of special equidimensional (LCM) space curves",
    PackageExports => {
        "StronglyStableIdeals" --,
        -- "TriangleDiagrams"
        -- ("TriangleDiagrams", FileName => "./TriangleDiagrams.m2")
        },
    DebuggingMode => true
    )

--needs "borel.m2"

export {
    -- generation of Borel's
    "generatorList",
    "doubleSaturation",
    "spaceCurveBorels",
    "Filter",
    -- partition by double saturation

    -- minimal ideal in a linkage class    
    "minimalSpaceCurveIdeal",

    "ext0",
    "degreeMatrix",
    "randomElement",

    "randomLexCurve",
    "extremalCurve",
    "subextremalCurve",
    "curveInDoublePlane",
    
    "degree3Type1",
    "degree3Type2",
    "degree3Type3"
--     latexBorels
     }

spaceCurveBorels = method(Options => {Filter => true})
spaceCurveBorels(ZZ, ZZ, Ring) := opts -> (d, g, S) -> (
    -- returns a list of all saturated Borel-fixed (in char 0) monomial ideals 
    -- with Hilbert polynomial d * t + 1 - g (i.e. degree d, genus g), in P^3.
    if numgens S =!= 4 then error "expected a polynomial ring in 4 variables";
    A := ring hilbertPolynomial(S, Projective => false);
    allborels := stronglyStableIdeals(d * A_0 + 1 - g, S);
    allborels = allborels/monomialIdeal;
    if opts.Filter then (
        lexpt := monomialIdeal(S_0, S_1^d);
        allborels = select(allborels, b -> doubleSaturation b != lexpt);
        );
    allborels
    )

doubleSaturation = method()
doubleSaturation MonomialIdeal := (B) -> (
    -- we assume that B is a strongly stable ideal.
    -- really: we only need that the last 2 variables are generic.
    R := ring B;
    if numgens R <= 1 then error "expected at least 2 variables";
    B1 := saturate(B, R_(numgens R - 1));
    saturate(B, R_(numgens R - 2))
    )

generatorList = method()
generatorList MonomialIdeal := (I) -> (
    flatten entries sort (gens I, MonomialOrder=> Descending, DegreeOrder=>Ascending)
    )

TEST ///
-*
  restart
  needsPackage "LCMSpaceCurves"
*-
  S = ZZ/32003[x,y,z,w]
  Bs = spaceCurveBorels(3,0,S, Filter=>false)
  assert(#Bs == 3)
  Bs = spaceCurveBorels(3,0,S)
  assert(#Bs == 1)
  Bs/doubleSaturation
  Bs/generatorList//netList
  Bs/doubleSaturation/generatorList//netList
  

  Bs = spaceCurveBorels(5,0,S, Filter=>false)
  partition(f -> generatorList doubleSaturation f, Bs)
///

--------------------------------------
-- Minimal curve in a linkage class --
--------------------------------------
-- This algorithm is the one from Liebling's thesis (page 49-50)
-- which comes from MDP90, section IV.
trunc = method()
trunc(ZZ, Matrix) := (d,m) -> (
     F := degrees source m;
     Floc := positions(F, a -> first a <= d);
     submatrix(m, Floc)
     )

ell = method()
ell(ZZ,Matrix) := (d,m) -> (
     L := degrees source m;
     # select(L, a -> first a === d)
     )

ellsharp = method()
ellsharp(ZZ,Matrix) := (d,m) -> (
     L := degrees source m;
     # select(L, a -> first a <= d)
     )

-- ell = (n,p) -> (L := degrees source p; length select(L, a -> first a === n))
alpha = (n, p) -> rank trunc(n,p)
beta = (n,p) -> (
    s := trunc(n,p);
    r := rank s;
    while r >= 0 do
      if codim minors(r, s) >= 2 then return r else r = r-1;
    )

qfcn = method()
qfcn(List,List,List) := (alphas, betas, ellsharps) -> (
    -- assume: alphas, beta, ellsharps are lists of non-negative integers of the
    -- same length.  Also, the first entry of each is 0.
    a0 := 1 + max select(0..#alphas-1, i -> alphas#i == betas#i and alphas#i == ellsharps#i);
    result := {0};
    for i from 1 to #alphas-1 do (
        if i < a0 then 
            result = append(result, ellsharps#i - ellsharps#(i-1))
        else (
            result = append(result, min(alphas#i - 1, betas#i) - sum result);
            )
        );
    result
    )

makeP = method()
makeP(ZZ, List, Ring) := (firstdegree, qs, R) -> (
    result := flatten for i from 0 to #qs-1 list (
        qs#i : -(firstdegree + i)
        );
    R^result
    )

-- minimalSpaceCurveIdeal
--  input: a finite length graded module in a polynomial ring in 4 variables (i.e. on P^3)
--  output: an ideal in the same ring, which is minimal in the linkage class of M.
minimalSpaceCurveIdeal = method()
minimalSpaceCurveIdeal Module := Ideal => (M) -> (
    R := ring M;
    -- step 0: error checks
    if numgens R =!= 4 then error "expected a polynomial ring with 4 variables";
    if dim M != 0 then error "expected a finite length module";
    -- step 1: compute a free res of M, and in particular, the map sigma: L2 --> L1
    kst := (coefficientRing R)[getSymbol "s", getSymbol "t"];
    phi := map(kst, R, random(kst^1, kst^{-1,-1,-1,-1}));
    C := res M;
    sigma := C.dd_2;
    N0 := image sigma;
    L := C_2;

    firstdegree := -1 + first min degrees L;
    topdegree := first max degrees L;
    ells := for i from firstdegree to topdegree list ell(i,sigma);
    ellsharps := for i from firstdegree to topdegree list ellsharp(i,sigma);
    alphas := for i from firstdegree to topdegree list alpha(i,sigma);
    betas := for i from firstdegree to topdegree list beta(i,phi sigma);
    --betas2 = for i from firstdegree to topdegree list beta(i,sigma);
    qs := qfcn(alphas, betas, ellsharps);
    P := makeP(firstdegree, qs, R);
    NmodP := coker(random(L, P) | C.dd_3);
    H := Hom(NmodP,R);
    I := trim ideal cover homomorphism H_{0};
    (alphas, betas, ellsharps, qs, makeP(firstdegree, qs, R), I); -- TODO: why is this line here?
    I 
    -- TODO: I think this is a description of the algorithm.  Check that, check that this is all
    --  implemented!
    -- step 2: compute the numbers beta(n) <= alpha(n) <= ell(n)
    --  and a0 := 1 + max(n | all three are equal at n)
    -- step 3: take a free direct summand P of L, given by:
    --  for twist S(-n), take q(n).
    --  where q(n) = what?
    --    for n < a0, q(n) = ell(n) (i.e. entire direct summand of L in these degrees
    --    for n >= a0:
    --      q#(n) = alpha(n)-1 if beta(n) = alpha(n)
    --            = beta(n) if beta(n) < alpha(n)
    --      (and  q(n) = q#(n) - q#(n-1) )
    --  the difficulty is to compute beta(n)
    -- step 4: take a general map P --> N0, and find the ideal I s.t. 0 --> P --> N0 --> I(h) --> 0
    --  is exact.  Return this ideal (and maybe the integer h?)
    )

--------------------------------------

degreeMatrix = method()
degreeMatrix Matrix := (M) -> (
     F := target M;
     G := source M;
     transpose matrix (
       for i from 0 to rank G - 1 list 
       for j from 0 to rank F - 1 list 
         first ((degrees G)_i - (degrees F)_j)))

ext0 = method()
ext0 Ideal := (I) -> (
     X := variety I;
     IX := sheaf coker((presentation module I) ** ring X);
     (rank Ext^0(IX,OO_X), rank Ext^1(IX,OO_X))
     )

randomElement = method()
randomElement(ZZ,Ideal) := (d,I) -> ((gens I) * random(source gens I, (ring I)^{-d}))_(0,0)

randomLexCurve = method()
randomLexCurve(ZZ,ZZ,Ring) := (d,g,R) -> (
    npts := (d-1)*(d-2)//2 - g;
    -- first do the random plane, and the random degree d poly in that plane:
    I1 := ideal random(R^1, R^{-1,-d});
    I2 := intersect for i from 1 to npts list
    minors(2, vars R || random(R^1, R^4));
    intersect(I1,I2)
    )

extremalCurve = method()
extremalCurve(ZZ,ZZ,Ring) := (d,g,R) -> (
     -- a random extremal curve of degree d and genus g in R
     -- R should be a polynomial ring in 4 variables
     a := binomial(d-2,2) - g;
     if a <= 0 then error "there is no extremal curve if g >= binomial(d-2,2)";
     ell := d-2;
     F := random(a, R);
     G := random(a+ell, R);
     if a > 1 then (
	     -- return (a^2, a b, G1 b^2, a G + G1 b F)
	     -- where deg(G1) = ell, deg(F) = a, deg(G) = a + ell
	     G1 := random(ell, R);
	     trim ideal(R_0^2, R_0*R_1, G1 * R_1^2, R_0 * G + G1 * R_1 * F)
	     )
     else if a == 1 then (
	     ideal(R_0*F,R_1*F,R_0*G,R_1*G)
	     )
     )

subextremalCurve = method()
subextremalCurve(ZZ,ZZ,Ring) := (d,g,R) -> (
     IE := extremalCurve(d-2, g+3-d,R);
     F := randomElement(2,IE);
     L := ideal(F, randomElement(d-2,IE));
     J := L : IE;
     L2 := ideal(F, randomElement(d-1,J));
     trim(L2 : J)
     )

-- Construction of curves lying in a double plane in P^3
curveInDoublePlane = method()
curveInDoublePlane(Ideal, RingElement, RingElement, Ring) := (IZ, F, G, S) -> (
     -- IZ is a (saturated) ideal of a subscheme in P^2, possibly locally a complete intersection
     -- F is a homogeneous element in IZ, IY = (F)
     -- G is a homogeneous poly in (R = ring IZ), a ring in 3 variables, IP = (FG)
     -- S is a polynomial ring in 4 variables, coordinate ring of P^3.
     -- Result is an ideal in S, which is a locally CM curve in a double plane
     R := ring IZ;
     if R =!= ring F or R =!= ring G or numgens R =!= 3 then 
       error "excepted same ring, in 3 variables";
     degZ := degree IZ;
     degY := first degree F;
     degP := degY + first degree G;
     << "degP = " << degP << endl;
     H := basis(degP-1, Hom(IZ, R^1/F));
     rand := random(R^(numColumns H), R^1);
     FH := matrix homomorphism(H * rand);
     toS := map(S,R,{S_1,S_2,S_3});
     FS := toS F;
     GS := toS G;
     IZS := toS IZ;
     FHS := toS FH;     
     I1 := ideal(S_0^2, S_0 * FS, FS^2 * GS);
     I2 := ideal(FS * GS * (gens IZS) + S_0 * FHS);
     trim(I1+I2)
     )

----------------------------
-- Degree 3 curves ---------
----------------------------
-- Ideals of LCM curves in P^3 of degree 3
-- from paper of Nollet

-- H_-1: from prop. 3.2  (extremal curves)
-- H_0: prop 3.3
-- H_a, for 0 < a < (-2-g)/3, prop 2.3

degree3Type1 = method()
degree3Type1(ZZ, Ring) := (g,R) -> (
    -- Nollet type H_(-1) 
     a := R_0;
     b := R_1;
     c := R_2;
     deg := -g;  -- WHAT IS IT REALLY???
     F := random(deg, R);
     G := random(deg, R);
     F = sub(F, {a=>0, b=>0});
     G = sub(G, {a=>0, b=>0});
     IZ := ideal(a^2, a*b, b^2, a*F-b*G);
     intersect(ideal(a,c), IZ)
     )

degree3Type2 = method()
degree3Type2(ZZ, Ring) := (g,R) -> (
     -- Nollet type H_0
     a := R_0;
     b := R_1;
     c := R_2;
     d := R_3;
     deg := -g-1;  -- WHAT IS IT REALLY???
     F := random(deg, R);
     G := random(deg, R);
     F = sub(F, {a=>0, b=>0});
     G = sub(G, {a=>0, b=>0});
     IZ := ideal(a^2, a*b, b^2, a*F-b*G);
     intersect(ideal(c,d), IZ)
     )

degree3Type3 = method()
degree3Type3(ZZ, ZZ, Ring) := (g,da,R) -> (
    -- Nollet type H_a
     a := R_0;
     b := R_1;
     c := R_2;
     d := R_3;
     if da <= 0 or da >= (-2-g)/3 then error "second argument must satisfy: 0 < a < (-2-g)/3";
     db := -2-3*da-g;
     F := random(da+1, R);
     G := random(da+1, R);
     F = sub(F, {a=>0, b=>0});
     G = sub(G, {a=>0, b=>0});
     P := random(db, R);
     Q := random(-g, R);
     P = sub(P, {a=>0, b=>0});
     Q = sub(Q, {a=>0, b=>0});
     J := ideal(F^2, F*G, G^2);
     tail := (matrix{{a^2, a*b, b^2}} * (Q // gens J))_(0,0);
     H := a*G-b*F;
     ideal(a^3,a^2*b,a*b^2,b^3,a*H, b*H, P*H-tail)
     )

---------------------------- 
-*
latexBorels = method()
latexBorels(ZZ,ZZ,Ring) := (deg,gen,R) -> (
     -- deg is degree
     -- gen is genus
     -- R must be a polynomial ring in 4 variables, with variables named a,b,c,d.
     -- output: a string containing a latex file for displaying all saturated Borels
     --  with the given degree and genus, except for the ones where when setting the
     --  variable c to 1 (the double saturation) gives (a, b^deg).
     Bpart := getPossibleLCMBorels(deg,gen);
     Bnonlex := select(Bpart, x -> ideal x#0 != ideal(R_0, (R_1)^(deg)));
     Bnonlex = flatten (Bnonlex/(x -> drop(x,1)));
     Bnonlex = Bnonlex/ideal;	  
     S := concatenate apply(pack(6, Bnonlex), x -> displayTriangles(2, x));
     wrapLatex S
     )
*-

beginDocumentation()

doc ///
Key
  LCMSpaceCurves
Headline
  examples of special equidimensional (LCM) space curves
Description
  Text
    This package contains code for generating extremal, subextremal
    and general curves on certain components of small Hilbert schemes
    (restricted to LCM curves).
    
    Here is a usual method of using this package.
  Example
    R = ZZ/32003[a..d]
    I = extremalCurve(5, -3, R)  
    assert((degree I, genus I) == (5,-3))
    assert(ideal leadTerm I == ideal"a2,ab,b5,b4c6")
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  R = ZZ/32003[a..d]
  I = randomLexCurve(4, 0, R)
  assert((degree I, genus I) == (4,0))
  assert(ideal leadTerm I == ideal"a2,ac2,abc,ab2,b4")
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  R = ZZ/32003[a..d]
  I = extremalCurve(5, -3, R)  
  assert((degree I, genus I) == (5,-3))
  assert(ideal leadTerm I == ideal"a2,ab,b5,b4c6")
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  R = QQ[x,y,z,w]
  I = subextremalCurve(5, -3, R)  
  assert((degree I, genus I) == (5,-3))
  assert(ideal leadTerm I == ideal"x2,xy2,y4,y3z5")
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  needsPackage "GenericInitialIdeal"
  needsPackage "TriangleDiagrams"
  -- test of inputs to extremalCurve and subextremalCurve
  setRandomSeed 723482634782
  R = ZZ/32003[x,y,z,w]

  -- degree 1
  extremalCurve(1, -10, R)
  -- degree 2
  assert try (extremalCurve(2,0,R); false) else true
  lexgin extremalCurve(2,-1,R)
  gin extremalCurve(2,-1,R) == ideal"x2,xy,y2,xz"
  lexgin extremalCurve(2,-1,R) == ideal"x2,xy,y2,xz"

  I = extremalCurve(5, 0, R)
  D = triangleDiagram I  
  displayDiagram D

  I = subextremalCurve(5, 0, R);
  D = triangleDiagram I  
  displayDiagram D

  I = extremalCurve(4, 0, R);
  D = triangleDiagram I  
  I = subextremalCurve(4, 0, R);
  D = triangleDiagram I  

  displayDiagram D

  I = extremalCurve(4, -3, R)
  D = triangleDiagram I  
  displayDiagram D

  I = extremalCurve(7, -3, R)
  D = triangles I  
  displayDiagram D

  
  I = extremalCurve(3,-1,R)
  D = triangles I  

  subextremalCurve(1, 1, R)
  subextremalCurve(1, 0, R)
  subextremalCurve(1, 0, R)
  I = subextremalCurve(5, -3, R)  
  assert((degree I, genus I) == (5,-3))
  assert(ideal leadTerm I == ideal"x2,xy2,y4,y3z5")
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  R = ZZ/32003[x,y,z,w]
  I = degree3Type1(-3, R)
  assert((degree I, genus I) == (3,-3))
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  R = ZZ/32003[x,y,z,w]
  I = degree3Type2(-3, R)
  assert((degree I, genus I) == (3,-3))
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  R = ZZ/32003[x,y,z,w]
  I = degree3Type3(-6, 1, R)
  assert((degree I, genus I) == (3, -6))
  I = degree3Type3(-9, 2, R)
  assert((degree I, genus I) == (3, -9))
  I = degree3Type3(-9, 1, R)
  assert((degree I, genus I) == (3, -9))
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  setRandomSeed 723482634782
  kk = ZZ/32003
  S = kk[x,y,z,w]
  R = kk[y,z,w]
  IZ = ideal(y,z^3)
  F = IZ_0
  G = w^3
  IC = curveInDoublePlane(IZ, F, G, S)
  (degree IC, genus IC) == (5, 0)
  needsPackage "GenericInitialIdeal"
  gin IC
///

TEST ///
-*
  restart
  loadPackage "LCMSpaceCurves"
*-
  S = ZZ/32003[x,y,z,w]
  M = coker matrix{{x,y,z^3, w^3}}
  I = minimalSpaceCurveIdeal M
  triangles I
  assert(degree I == 2)
  assert(genus I == -3)
  res I
///

end--

restart
needsPackage "LCMSpaceCurves"
check oo


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
-- test code and assertions here
-- may have as many TEST sections as needed
///

restart
loadPackage "LCMSpaceCurves"
check oo


