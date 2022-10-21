--Hilbert scheme structure for (d,g) = (5,2) in P^3.

restart
path = prepend("~/src/hilbertschemes-mike-irena-ritvik/external-packages", path)
needsPackage "Truncations"
debug needsPackage "HilbertSchemes"
--debug needsPackage("HilbertSchemes", FileName => "~/src/M2-hilbert-schemes/M2/Macaulay2/packages/HilbertSchemes.m2")
  -- debug HilbertSchemes is for findIndices, what else?
needsPackage "GroebnerStrata"
--path = prepend("~/src/kristine-jones-lcm-space-curves/m2-code/", path)
needsPackage "LCMSpaceCurves"
--needsPackage "MinimalSpaceCurves"
needsPackage "TriangleDiagrams"
needsPackage "VersalDeformations"
needsPackage "GenericInitialIdeal"
needsPackage "gfanInterface"

S = ZZ/101[a..d]

  Bs = spaceCurveBorels(5, 2, S, Filter=>false) -- first is always lex.
  
-- components are named by dim, e.g. C35.  General elements are written as e.g. I35 (or I35a, ...)
  macaulayVector Bs_0 -- {9,5}
  MtoA macaulayVector Bs_0 -- {4,5}
  
  Bs/dimHilbTangentSpace -- {35, 35, 39, 41, 43, 39, 37, 41, 36, 41, 25, 24, 20}
  netList Bs -- 
  use S
  Bs/(i -> saturate(i, c))//unique

-- a list of the components:
-- 1. C35 (Lex). plane quintic + 4 free points.
--   contains the first 10 (#0 - #9).
  I35 = randomPtOnLex(new Partition from {9,5}, S)
  betti res I35 -- in(I35) = Bs_9

-- 2. C20 (or maybe C20a). 
--    Borels in gfan of I20: {6, 8, 10, 11, 12}
--    #12 is smooth.  The first 3 are on C35 
  C = res ideal(a^2, a*b^2, b^3)
  C.dd_2 -- to determine the correct numbers for the next line:
  M = random(S^{-2,-3,-3}, S^{-4,-4})
  I20 = minors(2, M);
  gfan I20;
  select(oo/first/monomialIdeal, isBorel)
  sort findIndices(oo/saturate, Bs)
  dimHilbTangentSpace minors(2, M) == 20

-- 3. C23a: line + plane quartic (meeting at a point) + free point
  -- {5, 6, 8, 10, 11}
  -- first choose the intersection point:
  p1 = randomPoint S
  line = ideal ((super basis(1, p1)) * random(S^3, S^2)) -- line containing p1
  plane = ideal ((super basis(1, p1)) * random(S^3, S^1)) -- plane containing p1
  quartic = trim(plane + ideal ((super basis(4, p1)) * random(S^34, S^1))) -- line containing p1
  I23a = intersect(line, quartic, randomPoint S)
  HP I23a
  betti res I23a
  monomialIdeal leadTerm I23a
  gfan I23a;
  select(oo/first/monomialIdeal, isBorel)
  findIndices(oo/saturate, Bs)
  sort unique oo
  dimHilbTangentSpace I23a == 23
  
-- 4.  Extremal component
-- C21: 
-- Borels: {6,10} (so intersects C23a, C35, C20)
  I21 = extremalCurve(5, 2, S) -- this has 2 Borels: 6, 10. 
  dimHilbTangentSpace I21 == 21
  select((gfan I21)/first/monomialIdeal, isBorel)
  findIndices(oo, Bs)
  betti res I21
  
-------------------------------------------------
-- Test local structure at the various Borel's --
-------------------------------------------------
  checkComparisonTheorem Bs_12 -- this one is smooth
  (F,R,G,C) = localHilbertScheme(gens Bs_12, Verbose => 4, HighestOrder => 12);
  sum G

  checkComparisonTheorem Bs_11 -- 
  (F,R,G,C) = localHilbertScheme(gens Bs_11, Verbose => 4, HighestOrder => 12);
  IG = trim ideal sum G 
  primaryDecomposition IG  -- components of dimension 20, 23. i.e. C20a, C23.

    --let's get 2 ideals on these components.
    -- first is on C23a, second on C20.
    kk = coefficientRing S
    T = kk (monoid ring sum F)
    IG = trim sub(ideal sum G, T)
    CIG = primaryDecomposition IG
    ptA = randomPointOnRationalVariety CIG_0
    ptB = randomPointOnRationalVariety CIG_1
    IA = ideal sub(sum F, sub(ptA, S))
    betti res IA
    IB = ideal sub(sum F, sub(ptB, S))
    netList primaryDecomposition IA -- line, plane quartic (meeting at some point) + free point. (reduced)

    -- what is IB?
    betti res IB -- CM

  checkComparisonTheorem truncate(4, Bs_10) -- 
  (F,R,G,C) = localHilbertScheme(gens truncate(4, Bs_10), Verbose => 4, HighestOrder => 5);
  IG = trim ideal sum G
  primaryDecomposition IG  -- appears we have 4 components through here, dims 23, 21, 20, 20 (last non-reduced?)

  (F,R,G,C) = localHilbertScheme(gens truncate(4, Bs_10), Verbose => 4, HighestOrder => 7);
  IG = trim ideal sum G
  decompose IG
  CIG = primaryDecomposition IG  -- appears we have 4 components through here, dims 23, 21, 20, 20 (last non-reduced?)
  -- it appears that C20b is non-reduced, but is embedded as divisor in C21.
  -- Question: how to identify C20b...?

  J20b = trim radical CIG_3  
  T = kk (monoid ring J20b)
  U = T (monoid S)
  J20b = sub(J20b, T)
  pt20b = randomPointOnRationalVariety J20b
  
  phi = map(S, U, (vars S) | pt20b)
  I20b = saturate ideal phi sub(sum F, U)
  HP I20b -- WRONG... Maybe we need to go higher in degree.
  betti res I20b
  psi = map(S, S, random(S^1, S^{-1,-1,-1,-1}))
  select((gfan trim psi I20b)/first/monomialIdeal, isBorel)
  findIndices(oo/saturate, Bs)
  sort unique oo
  dimHilbTangentSpace I23a == 23
  
  -- extremal component
  IE = extremalCurve(5, 2, S) -- this has 2 Borels: 6, 10. 
  dimHilbTangentSpace IE
  select((gfan IE)/first/monomialIdeal, isBorel)
  findIndices(oo, Bs)
  F = groebnerFamily Bs_10
  see F
  J = groebnerStratum F;
  J = trim J;
  J1 = ideal select(J_*, f -> sum first exponents f != 1)
  see J1
  sum decompose J1

  pt0 = randomPointOnRationalVariety (decompose J)_0
  pt1 = randomPointOnRationalVariety (decompose J)_1
  T = ring J1
  I1 = (map(S, ring F, vars S | pt0)) F
  I2 = (map(S, ring F, vars S | pt1)) F
  C1 = decompose I1
  C2 = decompose I2
  decompose sum C1 -- I1: one line + plane quartic singular, intersect at one point (and it is on the quartic),
    -- and this point is embedded.
    C1_0 -- line
    C1_1 -- smooth plane quartic
      singC11 = trim(C1_1 + minors(codim C1_1, jacobian C1_1))
      codim singC11 == 4 
    -- where do they meet?
    pt = trim(C1_0 + ideal(C1_1_0)) -- plane and line meet at a point.  Is this point in the quartic
    (gens C1_1) % pt -- yes
    trim(C1_0 + C1_1) -- this is the same point.
    -- So I1: union of a line and a plane quartic meeting at one point.  line: 4 plane: 3, quartic through point: 14-1
    dimHilbTangentSpace I1 == 23 -- maybe quite singular? ie non-reduced.
    
    -- Now for I2:
    C2_0 -- line
    C2_1 -- smooth plane quartic
      singC21 = trim(C2_1 + minors(codim C2_1, jacobian C2_1))
      codim singC21 == 4 
    -- where do they meet?
    pt = trim(C2_0 + ideal(C2_1_0)) -- plane and line meet at a point.  Is this point in the quartic
    (gens C2_1) % pt -- NO!
    trim(C2_0 + C2_1) -- these two components do not intersect.
    -- So I2: skew union of a line and a plane quartic: plane quartic 3 + 14 + 4 = 21
    -- I think this one is the extremal curve locus?
    dimHilbTangentSpace I2 == 21
    
  decompose sum C2  
  C1_0
  C1_1  
  oo_1
  
  singI1 = trim(I1 + minors(2, jacobian I1))
  radical singI1 -- 2 points

  betti res randomPtOnLex(new Partition from {9,5}, S)

  -- Free resolution/Groebner strata
  viewHelp GroebnerStrata
  F = groebnerFamily Bs_9
  see F
  J = groebnerStratum F;
  J = trim J;
  codim J -- 69
  select(J_*, f -> sum first exponents leadMonomial f == 1);
  codim ideal leadTerm ideal oo 
  codim oo -- codim 63
  J1 = ideal select(J_*, f -> sum first exponents leadMonomial f > 1)
  codim J1
  assert isPrime J1 -- this is Lex component.
  dim J == 35

  F = groebnerFamily Bs_10    
  see F
  J = groebnerStratum F;
  J = trim J;
  codim J -- 42
  Jlin = ideal select(J_*, f -> sum first exponents leadMonomial f == 1);
  codim Jlin -- 41
  J1 = ideal select(J_*, f -> sum first exponents leadMonomial f > 1)
  codim J1
  CJ1 = primaryDecomposition J1 -- 2 prime components
  radical J1 == J1
  CJ = CJ1/(j -> trim(Jlin + j));
  CJ/dim -- {22, 21}
  CJ/codim
  CJ1/codim/(c -> numgens ring Jlin - codim Jlin - c) -- dims {21, 20} hmmm, no!
  (gens J) % CJ_0
  (gens J) % CJ_1
  pt0 = randomPointOnRationalVariety CJ_0
  pt1 = randomPointOnRationalVariety CJ_1
  ev0 = map(S, ring F, (vars S) | sub(pt0, S))
  ev1 = map(S, ring F, (vars S) | sub(pt1, S))
  I21a = ev0 F
  select((gfan I21a)/first/monomialIdeal/saturate, isBorel)
  findIndices(oo, Bs)
  primaryDecomposition(I21a)

  I22a = ev1 F
  select((gfan I22a)/first/monomialIdeal/saturate, isBorel)
  findIndices(oo, Bs)
  primaryDecomposition(I22a) -- line and plane quintic, do not meet.
  saturate trim sum oo == 1 
  
  F = groebnerFamily Bs_11
  see F
  J = groebnerStratum F;
  J = trim J;
  codim J -- 32
  isPrime J
  dim J == 23

  F = groebnerFamily Bs_12
  see F
  J = groebnerStratum F;
  J = trim J;
  codim J -- 17
  isPrime J 
  dim J == 20
  

  

  checkComparisonTheorem truncate(6, Bs_4) -- 
  (F,R,G,C) = localHilbertScheme(gens truncate(6, Bs_4), Verbose => 4, HighestOrder => 2);
  (F,R,G,C) = versalDeformation(F,R,G,C, Verbose => 4, HighestOrder => 3);
  
  elapsedTime (F,R,G,C) = localHilbertScheme(gens truncate(6, Bs_4), Verbose => 4, HighestOrder => 4);  
  IG = trim ideal sum G
  primaryDecomposition IG 
