--Hilbert schemes of small Hilbert schemes in P^3 or P^4...

restart
needsPackage "Truncations"
debug needsPackage("HilbertSchemes", FileName => "~/src/M2-hilbert-schemes/M2/Macaulay2/packages/HilbertSchemes.m2")
  -- debug HilbertSchemes is for findIndices, what else?
needsPackage "GroebnerStrata"
path = prepend("~/src/kristine-jones-lcm-space-curves/m2-code/", path)
needsPackage "LCMSpaceCurves"
needsPackage "MinimalSpaceCurves"
needsPackage "TriangleDiagrams"
needsPackage "VersalDeformations"
needsPackage "GenericInitialIdeal"
needsPackage "gfanInterface"
-- small situations
S = ZZ/101[a..d]
Bs = spaceCurveBorels(3, 0, S, Filter=>false) -- first is always lex.
Bs/dimHilbTangentSpace
Bs_2
checkComparisonTheorem Bs_2
checkComparisonTheorem Bs_1
checkComparisonTheorem truncate(3, Bs_0)
localHilbertScheme(gens Bs_0)
localHilbertScheme(gens Bs_1)

  (F,R,G,C) = localHilbertScheme(gens Bs_1, Verbose => 4);
  see ideal sum F
  see ideal sum G
  sum R
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

  (F,R,G,C) = localHilbertScheme(gens Bs_2, Verbose => 4);
  see ideal sum F
  see ideal sum G
  sum R
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

  (F,R,G,C) = localHilbertScheme(gens truncate(3, Bs_0), Verbose => 4, HighestOrder => 30);
  see ideal sum F
  see ideal sum G
  sum R
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

-- degree 4, genus 2
Bs = spaceCurveBorels(4, 2, S, Filter=>false) 
  MtoA macaulayVector Bs_0 == {1, 4} -- 1 point + deg 4 curve
  Bs/dimHilbTangentSpace -- smooth, one component.


  checkComparisonTheorem Bs_3
  checkComparisonTheorem truncate(4, Bs_1)
  (F,R,G,C) = localHilbertScheme(gens truncate(4, Bs_1), Verbose => 4, HighestOrder => 30);
  see ideal sum G
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

-- degree 4, genus 1
-- my "guess": 2 components: lex, CI(2,2).
-- BUT: could there be another component through Bs_1? (or perhaps an embedded component?
Bs = spaceCurveBorels(4, 1, S, Filter=>false) 
  MtoA macaulayVector Bs_0 == {2, 4} -- 2 points, deg 4 curve
  Bs/dimHilbTangentSpace -- {23, 27, 24, 16}

  hf0 = for i from 1 to 6 list hilbertFunction(i, Bs_0)
  ids0 = hilbertRepresentatives(S, hf)
  select(ids0, i -> i == monomialIdeal saturate i)
  ids0/dimHilbTangentSpace

  hf0 = for i from 1 to 5 list hilbertFunction(i, Bs_1)
  ids0 = hilbertRepresentatives(S, hf0)
  ids0 = select(ids0, i -> HP i == HP Bs_1)
  select(ids0, i -> i != monomialIdeal saturate i)
  ids0/dimHilbTangentSpace

  hf0 = for i from 1 to 5 list hilbertFunction(i, Bs_2)
  ids0 = hilbertRepresentatives(S, hf0);
  ids0 = select(ids0, i -> HP i == HP Bs_2)
  select(ids0, i -> i != monomialIdeal saturate i)
  satids0 = select(ids0, i -> i == monomialIdeal saturate i)
  satids0/dimHilbTangentSpace


  -- this one seems to take quite a while...
  checkComparisonTheorem Bs_1
  checkComparisonTheorem truncate(4, Bs_1)
  (F,R,G,C) = localHilbertScheme(gens truncate(4, Bs_1), Verbose => 4, HighestOrder => 6);
  (F,R,G,C) = liftDeformation(F,R,G,C, Verbose => 4, DegreeBound => 7);
  (F,R,G,C) = liftDeformation(F,R,G,C, Verbose => 4, DegreeBound => 8);
  (F,R,G,C) = liftDeformation(F,R,G,C, Verbose => 4, DegreeBound => 9);
  see ideal sum G
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

  -- this is a smooth point, it appears...
  checkComparisonTheorem Bs_3 
  (F,R,G,C) = localHilbertScheme(gens Bs_3, Verbose => 4, HighestOrder => 30);
  see ideal sum G
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

  -- this is on 2 components, both I think smooth.
  checkComparisonTheorem Bs_2
  (F,R,G,C) = localHilbertScheme(gens Bs_2, Verbose => 4, HighestOrder => 30);
  IG = ideal sum G
  trim IG
  primaryDecomposition IG
  T = ring sum F
  transpose((sum F) * (sum R)) + (sum C) * (sum G) == 0 -- true in polynomial case...

  CI = ideal random(S^1, S^{-2,-2})
  gfan CI

  F = groebnerFamily(Bs_2)
  see F
  J = groebnerStratum F
  gens gb J
  see ideal oo
  -- now find a point on this, and get the ideal.
  -- see if it is on Lex...
  leadTerm randomPtOnLex(new Partition from {6,4}, S)
  F = groebnerFamily(Bs_1)
  J = groebnerStratum F
  gens gb J
  J = trim ideal gens gb J
  assert isPrime J -- so, the subset of Hilb which goes to Bs_1 via grevlex is irreducible.  Dim = 22.
    -- i.e. a divisor's worth has B1 as a grevlex sync.

-- Example, curves of degree 5
S = ZZ/101[a..d]
  -- {0,5}
  Bs = spaceCurveBorels(5, 6, S, Filter=>false) -- first is always lex.
  MtoA macaulayVector Bs_0 -- {0,5} one Borel
  Bs/dimHilbTangentSpace
  -- {1,5}
  Bs = spaceCurveBorels(5, 5, S, Filter=>false) -- first is always lex.
  MtoA macaulayVector Bs_0 -- {1,5}
  Bs/dimHilbTangentSpace -- smooth

  -- {2,5}
  Bs = spaceCurveBorels(5, 4, S, Filter=>false) -- first is always lex.
  MtoA macaulayVector Bs_0 -- 
  Bs/dimHilbTangentSpace -- {29, 33, 29}, not smooth.
  netList Bs -- all are on Lex.
  -- is Bs_1 irreducible on Hilb?
  checkComparisonTheorem truncate(5,Bs_1)
  (F,R,G,C) = localHilbertScheme(gens truncate(5, Bs_1), Verbose => 4, HighestOrder => 4);
  see ideal sum G
  IG = trim ideal sum G
  assert isPrime IG
  (F,R,G,C) = liftDeformation(F,R,G,C, Verbose => 4, DegreeBound => 5);
  (F,R,G,C) = liftDeformation(F,R,G,C, Verbose => 4, DegreeBound => 6);
  -- NOT QUITE CLEAR TO ME: Bs_1 is irreducible on Hilb.

  -- {3,5}
  Bs = spaceCurveBorels(5, 3, S, Filter=>false) -- first is always lex.
  MtoA macaulayVector Bs_0 -- 
  Bs/dimHilbTangentSpace -- {32, 32, 36, 36, 33, 32, 20} not smooth.
  netList Bs -- 
  -- one component: (plane quartic) + line meeting in a point (dim: 3 + 3 + 3 (plane) + (15-1)
  M = random(S^{-2,-2,-4}, S^{-3,-5})
  I = minors(2, M)
  trim sum decompose I
  intersect oo == I

  select((gfan I)/first/monomialIdeal, isBorel)
  netList Bs

  checkComparisonTheorem truncate(3,Bs_4)
  (F,R,G,C) = localHilbertScheme(gens truncate(3, Bs_4), Verbose => 4, HighestOrder => 12);

  checkComparisonTheorem truncate(6,Bs_2)
  (F,R,G,C) = localHilbertScheme(gens truncate(6, Bs_2), Verbose => 4, HighestOrder => 4);
  assert isPrime ideal sum G

  -- {4,5}
  -- see d5g2.m2
