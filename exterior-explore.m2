path = prepend("~/src/hilbert-schemes/external-packages", path)
needsPackage "Truncations"
debug needsPackage "HilbertSchemes"
--debug needsPackage("HilbertSchemes", FileName => "~/src/M2-hilbert-schemes/M2/Macaulay2/packages/HilbertSchemes.m2")
  -- debug HilbertSchemes is for findIndices, what else?

needsPackage "GroebnerStrata"
path = prepend("~/src/kristine-jones-lcm-space-curves/m2-code/", path)
needsPackage "LCMSpaceCurves"
--needsPackage "MinimalSpaceCurves"
needsPackage "TriangleDiagrams"
needsPackage "VersalDeformations"
needsPackage "GenericInitialIdeal"
needsPackage "gfanInterface"
needsPackage "TateOnProducts"

needs "ExteriorBorel.m2"

processHilbs = H -> (
  hashTable for k in keys H list k => (
    for i from 0 to #H#k-1 list (
      << "doing " << k << " and i = " << i << endl;
      I = H#k#i;
      F = groebnerFamily I;
      tandim = numcols basis(0, Hom(I, comodule I));
      J = trim groebnerStratum F;
      {H#k#i, numgens ring J, tandim, J == 0 or isPrime J, J, F}
      ))
    )

processHilbs2 = H -> (
  hashTable for k in keys H list k => (
    for i from 0 to #H#k-1 list (
      << "doing " << k << " and i = " << i << endl;
      I = H#k#i;
      F = groebnerFamily(I, AllStandard => true);
      tandim = numcols basis(0, Hom(I, comodule I));
      J = trim groebnerStratum F;
      {H#k#i, numgens ring J, tandim, J == 0 or isPrime J, J, F}
      ))
    )

quadraticForm = method()
quadraticForm RingElement := Matrix => (f) -> (
    -- return n x n matrix, skew symm if ring d is the exterior algebra.
    E := ring f;
    sub(diff(vars E, diff(transpose vars E, f)), coefficientRing E)
    )

///
A = kk[s,t]
M1 = quadraticForm J0_0
M2 = quadraticForm J0_1

M1 = quadraticForm J1_0
M2 = quadraticForm J1_1

M1 = quadraticForm J2_0
M2 = quadraticForm J2_1
rank M1
rank M2
s*sub(M1,A) + t*sub(M2,A)


Im = minors(3, s*sub(M1,A) + t*sub(M2,A))
Im = trim Im
decompose Im
///
end--

restart
load "exterior-explore.m2"
-- All of these appear to be smooth. The one in length 8 is perhaps an interesting case.
kk = ZZ/101
E = kk[a..d, SkewCommutative => true]
allss = flatten for d from 1 to 31 list SSideals(d, E);
H = partition(i -> HF(i,0,5), allss)
hilbs = processHilbs H;
hilbschemes = (keys hilbs)/(x -> (sum x, x))//sort/last
(sort keys hilbs)/(v -> #hilbs#v)//tally -- 24 have 1 borel, only one has 2.

hilbs#(first hilbschemes)
netList for k in hilbschemes list k => netList for x in hilbs#k list {x#1, dim x#4, x#2, x#3, numgens x#4}

-- The only one that seems wrong (due to using lead terms, not local equations, is {1, 4, 3, 0, 0, 0}.  I'm not
-- sure about this one.  Is there one component or 2?
-- All of these appear to be smooth. The one in length 8 is perhaps an interesting case.

restart
load "exterior-explore.m2"
kk = ZZ/101
E = kk[a..e, SkewCommutative => true]

allss = flatten for d from 1 to 31 list SSideals(d, E);
H = partition(i -> HF(i,0,5), allss)
hilbs = processHilbs2 H;
hilbschemes = (keys hilbs)/(x -> (sum x, x))//sort/last
(sort keys hilbs)/(v -> #hilbs#v)//tally -- 71 have 1 Borel, 23 have 2.

hilbs#(first hilbschemes)
netList for k in hilbschemes list k => netList for x in hilbs#k list {x#1, dim x#4, x#2, x#3, numgens x#4}
--netList for k in hilbschemes list k => netList for x in hilbs#k list print x
nonirreds = for k in hilbschemes list (
    if any(hilbs#k, x -> not x#3) then k else continue
    )
netList for k in nonirreds list k => for x in hilbs#k list (comps = decompose x#4; comps/dim)
for k in nonirreds list for x in hilbs#k list x#0
for k in hilbschemes list k => for x in hilbs#k list netList (x#5)_*

-- {1, 5, 8, 2, 0, 0, } apparently has 3 components, only one borel.
HILB = hilbs#{1,5,8,2,0,0}#0
  I = HILB#0
-- dimensions: 14, 14, 16.
  numcols basis(0, Hom(I, comodule I)) == 20
  F = HILB#5
  J = HILB#4
  numgens J
  dim J
  comps = decompose J
  
  pt0 = randomPointOnRationalVariety comps_0
  pt1 = randomPointOnRationalVariety comps_1
  pt2 = randomPointOnRationalVariety comps_2
  ev0 = map(ring F, ring F, (vars ring F) | pt0)
  ev1 = map(ring F, ring F, (vars ring F) | pt1)
  ev2 = map(ring F, ring F, (vars ring F) | pt2)
  L0 = ev0 F
  L1 = ev1 F
  L2 = ev2 F
  J0 = sub(L0, E)
  J1 = sub(L1, E)
  J2 = sub(L2, E)  

  (R1, E1) = productOfProjectiveSpaces({4}, CoefficientField => kk)
  J0' = sub(J0, vars E1)
  C0 = bgg(comodule J0', LengthLimit => 5)
  HC0 = prune HH C0
  HCT0 = prune HH dual C00
  
  J1' = sub(J1, vars E1)
  C1 = bgg(comodule J1', LengthLimit => 5)
  HC1 = prune HH C1
  HCT1 = prune HH dual C1

  J2' = sub(J2, vars E1)
  C2 = bgg(comodule J2', LengthLimit => 5)
  HC2 = prune HH C2
  HCT2 = prune HH dual C2

  M0 = coker C0.dd_-2
  M1 = coker C1.dd_-2
  M2 = coker C2.dd_-2  
  betti res M0
  betti res M1
  betti res M2
  
    
---------------------------------------------------------
-- analyze {1,5,7,1,0,0}
-- This has 2 borel's, each family has 2 components.
-- Here: find the components, their dimensions, intersections.
-- find random points on these components (and the intersection).
-- Identfy what the components really are (i.e. what do they parametrize).
HILB = hilbs#{1,5,7,1,0,0}
H1 = HILB#0
H2 = HILB#1
I1 = H1#0
I2 = H2#0

  -- analyze behavior near I1
  F1 = groebnerFamily(I1, AllStandard=>true)
  see F1
  isHomogeneous F1
  J1 = trim groebnerStratum F1
  dim J1 == 18
  C1 = decompose J1
  C1/dim//sort == {15, 18} 
    -- they both have linear lead terms, so in fact are smooth on this
    -- open set containing the point [I1].
    -- their intersection is also smooth, dim 14.
  numcols basis(0, Hom(I1, comodule I1)) == 19
  pt0 = randomPointOnRationalVariety C1_0
  pt1 = randomPointOnRationalVariety C1_1
  pt2 = randomPointOnRationalVariety (trim (C1_0 + C1_1))
  ev0 = map(ring F1, ring F1, (vars ring F1) | pt0)
  ev1 = map(ring F1, ring F1, (vars ring F1) | pt1)
  ev2 = map(ring F1, ring F1, (vars ring F1) | pt2)
  L0 = ev0 F1
  L1 = ev1 F1
  L2 = ev2 F1

  -- analyze behavior near I2
  F2 = groebnerFamily(I2, AllStandard=>true)
  see F2
  isHomogeneous F2
  J2 = trim groebnerStratum F2
  dim J2 == 18
  C1 = decompose J1
  C1/dim//sort == {15, 18} 
    -- they both have linear lead terms, so in fact are smooth on this
    -- open set containing the point [I1].
    -- their intersection is also smooth, dim 14.
  numcols basis(0, Hom(I1, comodule I1)) == 19
  pt0 = randomPointOnRationalVariety C1_0
  pt1 = randomPointOnRationalVariety C1_1
  pt2 = randomPointOnRationalVariety (trim (C1_0 + C1_1))
  ev0 = map(ring F1, ring F1, (vars ring F1) | pt0)
  ev1 = map(ring F1, ring F1, (vars ring F1) | pt1)
  ev2 = map(ring F1, ring F1, (vars ring F1) | pt2)
  L0 = ev0 F1
  L1 = ev1 F1
  L2 = ev2 F1
  
  S = kk[a..e]
  P0 = sub(L0, S)
  P1 = sub(L1, S)
  P2 = sub(L2, S)
  HF(P0, 0, 10)
  HF(P1, 0, 10)
  HF(P2, 0, 10)

  (R1, E1) = productOfProjectiveSpaces({4}, CoefficientField => kk)
  L0' = sub(L0, vars E1)
  C0 = bgg(comodule L0', LengthLimit => 5)
  HC0 = prune HH C0
  HCT0 = prune HH dual C0

  L1' = sub(L1, vars E1)
  C1 = bgg(comodule L1', LengthLimit => 5)
  HC1 = prune HH C1
  HCT1 = prune HH dual C1

  L2' = sub(L2, vars E1)
  C2 = bgg(comodule L2', LengthLimit => 5)
  HC2 = prune HH C2
  HCT2 = prune HH dual C2
  
-- 
numgens ring J1b == 24
see C1b_0 -- this one is codim 6 (dim 18), rational (linear lead terms)
see C1b_1 -- this one is codim 9 (dim 15), rational (linear lead terms)
see trim sum C1b -- codim 10 (dim 14)

F2a = groebnerFamily(I2)
F2b = groebnerFamily(I2, AllStandard=>true)
see F2a
see F2b
see F1b
isHomogeneous F1b
J2b = trim groebnerStratum F2b
decompose J2b


J1 = H1#4
F1 = H1#5
J2 = H2#4
F2 = H2#5

borels = {ideal (a*d, a*c, a*b, b*d*e, b*c*e, b*c*d), ideal (b*c, a*c, a*b, b*d*e, a*d*e)}
F = groebnerFamily borels#0
F1 = groebnerFamily borels#1
F2 = groebnerFamily(borels#1, AllStandard => true)
see F1
see F2
isHomogeneous F1
isHomogeneous F2
numcols basis(0, Hom(module I1, comodule I1))
  -- Now let's analyze the lex point.
  use ring F2
  A1 = coefficientRing ring F2
  A1' = A1[t_0, gens A1]
  R2' = A1'[a,b,c,d,e,SkewCommutative=>true]
  F2' = sub(F2, R2')
  F2'' = ideal prepend(F2'_0 - b*c + t_0 * (b*c), drop(F2'_*, 1))
  E1 = sub(basis(1, R), ring F2'')
  E2 = sub(basis(2, R), ring F2'')
  IF2 = ideal(F2''_0, F2''_1, F2''_2) * ideal E1 + ideal(F2''_3, F2''_4)
  use ring IF2
  (mons, cfs) = coefficients(gens IF2, Variables => {a,b,c,d,e})
  see F1
  A1 = coefficientRing ring F1
  R1 = 
  IF2 = F2_0 * ideal E1 + ideal(F2_1, F2_2, F2_3, F2_4)

-- analyze {1,5,7,2,0,0}
HILB = hilbs#{1,5,7,2,0,0}
netList oo
H1 = HILB#0
H2 = HILB#1
J1 = H1#4
F1 = H1#5
J2 = H2#4
F2 = H2#5
I1 = H1#0
I2 = H2#0

  (R1, E1) = productOfProjectiveSpaces({4}, CoefficientField => kk)
  CJ2 = decompose J2

  pt = randomPointOnRationalVariety first CJ2
  F2' = sub(F2, (vars R) | pt)
  HF(F2', 0, 5)
  F2' = sub(F2', vars E1)
  HF(F2', 0, 5)
  M = comodule F2'
  HF(M, 0, 5)
  C = bgg(M, LengthLimit => 5)
  prune HH C
  for i from -2 to 0 list rank C.dd_i

  pt = randomPointOnRationalVariety last CJ2
  F2' = sub(F2, (vars R) | pt)
  HF(F2', 0, 5)
  F2' = sub(F2', vars E1)
  HF(F2', 0, 5)
  M = comodule F2'
  HF(M, 0, 5)
  C = bgg(M, LengthLimit => 5)
  HF((prune HH C)#-3, -10, 10)
  for i from -2 to 0 list rank C.dd_i

  see F2
  KK = frac ((ring CJ2_0)/CJ2_0)
  T = KK[a..e, SkewCommutative => true]
  F2T = sub(F2, T)
  (R1, E1) = productOfProjectiveSpaces({4}, CoefficientField => KK)
  F2T' = sub(F2T, vars E1)
  C1 = bgg(comodule F2T', LengthLimit => 5)
  HC1 = prune HH C1

-- analyze {1,5,9,3,0,0}
HILB = hilbs#{1,5,9,3,0,0}
H1 = HILB#0
H2 = HILB#1
J1 = H1#4
F1 = H1#5
J2 = H2#4
F2 = H2#5
see F2
E1 = sub(basis(1, R), ring F2)
E2 = sub(basis(2, R), ring F2)
IF2 = F2_0 * ideal E1 + ideal(F2_1, F2_2, F2_3, F2_4)






-- 6 variables
restart
load "exterior-explore.m2"
kk = ZZ/101
R = kk[a..f, SkewCommutative => true]

allss = flatten for d from 1 to 31 list SSideals(d, R);
H = partition(i -> HF(i,0,6), allss)
(values H)/(x -> #x)//tally
select(keys H, k -> #H#k == 7)
hilbs = processHilbs H;
hilbschemes = (keys hilbs)/(x -> (sum x, x))//sort/last
(sort keys hilbs)/(v -> #hilbs#v)//tally -- 71 have 1 Borel, 23 have 2.

borels = H#{1, 6, 10, 4, 0, 0, 0}
Ha = new HashTable from {{1, 6, 10, 4, 0, 0, 0} => H#{1, 6, 10, 4, 0, 0, 0}}
processHilbs Ha

F = groebnerFamily borels#0
F = groebnerFamily(borels#0, AllStandard => true)
F = groebnerFamily(borels#1, AllStandard => true)
F = groebnerFamily(borels#2, AllStandard => true)









--IF2 = F2_0 * ideal E2 + ideal(F2_1, F2_2, F2_3, F2_4) * ideal E1
(mons, cfs) = coefficients(gens IF2, Variables => {a,b,c,d,e})
cfs = sub(transpose cfs, ring J2)
  doSingleIdeal = (I) -> (
      F = groebnerFamily I;
      << see F << endl;
      J = trim groebnerStratum F;
      assert isHomogeneous F;
      tandim = numcols basis(0, Hom(I, comodule I));
      {numgens ring J, tandim, codim J, isPrime J, J, F}
      )
  doSS = (ss) -> (
    netList for i from 0 to #ss-1 list doSingleIdeal ss#i
    )



ss = SSideals(5,R)
ss = SSideals(6,R)
ss = SSideals(7,R)
ss = SSideals(8,R) -- (ad, ac, ab, bcd) is only codim 1 in Hilbert scheme.
ss = SSideals(9,R)
ss = SSideals(10,R)
ss = SSideals(11,R)
ss = SSideals(12,R)
ss = SSideals(13,R)
ss = SSideals(14,R)
ss = SSideals(15,R)
  
  ss = SSideals(6,R)
  ss = drop(SSideals(5,R), 1)
  doSingleIdeal = (I) -> (
      F = groebnerFamily I;
      << see F << endl;
      J = trim groebnerStratum F;
      assert isHomogeneous F;
      tandim = numcols basis(0, Hom(I, comodule I));
      {numgens ring J, tandim, codim J, isPrime J, J, F}
      )
  doSS = (ss) -> (
    netList for i from 0 to #ss-1 list doSingleIdeal ss#i
    )
  doSS(drop(SSideals(5,R), 1))
  doSS (SSideals(7,R))
  doSS (SSideals(8,R))
  doSS (SSideals(9,R)) -- first one looks like it isn't complete...
  doSS (SSideals(10,R)) 
  doSS (SSideals(11,R)) 
  doSS (SSideals(12,R)) 
  doSS (SSideals(13,R)) 
  doSS (SSideals(14,R)) 

  doSingleIdeal ((SSideals(12, R))#3) -- first with 2 components (although maybe these are each part of one component?
  J = oo_4
  F = ooo_5
  CJ = decompose J
  intersect CJ == J
  J1 = eliminate({t_20, t_15, t_14, t_10, t_5, t_4, t_25, t_24}, J)
  CJ1 = decompose J1
  intersect CJ1 == J1 -- true.

  doSingleIdeal ((SSideals(13, R))#3) -- 2 components (although maybe these are each part of one component?
  J = oo_4
  F = ooo_5
  CJ = decompose J
  intersect CJ == J
  J1 = eliminate({t_11, t_12, t_6, t_23, t_18, t_24}, J)
  CJ1 = decompose J1
  intersect CJ1 == J1 -- true.

  doSingleIdeal ((SSideals(14, R))#1) -- 2 components (although maybe these are each part of one component?
  J = oo_4
  F = ooo_5
  see J
  see F
  CJ = decompose J
  J1 = eliminate({t_13, t_6, t_5, t_20, t_19}, J)
  CJ1 = decompose J1
  intersect CJ1 == J1 -- true.
