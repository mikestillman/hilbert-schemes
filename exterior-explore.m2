path = prepend("~/src/hilbert-schemes/external-packages", path)
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
R = kk[a..e, SkewCommutative => true]

allss = flatten for d from 1 to 31 list SSideals(d, R);
H = partition(i -> HF(i,0,5), allss)
hilbs = processHilbs H;
hilbschemes = (keys hilbs)/(x -> (sum x, x))//sort/last
(sort keys hilbs)/(v -> #hilbs#v)//tally -- 71 have 1 Borel, 23 have 2.

hilbs#(first hilbschemes)
netList for k in hilbschemes list k => netList for x in hilbs#k list {x#1, dim x#4, x#2, x#3, numgens x#4}
netList for k in hilbschemes list k => netList for x in hilbs#k list print x

-- analyze {1,5,7,1,0,0}
HILB = hilbs#{1,5,7,1,0,0}
H1 = HILB#0
H2 = HILB#1
J1 = H1#4
F1 = H1#5
J2 = H2#4
F2 = H2#5
I1 = H1#0
I2 = H2#0

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
