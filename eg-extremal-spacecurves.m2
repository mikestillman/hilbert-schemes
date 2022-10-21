restart
path = append(path, "~/src/kristine-jones-lcm-space-curves/m2-code")
needsPackage ("HilbertSchemes", FileName => "~/src/M2-hilbert-schemes/M2/Macaulay2/packages/HilbertSchemes.m2")
needsPackage "LCMSpaceCurves"
needsPackage "SpaceCurves"
S = ZZ/32003[a,b,c,d]
I = extremalCurve(5, 0, S)
B = monomialIdeal leadTerm I
hilbertPolynomial(B, Projective => false)
t = (ring oo)_0

Bs = spaceCurveBorels(5, 0, S) -- 12.
Bs = spaceCurveBorels(5, 0, S, Filter => false) -- 38 total
 -- 26 of these are on the lex component, remaining 12 are not.
for b in Bs list if numgens b == 4 then b else continue
netList oo
needsPackage "gfanInterface"
gfanI = gfan(I);
extremalBs = select(gfanI/first/monomialIdeal, isBorel)
Bs/(I -> trim sub(I, {c => 1, d => 1}))//tally
Bs/ext0


o37/first//tally
viewHelp SpaceCurves

A = ZZ/32003[s,t]
phi = map(A, S, random(A^1, A^{4:-5}))
IC = ker phi
leadTerm IC
HH^0(sheaf Hom(IC, comodule IC)) == 20
gfanC = gfan IC
borelsC = select(gfanC/first/monomialIdeal/saturate, isBorel)
#borelsC

H1I = HH^1((sheaf module I)(>=-10))
H1C = HH^1((sheaf module IC)(>=-10))
for d from -10 to 10 list hilbertFunction(d, H1I)
for d from -10 to 10 list hilbertFunction(d, H1C)
