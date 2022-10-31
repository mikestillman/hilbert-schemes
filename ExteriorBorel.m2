borelBigger = (m,n) -> (
    if degree m != degree n then return false;
    d := sum degree m;
    return all(d, i -> (support m)_i >= (support n)_i))
    
minimals = V -> (
    nonMins := {};
    for v in V do (
	for w in V do ( if v!=w and not member(w,nonMins) and borelBigger(v,w) then 
	    (nonMins = append(nonMins,v); break)));
    mins := V;
    for v in nonMins do mins = delete(v,mins);
    return mins)

SSideals = (c,E) -> (
    kk := coefficientRing E;
    E' := kk[gens E, SkewCommutative=> true,MonomialOrder => Lex];
    iota := map(E,E', gens E);
    LIST := {(ideal gens E', sub(1,E'))};
    for j in 2..c do (
	previous := LIST;
	next := {};
	for II in LIST do (
	    I := II_0;
	    m := II_1;
	    allGens := flatten entries mingens I;
	    activeGens := select(allGens, u-> (first degree u >= first degree m)); 
	    degreesActiveGens := unique apply(activeGens, u -> first degree u);
	    activeGens = flatten apply(degreesActiveGens, d -> minimals select(activeGens, u -> first degree u == d));
	    activeGens = select(activeGens, u -> (first degree u > first degree m) or (first degree u == first degree m and u >m));
	    for u in activeGens do (
		J := ideal mingens (ideal delete(u,allGens) + u*(ideal gens E'));
		next = append(next, (J, u));
		));
	LIST = unique next;
	);
    return unique apply(LIST, I-> iota(I_0)))

end--


restart
path = prepend("./external-packages", path)
debug needsPackage "HilbertSchemes"
needs "ExteriorBorel.m2"


kk = ZZ/32003;
n = 5;
S = kk[x_1..x_n];
ss = SSideals(17,S)
netList ss
HF(ss_0, 0, 5)

E = kk[x_1..x_n, SkewCommutative => true]
ss = SSideals(17,E)
netList ss
HF(ss_0, 0, 5)
matrix for s in ss list HF(s, 0, 5)

numcols basis(0, Hom(ss_0, comodule ss_0))
for s in ss list numcols basis(0, Hom(s, comodule s))

F = groebnerFamily ss_2
see F
isHomogeneous F
describe ring F
