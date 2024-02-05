load "lib/planar.m";

/* Expansion search parameters. Modify here */

p := 3;
n := 6;

// Dimension of the subfield for the coefficients
m := 6;
assert n mod m eq 0;

// Monomial # for the expansion
l := 1;

// Starting monomial for the expansion
f := 2;

/* End of user modifiabile section */

SetOutputFile(Sprintf("./expansions/p%o_n%o_m%o_l%o_x%o", p, n, m, l, f));

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

S := {x : x in GF(p^m) | not IsZero(x)};
E := [e : e in [3..p^n] | weight(p, e) eq 2 and e ne f];

CoeffSpace := CartesianPower(S, l);
ExpSpace   := CartesianPower(E, l);

SearchSpace := CartesianProduct(CoeffSpace, ExpSpace);

// GeneratedPlanarFunctions = [];
printf "p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\n", p, n;
printf "Functions := [";

for s in SearchSpace do
    c := s[1];
    e := s[2];

    candidate := [F!0: x in [1..p^n]];
    candidate[f+1] := F!1;
    
    for i in [1..l] do
        candidate[e[i]+1] := c[i];
    end for;

    candidate := R!candidate;

    if isPlanarDOPoly(candidate) then
        printf "%o,", candidate;
    end if;
end for;

printf("];");

UnsetOutputFile();