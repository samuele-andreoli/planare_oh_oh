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

SetOutputFile(Sprintf("./expansions/p%o_n%o_x%o_l%o_m%o", p, n, f, l, m));

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

S := {x : x in GF(p^m) | not IsZero(x)};

// DO poly exponents. The check i ge j is redundant since we use a set,
// but might as well have it explicit.
E := {p^i + p^j : i,j in [0..n-1] | i ge j};
Exclude(~E, f);

CoeffSpace := CartesianPower(S, l);
ExpSpace   := Subsets(E, l);

SearchSpace := CartesianProduct(CoeffSpace, ExpSpace);

// GeneratedPlanarFunctions = [];
printf "p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\n", p, n;
printf "Functions := [";

FFs:=getFFs(F);

for e in ExpSpace do
    e := [ei : ei in s[2]];

    for c in CoeffSpace do
        candidate := [Zero(F): x in [1..p^n]];
        candidate[f+1] := One(F);
        
        for i in [1..l] do
            candidate[e[i]+1] := c[i];
        end for;

        candidate := R!candidate;

        if fastIsPlanarDOPoly(candidate,FFs) then
            printf "%o,", candidate;
        end if;
    end for;
end for;

printf("];");

UnsetOutputFile();
