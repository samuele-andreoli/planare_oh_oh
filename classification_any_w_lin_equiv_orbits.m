load "lib/dupeq.m";
load "lib/invariantTable.m";

filename := "test";
expansion_filename := Sprintf("equivalence_test/%o", filename);

PrintFile("_scratch_file.m","load \"" cat expansion_filename cat "\";" : Overwrite := true);

load "_scratch_file.m";

invariantTable := getInvariantTable(n);
orbitsTable := getOrbitsTable(n);

inequivalent_functions := AssociativeArray();
for k->v in FunctionsToTest do
    if not k in Keys(invariantTable) then
        inequivalent_functions[k] := v;
        continue;
    end if;

    representatives := invariantTable[k];

    inequiv := v;
    for r in representatives do
        orbits := orbitsTable[r];
        inequiv := [f : f in inequiv | not dupeq_with_l2_representatives(r,f,orbits)];
    end for;

    if #inequiv gt 0 then
        inequivalent_functions[k] := inequiv;
    end if;
end for;

SetOutputFile(Sprintf("inequivalent/%o", filename) : Overwrite := true);

printf "p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\nFunctionsToTest := AssociativeArray();\n", p, n;

for k->v in inequivalent_functions do
    // No need to test for equivalence, it's all x^2
    if k eq Sprintf("[ %o, %o ].NA", p^n, p^n) then
        continue;
    end if;

    printf "FunctionsToTest[\"%o\"] := %o;\n", k, v;
end for;

printf "\n";

UnsetOutputFile();

