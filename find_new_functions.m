load "lib/ccz_equivalence.m";
load "lib/invariantTable.m";
load "lib/semifields.m";
load "lib/dupeq.m";

filename := "test";
n := 6;

expansion_filename := Sprintf("expansions/%o", filename);

PrintFile("_scratch_file.m","load \"" cat expansion_filename cat "\";" : Overwrite := true);

load "_scratch_file.m";

gt_invariant_table := getInvariantTable(n);

to_test_for_equivalence := AssociativeArray();

for f in Functions do
    N:=[0,0];
    if isDOPolynomial(f) then
        N:=Nuclei(f, One(F));
    end if;

    order := "NA";
    if (n gt 6) or ((n eq 6) and not N in {[p^n,p^n],[p^2,p^2]}) then
        order := AutomoriphismGroupOrderFromFunction(f);
    end if;

    key := Sprintf("%o.%o", N, order);

    if not key in Keys(gt_invariant_table) then
        printf "unknown combination of invariants %o for f=%o\n\n", key, f;
        gt_invariant_table[key] := f;
    end if;

    if not key in Keys(to_test_for_equivalence) then
        to_test_for_equivalence[key] := [];
    end if;

    Append(~to_test_for_equivalence[key], f);
end for;

SetOutputFile(Sprintf("equivalence_test/%o", filename));

printf "p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\nFunctionsToTest := [\n", p, n;

for k->v in to_test_for_equivalence do
    // No need to test x^2 for inequivalence
    if k eq Sprintf("[ %o, %o ].NA", p^n, p^n) then
        continue;
    end if;

    if k in Keys(gt_invariant_table) then
        v := gt_invariant_table[k] cat v;

    printf "    %o,", v;
end for;

printf "];\n";

UnsetOutputFile();
