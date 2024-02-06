load "lib/ccz_equivalence.m";
load "lib/invariantTable.m";
load "lib/semifields.m";
load "lib/dupeq.m";

filename := "test";
expansion_filename := Sprintf("expansions/%o.m", filename);

PrintFile("_scratch_file.m","load \"" cat expansion_filename cat "\";" : Overwrite := true);

load "_scratch_file.m";

gt_invariant_table := getInvariantTable();

to_test_for_equivalence := AssociativeArray();
for k->v in gt_invariant_table do
    to_test_for_equivalence[k] := [v];
end for;

e:=One(F);
subfields,sizes:=PrecomputeSubfields(F);

for f in Functions do
    N:=[0,0];
    if isDOPolynomial(f) then
        N:=Nuclei(f, e, subfields, sizes);
    end if;

    order := "NA";
    if (n lt 6) or ((n eq 6) and not N in {[3^6,3^6],[3^(2),3^(2)]}) then
        order := AutomoriphismGroupOrderFromFunction(f);
    end if;

    key := Sprintf("%o.%o", N, order);

    if not key in Keys(gt_invariant_table) then
        printf "unknown combination of invariants for f=%o\n\n";
        gt_invariant_table[key] := f;
        to_test_for_equivalence[key] := [];
    end if;

    Append(~to_test_for_equivalence[key], f);
end for;

SetOutputFile(Sprintf("equivalence_test/%o", filename));

printf "p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\nFunctionsToTest := [\n", p, n;

for k->v in to_test_for_equivalence do
    printf "    %o,", v;
end for;

printf "];\n";