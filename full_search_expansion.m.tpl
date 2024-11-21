load "lib/cczEquivalence.m";
load "lib/invariantTable.m";
load "lib/@SEMIFIELDS@";
load "lib/dupeq.m";

load "lib/planar.m";

/* Expansion search parameters. Modify here */

p := @P@;
n := @N@;
ms := @MS@;
q := p^n;

// Dimension of the subfield for the coefficients
m := @M@;
assert n mod m eq 0;

// Monomial # for the expansion
l := @L@;

// Starting monomial for the expansion
f := @F@;

/* End of user modifiabile section */

filename := Sprintf("p%o_n%o_x%o_l%o_m%o", p, n, f, l, m);
SetLogFile(Sprintf("logs/%o", filename) : Overwrite := true);

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

xf := x^f;

// Subfields to not redo computations
subfields := [];
if #ms gt 0 then
    subfields := [GF(p^m) : m in ms];
end if;

// Precomputation for fast planar functions test
FFs:=getFFs(F);

S := {x : x in GF(p^m) | not IsZero(x)};

// DO poly exponents. The check i ge j is redundant since we use a set,
// but might as well have it explicit.
E := {p^i + p^j : i,j in [0..n-1] | i ge j};
Exclude(~E, f);
ExpSpace := Subsets(E, l);
IncompleteCoeffSpace := CartesianPower(S, l-1);

// Cyclotomic coset of the monomial used for expansion.
// If all chosen coefficients lie in it, then the generated
// polynomial is equivalent to a monomial.
exp_cyclotomic_coset := {f * p^i : i in [0..(n-1)]};

// Cyclotomic + mult. cosets representatives of the elements in Fp^n
// When guessing the coeff. for a chosen exponent e, it is enough to get it from here
F_M_e := AssociativeArray();
F_cosets := AssociativeArray();
F_cosets[1] := {One(F)};

print "Computing cosets";

for e in E do
    // Compute M := {a^(f-e) : a in F}
    d := GCD(q-1, f-e);
    if IsDefined(F_cosets, d) then
        continue;
    end if;        

    if not IsDefined(F_M_e, d) then
        g := a^d;
        M := {g^i : i in [1..((q-1) div d)]};

        F_M_e[d] := M;
    end if;

    M := F_M_e[d];

    // Find cosets using M and then cyclotomic equivalence
    F_elements := {x : x in F | not IsZero(x)};
    coset_reps := {};

    while #F_elements gt 0 do
        c := Rep(F_elements);

        coset := {c * m : m in M};
        new_values := coset;

        while #new_values gt 0 do
            ExtractRep(~new_values, ~r);
            
            rp := r^p;
            if not rp in coset then
                Include(~coset, rp);
                Include(~new_values, rp);
            end if;
        end while;

        r := Min(coset);
        for r1 in coset do
            if #subfields gt 1 and r1 in subfields[2] then
                r := r1;
                continue;
            end if;
            if #subfields gt 0 and r1 in subfields[1] then
                r := r1;
                break;
            end if;
        end for;

        Include(~coset_reps, r);
        F_elements diff:= coset;
    end while;

    F_cosets[d] := coset_reps;
end for;


generatedPlanarFunctions := [];

expansion_filename := Sprintf("expansions/%o", filename);
PrintFile(expansion_filename, Sprintf("p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\ngeneratedPlanarFunctions := [", p, n) : Overwrite := true);

print "Start expansion";
timeExpansion := Cputime();

for exp in ExpSpace do
    // First just skip the exponents if this would be equivalent to a monomial
    if exp subset exp_cyclotomic_coset then
        continue;
    end if;

    e := [ei : ei in exp];

    // Select the first exponent from the correct cyclotomic + multiplicative
    // cosets representatives for e[1]. The others are all possible l-1 subsets of the coefficients.
    for coefficients in CartesianProduct(F_cosets[GCD(f-e[1], q-1)], IncompleteCoeffSpace) do
        candidate := xf;

        is_in_subfield := false;
        for s in subfields do
            if coefficients[1] in s then
                is_in_subfield := true;

                for c in coefficients[2] do
                    if not c in s then
                        is_in_subfield := false;
                        break;
                    end if;
                end for;
            end if;

            if is_in_subfield then
                break;
            end if;
        end for;

        if is_in_subfield then 
            continue;
        end if;

        candidate +:= coefficients[1] * x^e[1];

        for i in [2..l] do
            candidate +:= (coefficients[2])[i-1] * x^e[i];
        end for;

        if fastIsPlanarDOPoly(candidate,FFs) then
            PrintFile(expansion_filename, Sprintf("%o,", candidate));
            Append(~generatedPlanarFunctions, candidate);
        end if;
    end for;
end for;

PrintFile(expansion_filename,"];");

printf "End expansion %o\n\n", Cputime(timeExpansion);

// Classification using invariants
invariantTable := getInvariantTable(n);

print "Start invariant test";
timeInvariant := Cputime();

to_test_for_equivalence := AssociativeArray();
for f in generatedPlanarFunctions do
    N:=[0,0];
    if isDOPolynomial(f) then
        N:=Nuclei(f);
    end if;

    order := "NA";
    if (n lt 6) or ((n eq 6) and not N in {[p^n,p^n],[p^2,p^2]}) then
        order := AutomoriphismGroupOrderFromFunction(f);
    end if;

    key := Sprintf("%o.%o", N, order);

    if not key in Keys(invariantTable) then
        printf "unknown combination of invariants %o for f=%o\n\n", key, f;
        invariantTable[key] := [f];
    end if;

    if not key in Keys(to_test_for_equivalence) then
        to_test_for_equivalence[key] := [];
    end if;

    Append(~to_test_for_equivalence[key], f);
end for;

printf "End invariant test %o\n\n", Cputime(timeInvariant);

equivalence_filename := Sprintf("equivalence_test/%o", filename);
PrintFile(equivalence_filename, Sprintf("p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\nto_test_for_equivalence := AssociativeArray();", p, n) : Overwrite:= true);

/* Use theoretical results on nuclei to weed out some of the expansions */

x2_key := Sprintf("[ %o, %o ].NA", p^n, p^n);
// No need to test for equivalence, it's all x^2
Remove(~to_test_for_equivalence, x2_key);

if n mod 4 eq 0 then
    // It's all Dickson
    dickson_key := Sprintf("[ %o, %o ].NA", p^(n div 4), p^(n div 2));

    Remove(~to_test_for_equivalence, dickson_key);
end if;

if n mod 3 eq 0 then
    // It's all Albert
    albert_key := Sprintf("[ %o, %o ]", p^(n div 3), p^(n div 3));

    for k in Keys(to_test_for_equivalence) do
        if Substring(k, 1, #albert_key) eq albert_key then
            Remove(~to_test_for_equivalence, k);
        end if;
    end for;
end if;

if n in {4,6,8,10} then
    // I know that nucleus
    nuclei_key := Sprintf("[ %o, %o ]", p, p^(n div 2));

    for k in Keys(to_test_for_equivalence) do
        if Substring(k, 1, #nuclei_key) eq nuclei_key then
            Remove(~to_test_for_equivalence, k);
        end if;
    end for;
end if;

for k->v in to_test_for_equivalence do
    PrintFile(equivalence_filename, Sprintf("to_test_for_equivalence[\"%o\"] := %o;\n", k, v));
end for;

/* Classification using dupeq */
orbitsTable := getOrbitsTable(n);

print "Start equivalence test";
timeEquivalence := Cputime();

inequivalent_functions := AssociativeArray();
for k->v in to_test_for_equivalence do
    // We have made sure they are in invariant table
    representatives := invariantTable[k];

    inequiv := v;
    for r in representatives do
        if r in Keys(orbitsTable) then
            orbits := orbitsTable[r];
            inequiv := [f : f in inequiv | not dupeq_with_l2_representatives(r,f,orbits)];
        else
            // If we do not have he orbit there is a reson :)
            inequiv := [f : f in inequiv | not dupeq(r,f)];
        end if;
    end for;

    if #inequiv gt 0 then
        inequivalent_functions[k] := inequiv;
    end if;
end for;

printf "End equivalence test %o\n\n", Cputime(timeEquivalence);

inequivalent_filename := Sprintf("inequivalent/%o", filename);

PrintFile(inequivalent_filename, Sprintf("p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\ninequivalent_functions := AssociativeArray();", p, n) : Overwrite:= true);

for k->v in inequivalent_functions do
    PrintFile(inequivalent_filename, Sprintf("inequivalent_functions[\"%o\"] := %o;\n", k, v));
end for;

printf "\n";

p;
n;
m;
l;
f;

UnsetLogFile();

quit;