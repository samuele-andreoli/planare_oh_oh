load "lib/cczEquivalence.m";
load "lib/invariantTable.m";
load "lib/representatives.m";
load "lib/@SEMIFIELDS@";
load "lib/planar.m";
load "lib/dupeq.m";

p := @P@;
n := @N@;
q := p^n;

l := @L@;

// Dimension of the subfield for the coefficients
m := @M@;
assert n mod m eq 0;

/* End of user modifiabile section */

filename := Sprintf("p%o_n%o_l%o_m%o", p, n, l, m);
SetLogFile(Sprintf("logs/%o", filename) : Overwrite := true);

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

// Precomputation for fast planar functions test
FFs:=getFFs(F);

S := {x : x in GF(p^m) | not IsZero(x)};
CoeffSpace := CartesianPower(S, l);

E := {};
cosets := AssociativeArray();

for i in [0..n-1] do
    ei := p^i;
    for j in [i..n-1] do
        e := ei + p^j;
        
        cosets[e] := j-i;
        Include(~E, e);
    end for;
end for;

// Cyclotomic + mult. cosets representatives of the elements in Fp^n
// When guessing the coeff. for a chosen exponent e, it is enough to get it from here
F_M_e := AssociativeArray();
F_cosets := AssociativeArray();
F_cosets[1] := {One(F)};

print "Computing cosets";

for d in Divisors(q-1) do
    // Compute M := {a^(f-e) : a in F}
    if IsDefined(F_cosets, d) then
        continue;
    end if;        

    g := a^d;
    M := {g^i : i in [1..((q-1) div d)]};

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

        Include(~coset_reps, Min(coset));
        F_elements diff:= coset;
    end while;

    F_cosets[d] := coset_reps;
end for;

ExpSpace   := {s : s in Subsets(E,l) | #{cosets[e] : e in s} gt 1};

IncompleteCoeffSpace := CartesianPower(S, l-2);

generatedPlanarFunctions := [];

expansion_filename := Sprintf("expansions/%o", filename);
PrintFile(expansion_filename, Sprintf("p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\ngeneratedPlanarFunctions := [", p, n) : Overwrite := true);

print "Start expansion";
timeExpansion := Cputime();

for exp in ExpSpace do
    e := [ei : ei in exp];

    // Select the first exponent from the correct cyclotomic + multiplicative
    // cosets representatives for e[1]. The others are all possible l-1 subsets of the coefficients.
    for coefficients in CartesianProduct(F_cosets[GCD(e[1]-e[2], q-1)], IncompleteCoeffSpace) do
        // First can always be 1, second can be one representative for each coset using M and p^i
        candidate := x^e[1] + coefficients[1] * x^e[2];

        for i in [3..l] do
            candidate +:= (coefficients[2])[i-2] * x^e[i];
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

for k->v in to_test_for_equivalence do
    PrintFile(equivalence_filename, Sprintf("to_test_for_equivalence[\"%o\"] := %o;\n", k, v));
end for;

// Classification using dupeq
orbitsTable := getOrbitsTable(n);

print "Start equivalence test";
timeEquivalence := Cputime();

inequivalent_functions := AssociativeArray();
equivalence_classes := AssociativeArray();
for k->v in to_test_for_equivalence do
    // We have made sure they are in invariant table
    // and that the easier the (in)equivalence check, the earlier we process them
    // so we expect to get rid of most ones before getting to the hard equivalence tests.
    representatives := invariantTable[k];

    vs := {vi : vi in v};
    inequiv := vs;
    for r in representatives do
        if r in Keys(orbitsTable) then
            orbits := orbitsTable[r];
            inequiv := {f : f in inequiv | not dupeq_with_l2_representatives(r,f,orbits)};
        else
            // Leave this for sanity, but now all should have orbits
            inequiv := {f : f in inequiv | not dupeq(r,f)};
        end if;

        vs diff:= inequiv;
        equivalence_classes[r] := vs;
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

PrintFile(inequivalent_filename, "equivalence_classes := AssociativeArray();\n");

for k->v in equivalence_classes do
    if not k in interesting_r then
        continue;
    end if;

    PrintFile(inequivalent_filename, Sprintf("equivalence_classes[\"%o\"] := %o;\n", k, v));
end for;

printf "\n";

p;
n;
m;
l;

UnsetLogFile();

quit;