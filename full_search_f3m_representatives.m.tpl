load "lib/invariantTable.m";
load "lib/dupeq.m";

/* Search parameters. Modify here */

p := 3;
n := @N@;

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

// DO poly exponents not in the cyclotomic coset of 2. The check i gt j is redundant since we use a set,
// but might as well have it explicit.

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

CoeffSpace := CartesianPower(S, l);
ExpSpace   := {s : s in Subsets(E,l) | #{cosets[e] : e in s} gt 1};

generatedPlanarFunctions := [];

expansion_filename := Sprintf("expansions/%o", filename);
PrintFile(expansion_filename, Sprintf("p := %o;\nn := %o;\n\nF<a> := GF(p^n);\nR<x> := PolynomialRing(F);\n\ngeneratedPlanarFunctions := [", p, n) : Overwrite := true);

print "Start expansion";
timeExpansion := Cputime();

for exp in ExpSpace do
    e := [ei : ei in exp];

    for c in CoeffSpace do
        candidate := [Zero(F): x in [1..p^n]];
        
        for i in [1..l] do
            candidate[e[i]+1] := c[i];
        end for;

        candidate := R!candidate;

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
        N:=Nuclei(f, One(F));
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

if n eq 8 then
    interesting_r := [
        a^3608*x^1458 + a^3608*x^738 + a^3810*x^486 + a^3810*x^246 + a^3413*x^162 + a^3413*x^82 + a^3608*x^18 + a^3810*x^6 + a^2565*x^2,
        a^164*x^1458 + a^164*x^738 + a^950*x^486 + a^950*x^246 + a^616*x^162 + a^616*x^82 + a^164*x^18 + a^950*x^6 + a^6297*x^2
    ];
elif n eq 6 then
    interesting_r := [
        x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2,
        x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2
    ]
end if;

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