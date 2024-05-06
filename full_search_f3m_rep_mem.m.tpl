load "lib/invariantTable.m";
load "lib/dupeq.m";

/* Search parameters. Modify here */

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

representatives := getRepresentatives(n);
orbitsTable := getOrbitsTable(n);

zp1TT, invzp1TT := get_tt_with_inv(representatives[21]);
orbits1 := orbitsTable[representatives[21]];

zp2TT, invzp2TT := get_tt_with_inv(representatives[23]);
orbits2 := orbitsTable[representatives[23]];

print "Start expansion";

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

        if not fastIsPlanarDOPoly(candidate,FFs) then
            continue;
        end if;

        print "b";

        N:=Nuclei(candidate, One(F));

        if N ne [3,9] then
            continue;
        end if;

        fTT, invfTT := get_tt_with_inv(candidate);

        if dupeq_with_l2_representatives_tt(zp1TT, invzp1TT, fTT, invfTT, orbits1) then
            printf "repr 1 %o\n", candidate;
            continue;
        end if;
        if dupeq_with_l2_representatives_tt(zp2TT, invzp2TT, fTT, invfTT, orbits2) then
            printf "repr 2 %o\n", candidate;
            continue;
        end if;

        printf("done 1\n");
    end for;
end for;

p;
n;
m;
l;

UnsetLogFile();

quit;