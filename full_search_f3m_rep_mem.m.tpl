load "lib/cczEquivalence.m";
load "lib/invariantTable.m";
load "lib/representatives.m";
load "lib/semifields.m";
load "lib/planar.m";
load "lib/dupeq.m";

p := @P@;
n := @N@;
q := p^n;

l := @L@;

// Dimension of the subfield for the coefficients
m := @M@;
assert n mod m eq 0;

filename := Sprintf("p%o_n%o_l%o_m%o", p, n, l, m);
SetLogFile(Sprintf("logs/%o", filename) : Overwrite := true);

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

// Default targets are all non monomials. Refining the search is recommended.
targets := getRepresentatives(n);
targets := [r : r in getRepresentatives(n) | #Terms(r) gt 1];

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

invariantTable := getInvariantTable(n);
invariantTableTT := AssociativeArray();

for key -> values in invariantTable do
    TTs := [];
    for r in values do
        tt, invtt := get_tt_with_inv(r);
        Append(~TTs, <r, tt, invtt>);
    end for;

    invariantTableTT[key] := TTs;
end for;

orbitsTable := getOrbitsTable(n);

print "Start expansion";
t := Cputime();

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

        try 
            N:=Nuclei(candidate, One(F));
        catch e
            // Just test it with the equivalence
            N := [3,3];
        end try;

        order := "NA";
        if (n lt 6) or ((n eq 6) and not N in {[p^n,p^n],[p^2,p^2]}) then
            order := AutomoriphismGroupOrderFromFunction(candidate);
        end if;

        key := Sprintf("%o.%o", N, order);

        /* Use theoretical results on nuclei to weed out some of the expansions, when we already know good representatives */
        x2_key := Sprintf("[ %o, %o ].NA", p^n, p^n);
        if key eq x2_key then
            continue;
        end if;

        if n mod 4 eq 0 then
            // It's all Dickson
            dickson_key := Sprintf("[ %o, %o ].NA", p^(n div 4), p^(n div 2));

            if key eq dickson_key then
                continue;
            end if;
        end if;

        if n mod 3 eq 0 then
            // It's all Albert
            albert_key := Sprintf("[ %o, %o ]", p^(n div 3), p^(n div 3));

            if Substring(key, 1, #albert_key) eq albert_key then
                continue;
            end if;
        end if;

        fTT, invfTT := get_tt_with_inv(candidate);

        // We should have already found this in the expansion searches, but out of caution...
        if not key in Keys(invariantTableTT) then
            printf "unknown combination of invariants %o for %o\n", key, candidate;
            Append(~invariantTableTT[key], <candidate, fTT, invfTT>);
        end if;

        representatives := invariantTableTT[key];
        inequiv := true;

        for r in representatives do
            if r[1] in Keys(orbitsTable) then
                orbits  := orbitsTable[r[1]];
                if dupeq_with_l2_representatives_tt(r[2], r[3], fTT, invfTT, orbits) then
                    inequiv := false;
                    break;
                end if;
            else
                if dupeq_tt(r[2], r[3], fTT, invfTT) then
                    inequiv := false;
                    break;
                end if;
            end if;
        end for;

        if inequiv then
            // We should have already found this in the expansion searches, but out of caution...
            printf "inequivalent function with invariants %o: f=%o\n\n", key, candidate;
            Append(~invariantTableTT[key], <candidate, fTT, invfTT>);
        elif r in targets then
            printf "Representative found for target %o: %o\n", r, candidate;
        end if;
    end for;
end for;

printf "\n";

Cputime(t);

p;
n;
m;
l;

UnsetLogFile();

quit;