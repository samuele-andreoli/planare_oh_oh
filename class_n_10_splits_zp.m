load "lib/familiesPlanar.m";
load "lib/dupeq.m";

p := 3;
n := 10;

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

ZP_cop0 := [
    2*x^19926 + 2*x^486 + 2*x^82 + x^2,
    x^2430 + x^486 + x^10 + 2*x^2
];

zp1TT, invzp1TT := get_tt_with_inv(ZP_cop0[1]);
zp2TT, invzp2TT := get_tt_with_inv(ZP_cop0[2]);

orbits := { 1, a^17, a, a^2, a^19, a^20, a^4, a^5, a^7, a^8, a^10, a^61, a^11, a^16 };

SetLogFile("logs/zp_split.txt": Overwrite := true);

/* Check if ZP1/2 splits (into ZP2/1) */

split_ZP := procedure(f, ZP1TT, invZP1TT, ZP2TT, invZP2TT)
    star:=function(u,v)
        return ZP1TT[u+v] - ZP1TT[u] - ZP1TT[v];
    end function;

    e := Zero(F);
    for a in F do
        if IsOne(star(a,a)) then
            e := a;
            break;
        end if;
    end for;

    assert not IsZero(e);

    starPsi := AssociativeArray();
    for u in F do
        starPsi[star(u,e)] := u;
    end for;

    asterisk := function(u,v)
        return star(starPsi[u],starPsi[v]);
    end function;

    N:=GF(3);
    Nm:=GF(3^2);

    CandidatesB:={Rep({asterisk(u,b): u in N| not IsZero(u)}): b in Nm | not b in N};

    for b in CandidatesB do
        f1TT:= AssociativeArray();
        invf1TT := AssociativeArray();
        for x in F do
            if IsDefined(f1TT, x) then
                continue;
            end if;

            f1TT[x] := asterisk(asterisk(b,x),x);
            f1TT[-x] := f1TT[x];
            invf1TT[f1TT[x]] := Min({x,-x});
        end for;

        s, l1, l2 := dupeq_with_l2_representatives_tt(ZP1TT, invZP1TT, f1TT, invf1TT, orbits);
        if s then
            continue;
        end if;

        print "Splits!";

        s, l1, l2 := dupeq_with_l2_representatives_tt(ZP2TT, invZP2TT, f1TT, invf1TT, orbits);
        if s then
            print "Splits into ZP2";
            b;
            e;
            Interpolation([u : u in F], [l1[u] : u in F]);
            Interpolation([u : u in F], [l2[u] : u in F]);
        else
            b;
            e;
            print "Splits into new function";
        end if;
    end for;
end procedure;

SetMemoryLimit(10^10);

/* Find splits for zp1 and zp2 */

print "Split zp1";
split_ZP(ZP_cop0[1], zp1TT, invzp1TT, zp2TT, invzp2TT);

print "Split zp2";
split_ZP(ZP_cop0[2], zp2TT, invzp2TT, zp1TT, invzp1TT);

/* Compute naive split of ZP1 for dupeq */
star:=function(u,v)
    return zp1TT[u+v] - zp1TT[u] - zp1TT[v];
end function;

// b,e from split
e := a^14762;
b := a^7381;

starPsi := AssociativeArray();
for u in F do
    starPsi[star(u,e)] := u;
end for;

asterisk := function(u,v)
    return star(starPsi[u],starPsi[v]);
end function;

fTT:= AssociativeArray();
invfTT := AssociativeArray();
for x in F do
    if IsDefined(fTT, x) then
        continue;
    end if;

    fTT[x] := asterisk(asterisk(b,x),x);
    fTT[-x] := fTT[x];
    invfTT[fTT[x]] := Min({x,-x});
end for;

/* Compute orbits, then use precomputed */
// zp_split := Interpolation([x : x in F],[fTT[x] : x in F]);
// tp := trivialPartition(zp_split);
// orbits := partitionByL2tt(fTT, invfTT, tp);
// {* #o : o in orbits*};
// orbitsf := {Min(o) : o in orbits};
orbitsf := { 1, a, a^2, a^3, a^21, a^5, a^6, a^7, a^26, a^10, a^11, a^14, a^15 };

/* Compute naive split of ZP2 for dupeq */
star:=function(u,v)
    return zp2TT[u+v] - zp2TT[u] - zp2TT[v];
end function;

// b,e from split
e := One(F);
b := a^7381;

starPsi := AssociativeArray();
for u in F do
    starPsi[star(u,e)] := u;
end for;

asterisk := function(u,v)
    return star(starPsi[u],starPsi[v]);
end function;

gTT:= AssociativeArray();
invgTT := AssociativeArray();
for x in F do
    if IsDefined(gTT, x) then
        continue;
    end if;

    gTT[x] := asterisk(asterisk(b,x),x);
    gTT[-x] := gTT[x];
    invgTT[gTT[x]] := Min({x,-x});
end for;

UnsetLogFile();
