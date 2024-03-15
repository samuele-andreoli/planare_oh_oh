load "lib/FamiliesPlanar.m";
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

// Re-generalize to find better representative
findBetterRepresentatives := procedure(fTT, invfTT, gTT, invgTT, orbitsf, orbitsg)
    m := n div 2;
    Fq := GF(p^m);

    OpTTs := [];
    for k:=1 to (m div 2) do
        if IsEven(m div GCD(m,k)) then
            continue;
        end if;

        OpTT := AssociativeArray();
        for a in Fq do
            // Op := 2*y^(p^k+1)
            OpTT[a] := 2*a^(p^k+1);
        end for;
    end for;

    for ns in F do
        if IsZero(ns) or IsSquare(ns) then
            continue;
        end if;

        Op1TT := AssociativeArray();
        for a in Fq do
            // Op1:=ns*y;
            Op1TT[a] := ns * a;
        end for;

        for OpTT in OpTTs do
            candTT := getFunFromSpecialSemifieldTT_zero_op2(R,OpTT,Op1TT);

            invcandTT := AssociativeArray();
            for x in F do
                if IsDefined(invcandTT, candTT[x]) then
                    continue;
                end if;

                invcandTT[candTT[x]] := Min({x, -x});
            end for;

            success, l1, l2 := dupeq_with_l2_representatives_tt(fTT, invfTT, candTT, invcandTT, orbitsf);
            if success then
                printf "Found candindate for ZP1 %o\n", cand;
                continue;
            end if;

            success, l1, l2 := dupeq_with_l2_representatives_tt(gTT, invgTT, candTT, invcandTT, orbitsg);
            if success then
                printf "Found candindate for ZP2 %o\n", cand;
                continue;
            end if;
        end for;
    end for;
end procedure;

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

// TODO b,e from split
e := One(F);
b := One(F);

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
zp_split := Interpolation([x : x in F],[fTT[x] : x in F]);
tp := trivialPartition(zp_split);
orbits := partitionByL2tt(fTT, invfTT, tp);
{* #o : o in orbits*};
orbitsf := {Min(o) : o in orbits};
orbitsf;

/* Compute naive split of ZP2 for dupeq */
star:=function(u,v)
    return zp2TT[u+v] - zp2TT[u] - zp2TT[v];
end function;

// TODO b,e from split
e := One(F);
b := One(F);

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

/* Compute orbits, then use precomputed */
zp_split := Interpolation([x : x in F],[gTT[x] : x in F]);
tp := trivialPartition(zp_split);
orbits := partitionByL2tt(gTT, invgTT, tp);
{* #o : o in orbits*};
orbitsg := {Min(o) : o in orbits};
orbitsg;

print "Find better representatives";

findBetterRepresentatives(fTT, invfTT, gTT, invgTT, orbitsf, orbitsg);

UnsetLogFile();
