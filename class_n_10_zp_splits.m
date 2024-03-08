load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

p := 3;
n := 10;

F<u> := GF(p^n);
R<x> := PolynomialRing(F);

BH := [
    x^2430 + x^244 + u^44286*x^10,
    x^19926 + x^244 + u^44286*x^82
];

bh1TT, invbh1TT := get_tt_with_inv(BH[1]);
bh2TT, invbh2TT := get_tt_with_inv(BH[2]);

orbit_rep := {u^17, One(F), u, u^2, u^3, u^4, u^5, u^6, u^8, u^10, u^11, u^12, u^13};

getZP_cop0_TT:=function(R)
    F:=BaseRing(R);
    p:=Characteristic(F);
    n:=Degree(F);

    if not IsDivisibleBy(n,2) then
        return [];
    end if;

    m:=n div 2;
    Fq := GF(p^m);

    ZP:=[];
    ns:=pickNonSquare(GF(p^m));

    Op1TT := AssociativeArray();
    for a in Fq do
        // Op1:=ns*y;
        Op1TT[a] := ns * a;
    end for;

    for k:=1 to (m div 2) do
        if IsEven(m div GCD(m,k)) then
            continue;
        end if;

        OpTT := AssociativeArray();
        for a in Fq do
            // Op := 2*y^(p^k+1)
            OpTT[a] := 2*a^(p^k+1);
        end for;

        Append(~ZP, getFunFromSpecialSemifieldTT_zero_op2(R,OpTT,Op1TT));
    end for;

    return ZP;
end function;

/* Check if ZP splits into BH (quick, we have nuclei)*/
// SetLogFile("logs/zp_bh_split.txt": Overwrite := true);

// for zTT in getZP_cop0_TT(R) do
//     star:=function(u,v)
//         return zTT[u+v] - zTT[u] - zTT[v];
//     end function;

//     e := Zero(F);
//     for a in F do
//         if IsOne(star(a,a)) then
//             e := a;
//             break;
//         end if;
//     end for;

//     assert not IsZero(e);

//     starPsi := AssociativeArray();
//     for u in F do
//         starPsi[star(u,e)] := u;
//     end for;

//     asterisk := function(u,v)
//         return star(starPsi[u],starPsi[v]);
//     end function;

//     N:=GF(3);
//     Nm:=GF(3^2);

//     CandidatesB:={Rep({asterisk(u,b): u in N| not IsZero(u)}): b in Nm | not b in N};

//     for b in CandidatesB do
//         f1TT:= AssociativeArray();
//         invf1TT := AssociativeArray();
//         for x in F do
//             if IsDefined(f1TT, x) then
//                 continue;
//             end if;

//             f1TT[x] := asterisk(asterisk(b,x),x);
//             f1TT[-x] := f1TT[x];
//             invf1TT[f1TT[x]] := Min({x,-x});
//         end for;

//         s, l1, l2 := dupeq_with_l2_representatives_tt(bh1TT, invbh1TT, f1TT, invf1TT, orbit_rep);
//         if s then
//             print "Splits into BH1";
//             b;
//             e;
//             Interpolation([u : u in F], [l1[u] : u in F]);
//             Interpolation([u : u in F], [l2[u] : u in F]);
//             break;
//         end if;

//         s, l1, l2 := dupeq_with_l2_representatives_tt(bh1TT, invbh1TT, f1TT, invf1TT, orbit_rep);
//         if s then
//             print "Splits into BH2";
//             b;
//             e;
//             Interpolation([u : u in F], [l1[u] : u in F]);
//             Interpolation([u : u in F], [l2[u] : u in F]);
//             break;
//         end if;
//     end for;
// end for;

// UnsetLogFile();

SetLogFile("logs/zp_split.txt": Overwrite := true);

zps :=  getZP_cop0_TT(R);

zTT := zps[1];
zTT2 := zps[2];

invzTT2 := AssociativeArray();
for a in F do
    if IsDefined(invzTT2, a) then
        continue;
    end if;

    invzTT2[zTT2[a]] := Min({a, -a});
end for;

/* To compute orbits, then use precomputed */

print "Interpolation";

z := Interpolation([u : u in F], [zTT[u] : u in F]);
z2 := Interpolation([u : u in F], [zTT2[u] : u in F]);

invzTT := AssociativeArray();
for a in F do
    if IsDefined(invzTT, a) then
        continue;
    end if;

    invzTT[zTT[a]] := Min({a, -a});
end for;

print "Computing orbits";

tp := trivialPartition(z);
orbits := partitionByL2tt(zTT, invzTT, tp);
z;
{* #o : o in orbits*};
orbit_rep := {Min(o) : o in orbits};
orbit_rep;

tp := trivialPartition(z2);
orbits := partitionByL2tt(zTT2, invzTT2, tp);
z2;
{* #o : o in orbits*};
orbit_rep := {Min(o) : o in orbits};
orbit_rep;

quit;

/* End orbits computation */ 

star:=function(u,v)
    return zTT[u+v] - zTT[u] - zTT[v];
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
end for;

UnsetLogFile();
