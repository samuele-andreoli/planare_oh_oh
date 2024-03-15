load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

p := 3;
n := 10;
m := n div 2;

Fq := GF(p^m);
F<a> := GF(p^n);
R<x> := PolynomialRing(F);

ns:=pickNonSquare(GF(p^m));

Op1TT := AssociativeArray();
for a in Fq do
    Op1TT[a] := 2*a^(p+1);
end for;

// Op2TT := AssociativeArray();
// for a in Fq do
//     Op2TT[a] := 2*a^(p^2+1);
// end for;

Op10TT := AssociativeArray();
for a in Fq do
    Op10TT[a] := ns * a;
end for;

Op11TT := AssociativeArray();
for a in Fq do
    Op11TT[a] := ns * a^p;
end for;

Op12TT := AssociativeArray();
for a in Fq do
    Op12TT[a] := ns * a^(p^2);
end for;

r01 := getFunFromSpecialSemifieldTT_zero_op2(R, Op1TT, Op10TT);
r11 := getFunFromSpecialSemifieldTT_zero_op2(R, Op1TT, Op11TT);
r21 := getFunFromSpecialSemifieldTT_zero_op2(R, Op1TT, Op12TT);
// r02 := getFunFromSpecialSemifieldTT_zero_op2(R, Op2TT, Op10TT);
// r12 := getFunFromSpecialSemifieldTT_zero_op2(R, Op2TT, Op11TT);
// r22 := getFunFromSpecialSemifieldTT_zero_op2(R, Op2TT, Op12TT);

invr01 := AssociativeArray();
for x in F do
    if IsDefined(invr01, r01[x]) then
        continue;
    end if;

    invr01[r01[x]] := Min({x, -x});
end for;

invr11 := AssociativeArray();
for x in F do
    if IsDefined(invr11, r11[x]) then
        continue;
    end if;

    invr11[r11[x]] := Min({x, -x});
end for;

invr21 := AssociativeArray();
for x in F do
    if IsDefined(invr21, r21[x]) then
        continue;
    end if;

    invr21[r21[x]] := Min({x, -x});
end for;

// invr02 := AssociativeArray();
// for x in F do
//     if IsDefined(invr02, r02[x]) then
//         continue;
//     end if;

//     invr02[r02[x]] := Min({x, -x});
// end for;

// invr12 := AssociativeArray();
// for x in F do
//     if IsDefined(invr12, r12[x]) then
//         continue;
//     end if;

//     invr12[r12[x]] := Min({x, -x});
// end for;

// invr22 := AssociativeArray();
// for x in F do
//     if IsDefined(invr22, r22[x]) then
//         continue;
//     end if;

//     invr22[r22[x]] := Min({x, -x});
// end for;

// 10.20 (i,k)=(0,1)
zp01 := 2*x^19926 + 2*x^486 + 2*x^82 + x^2;
fTT, invfTT := get_tt_with_inv(zp01);

/* To compute orbits. Then use precomputed */
// tp := trivialPartition(zp11);
// orbits := partitionByL2tt(fTT, invfTT, tp);
// zp01;
// {* #o : o in orbits*};
// orbit_rep_zp01 := {Min(o) : o in orbits};
// orbit_rep_zp01;
// {* 484^^2, 4840^^12 *}
orbit_rep_zp01 := { 1, a^17, a, a^2, a^19, a^20, a^4, a^5, a^7, a^8, a^10, a^61, a^11, a^16 };

dupeq_with_l2_representatives_tt(fTT, invfTT, r01, invr01, orbit_rep_zp01);

// 10.12 (i,k)=(1,1)
zp11 := x^2916 + 2*x^2190 + x^972 + 2*x^738 + a^14762 * x^730 + a^14762 * x^486 + a^44286 * x^246 + a^22143 * x^244 + x^12 + x^4 + x^2;
fTT, invfTT := get_tt_with_inv(zp11);

/* To compute orbits. Then use precomputed */
// tp := trivialPartition(zp11);
// orbits := partitionByL2tt(fTT, invfTT, tp);
// {* #o : o in orbits*};
// orbit_rep_zp11 := {Min(o) : o in orbits};
// orbit_rep_zp11;
// {* 242^^2, 484, 2420^^24 *}
orbit_rep_zp11 := { 1, a, a^2, a^3, a^62, a^4, a^34, a^6, a^7, a^8, a^183, a^68, a^10, a^39, a^69, a^11, a^12, a^14, a^15, a^74, a^19, a^21, a^22, a^23, a^53, a^84, a^28 };

dupeq_with_l2_representatives_tt(fTT, invfTT, r11, invr11, orbit_rep_zp11);

// 10.14 (i,k)=(2,1)
zp21 := x^8748 + 2 * x^6570 + 2 * x^2214 + x^972 + a^14762 * x^730 + a^14762 * x^486 + a^44286 * x^246 + a^22143 * x^244 + x^36 + x^4 + x^2;
fTT, invfTT := get_tt_with_inv(zp21);

/* To compute orbits. Then use precomputed */
// tp := trivialPartition(zp21);
// orbits := partitionByL2tt(fTT, invfTT, tp);
// zp21;
// {* #o : o in orbits *};
// orbit_rep_zp21 := {Min(o) : o in orbits};
// orbit_rep_zp21;
// {* 242^^2, 484, 2420^^24 *}
orbit_rep_zp21 := { 1, a^43, a, a^2, a^3, a^4, a^5, a^48, a^6, a^7, a^8, a^53, a^183, a^11, a^16, a^192, a^20, a^64, a^21, a^23, a^28, a^29, a^31, a^34, a^79, a^38, a^42 };

dupeq_with_l2_representatives_tt(fTT, invfTT, r21, invr21, orbit_rep_zp21);

// // 10.22 (i,k)=(0,2)
// zp02 := x^2430 + x^486 + x^10 + 2*x^2;
// fTT, invfTT := get_tt_with_inv(zp02);

// /* To compute orbits. Then use precomputed */
// // tp := trivialPartition(zp02);
// // orbits := partitionByL2tt(fTT, invfTT, tp);
// // {* #o : o in orbits*};
// // orbit_rep_zp02 := {Min(o) : o in orbits};
// // orbit_rep_zp02;
// // {* 484^^2, 4840^^12 *}
// orbit_rep_zp02 := { 1, a^17, a, a^2, a^19, a^20, a^4, a^5, a^7, a^8, a^10, a^61, a^11, a^16 };

// dupeq_with_l2_representatives_tt(fTT, invfTT, r02, invr02, orbit_rep_zp02);

// // 10.13 (i,k)=(1,2)
// zp12 := 2*x^7290 + x^6564 + 2*x^2430 + 2*x^2188 + x^756 + x^486 + 2*x^252 + 2*x^30 + 2*x^10 + 2*x^2;
// fTT, invfTT := get_tt_with_inv(zp12);

// /* To compute orbits. Then use precomputed */
// // tp := trivialPartition(zp12);
// // orbits := partitionByL2tt(fTT, invfTT, tp);
// // {* #o : o in orbits*};
// // orbit_rep_zp12 := {Min(o) : o in orbits};
// // orbit_rep_zp12;
// // {* 242^^2, 484, 2420^^24 *}
// orbit_rep_zp12 := { 1, a, a^4, a^133, a^5, a^91, a^49, a^7, a^10, a^11, a^55, a^14, a^16, a^104, a^19, a^20, a^65, a^22, a^26, a^31, a^76, a^34, a^122, a^38, a^82, a^40, a^41 };

// dupeq_with_l2_representatives_tt(fTT, invfTT, r12, invr12, orbit_rep_zp12);

// // 10.15 (i,k)=(2,2)
// zp22 := 2*x^21870 + x^19692 + 2*x^2430 + x^2268 + 2*x^2188 + x^486 + 2*x^252 + 2*x^90 + 2*x^10 + 2*x^2;
// fTT, invfTT := get_tt_with_inv(zp12);

// /* To compute orbits. Then use precomputed */
// // tp := trivialPartition(zp22);
// // orbits := partitionByL2tt(fTT, invfTT, tp);
// // {* #o : o in orbits*};
// // orbit_rep_zp22 := {Min(o) : o in orbits};
// // orbit_rep_zp22;
// // {* 242^^2, 484, 2420^^24 *}
// orbit_rep_zp22 := { 1, a^43, a, a^2, a^4, a^5, a^8, a^10, a^11, a^55, a^56, a^14, a^16, a^19, a^22, a^109, a^23, a^67, a^25, a^70, a^29, a^34, a^164, a^122, a^79, a^37, a^125 };

// dupeq_with_l2_representatives_tt(fTT, invfTT, r12, invr12, orbit_rep_zp22);