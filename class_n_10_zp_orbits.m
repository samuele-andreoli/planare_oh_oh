load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

p := 3;
n := 10;

F<a> := GF(p^n);
R<x> := PolynomialRing(F);

ns:=pickNonSquare(GF(p^m));

//(i,k)=(0,2)
zp02 := x^2430 + x^486 + x^10 + 2*x^2;
fTT, invfTT := get_tt_with_inv(zp02);

/* To compute orbits. Then use precomputed */
tp := trivialPartition(zp02);
orbits := partitionByL2tt(fTT, invfTT, tp);
{* #o : o in orbits*};
orbit_rep := {Min(o) : o in orbits};
orbit_rep;

//(i,k)=(1,2)
zp12 := 2*x^7290 + x^6564 + 2*x^2430 + 2*x^2188 + x^756 + x^486 + 2*x^252 + 2*x^30 + 2*x^10 + 2*x^2;

fTT, invfTT := get_tt_with_inv(zp12);

/* To compute orbits. Then use precomputed */
tp := trivialPartition(zp12);
orbits := partitionByL2tt(fTT, invfTT, tp);
{* #o : o in orbits*};
orbit_rep := {Min(o) : o in orbits};
orbit_rep;

//(i,k)=(2,2)
zp22 := 2*x^21870 + x^19692 + 2*x^2430 + x^2268 + 2*x^2188 + x^486 + 2*x^252 + 2*x^90 + 2*x^10 + 2*x^2;

OpTT := AssociativeArray();
for a in Fq do
    OpTT[a] := 2*a^(p^2+1);
end for;

Op10TT := AssociativeArray();
for a in Fq do
    Op1TT[a] := ns * a;
end for;

Op11TT := AssociativeArray();
for a in Fq do
    Op1TT[a] := ns * a^p;
end for;

Op12TT := AssociativeArray();
for a in Fq do
    Op1TT[a] := ns * a^(p^2);
end for;

r02 := getFunFromSpecialSemifieldTT_zero_op2(R, OpTT, Op10TT);
r12 := getFunFromSpecialSemifieldTT_zero_op2(R, OpTT, Op11TT);
r22 := getFunFromSpecialSemifieldTT_zero_op2(R, OpTT, Op12TT);

