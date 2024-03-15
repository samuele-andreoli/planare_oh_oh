load "lib/dupeq.m";

p := 3;
n := 10;

F<a> := GF(p^n);
R<x> := PolynomialRing(F);
representatives := [
    2*x^4374 + 2*x^2196 + a^7686 * x^1458 + a^7686 * x^732 + a^244 * x^486 + a^244 * x^244 + 2 * x^18 +a^7686 * x^6 + a^1220 * x^2,
    x^1458 + x^732 + 2*x^486 + 2*x^244 + x^6,
    x^4374 + x^2196 + 2*x^486 + 2*x^244 + x^18,
    a^44286 * x^13122 + a^44286 * x^6588 + x^4374 + x^2196 + x^486 + x^244 + a^44286 * x^54 + x^18
];

SetLogFile("logs/c10_orbits.txt" : Overwrite := true);

for r in representatives do
    orbits := partitionByL2(r);

    r;
    {* #o : o in orbits *};
    {Min(o) : o in Orbits};
end for;

UnsetLogFile();
