load "lib/representatives.m";
load "lib/invariantTable.m";
load "lib/dupeq.m";

/* Header - choose the dimensions/functions to examine here */

dimensions := [3..8];
functionLists := [getRepresentatives(n) : n in dimensions];

/* End of Header */

SetLogFile("logs/orbits.txt": Overwrite:= true);

for i := 1 to #dimensions do
    n := dimensions[i];
    F<a>:=GF(3^n);
    R<x>:=PolynomialRing(F);

    list := functionLists[i];

    printf "Orbits for dimension %o\n", n;

    for f in list do
        orbits := partitionByL2(R!f);
        orbits_rep := [Min(o) : o in orbits];
        Sort(~orbits_rep);

        printf "\t%o\n", R!f;
        printf "\t\t orbits multiset        : %o\n", {* #o : o in orbits *};
        printf "\t\t orbits representatives : %o\n\n", orbits_rep;
    end for;
end for;

UnsetLogFile();