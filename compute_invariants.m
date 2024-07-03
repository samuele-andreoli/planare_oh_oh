load "lib/representatives.m";
load "lib/invariantTable.m";
load "lib/cczEquivalence.m";
load "lib/semifields.m";
load "lib/planar.m";

/* Header - choose the dimensions/functions to examine here */

dimensions := [3..8];
functionLists := [getRepresentatives(n) : n in dimensions];

/* End of Header */

SetLogFile("logs/invariants.txt": Overwrite := true);


for i := 1 to #dimensions do
    n := dimensions[i];
    F<a>:=GF(3^n);
    R<x>:=PolynomialRing(F);

    list := functionLists[i];

    printf "Invariants for dimension %o.\n",n;

    invariantTable := AssociativeArray();

    for fr in list do
        f := R!fr;
        
        N:=[0,0];
        if isDOPolynomial(f) then
            N:=Nuclei(f, One(F));
        end if;

        order := "NA";
        if ((n eq 6) and not N in {[3^6,3^6],[3^2,3^2]}) then
            order := AutomoriphismGroupOrderFromFunction(f);
        end if;

        key := Sprintf("%o.%o", N, order);

        if not key in Keys(invariantTable) then
            invariantTable[key] := {f};
        else
            Include(~invariantTable[key],f);
        end if;
    end for;

    for key in Keys(invariantTable) do
        printf "\t%o : %o\n\n", key, invariantTable[key];
    end for;
end for;

UnsetLogFile();