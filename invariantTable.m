load "representatives.m";

load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/planar.m";


getInvariantTable := function()
    n := 6;

    FuctionList:=getFun(n);

    F:=BaseRing(Parent(Fun[1]));
    e:=One(F);

    subfields,sizes:=PrecomputeSubfields(F);

    invariantTable := AssociativeArray();

    for f in Fun do
        N:=[0,0];
        if isDOPolynomial(f) then
            N:=Nuclei(f, e,subfields,sizes);
        end if;

        order := "NA";
        if (n lt 6) or ((n eq 6) and not N in {[3^6,3^6],[3^(2),3^(2)]}) then
            order := AutomoriphismGroupOrderFromFunction(f);
        end if;

        key := Sprintf("%o.%o", N, order);

        if not key in Keys(invariantTable) then
            invariantTable[key] := f;
        end if;
    end for;

    return invariantTable;
end function;
