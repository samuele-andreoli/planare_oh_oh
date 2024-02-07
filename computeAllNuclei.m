load "lib/representatives.m";
load "lib/semifields.m";
load "lib/planar.m";


for n:=3 to 8 do
    Functions := getRepresentatives(n);
    F:=BaseRing(Parent(Functions[1]));
    e:=One(F);

    for i:=1 to #Functions do
        printf "%o.%o\t",n,i;
        if isDOPolynomial(Functions[i]) then
            N:=Nuclei(Functions[i], e);
            printf "%o",N;
        end if;
        printf "\n\n";
    end for;
end for;
