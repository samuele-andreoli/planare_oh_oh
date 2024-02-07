load "representatives.m";
load "lib/semifields.m";
load "lib/planar.m";


for n:=3 to 8 do
  Fun:=getFun(n);
  F:=BaseRing(Parent(Fun[1]));
  e:=One(F);
  for i:=1 to #Fun do
    printf "%o.%o\t",n,i;
    if isDOPolynomial(Fun[i]) then
      N:=Nuclei(Fun[i], e);
      printf "%o",N;
    end if;
    printf "\n\n";
  end for;
end for;
