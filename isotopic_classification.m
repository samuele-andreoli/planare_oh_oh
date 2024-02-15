load "lib/representatives.m";
load "lib/dupeq.m";
load "lib/semifields.m";
IsotopicTransform:=function(f,b)
  return Interpolation([u: u in Parent(b)],[Evaluate(f,u+Evaluate(f,u+b)-f-Evaluate(f,b))-f-Evaluate(f,Evaluate(f,u+b)-f-Evaluate(f,b)): u in Parent(b)]);
end function;
for n:=2 to 8 do
  F<a>:=GF(3^8);
  R<x>:=PolynomialRing(F);
  Fun:=R!getRepresentatives(n);
  for i:=1 to #Fun do
    f:=Fun[i];
    printf "\n%o.%o\t",n,i;
    N,Nm:=getNuclei(f,One(GF(3^n)));
    if IsEven(Log(3,Floor(#Nm/#N))) then
      printf"CH candidate\t";
      bol:=true;
      for b in Nm diff N do
        f1:=IsotopicTransform(f,b);
        if not dupeq(f,f1) then
          printf "splits\t";
          f1;
          bol:=false;
          break;
        end if;
      end for;
      if bol then
        printf "does not split";
      end if;
    end if;
  end for;
end for;
