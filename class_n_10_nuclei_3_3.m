load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

i := 1; // to 4

F<a> := GF(3^10);
R<x> := PolynomialRing(F);

getZP_rest:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  Op2:=Zero(RR);
  ZP:=[];
  ns:=pickNonSquare(GF(p^m));
  cop:=[i: i in [1..(m div 2)]|IsOne(GCD(i,m))];
  for k:=1 to (m div 2) do
    if IsOdd(m div GCD(m,k)) then
      Op:=2*y^(p^k+1);
      for i in cop do
        Op1:=ns*y^(p^i);
        Append(~ZP,getFunFromSpecialSemifield(R,Op,Op1,Op2));
      end for;
    end if;
  end for;
  return ZP;
end function;

ganley := getG(R);
zhoupott := getZP_rest(R);

FFs := getFFs(F);
gTT, invgTT := get_tt_with_inv(ganley[1], FFs);

zp := zhoupott[i];
zpTT, invzpTT := get_tt_with_inv(zp, FFs);

s, l1, l2 := dupeq_tt(gTT, invgTT, zpTT, invzpTT);
if s then 
    printf "Eqiuvalent to %o\n", zp;
    Interpolation([u : u in F], [l1[u] : u in F]);
    Interpolation([u : u in F], [l2[u] : u in F]);
end if;
