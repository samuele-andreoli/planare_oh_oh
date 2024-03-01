load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

F<a> := GF(3^10);
R<x> := PolynomialRing(F);

getD_10:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  ns:=pickNonSquare(GF(p^m));
  Op:=y^2;
  Op2:=Zero(RR);
  cop:=[i: i in [1..((m div 2))]|IsOne(GCD(i,m))];
  return [getFunFromSpecialSemifield(R,Op,ns*y^(p^i) ,Op2): i in cop];
end function;

dickson := getD_10(R);

assert #dickson eq 2;

FFs := getFFs(F);

d1, d1inv := get_tt_with_inv(dickson[1], FFs);
d2, d2inv := get_tt_with_inv(dickson[2], FFs);

s, l1, l2 := dupeq_tt(d1, d1inv, d2, d2inv);
s;
if s then
    Interpolation([u : u in F], [l1[u] : u in F]);
    Interpolation([u : u in F], [l2[u] : u in F]);
end if;
