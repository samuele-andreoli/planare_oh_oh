load "lib/FamiliesPlanar.m";
load "lib/planar.m";

for n:=8 to 8 do
  printf "test dimension %o\n",n;
  p:=3;
  F:=GF(p^n);
  R:=PolynomialRing(F);
  Fam:=getAllDOPlanar(R);
  FFs:=getD(R);
  for f in Fam do
    if not fastIsPlanarDOPoly(f,FFs) then error Sprintf("D %o", f); end if;
  end for;
  FFs:=getCG(R);
  for f in Fam do
    if not fastIsPlanarDOPoly(f,FFs) then error Sprintf("CG %o", f); end if;
  end for;
  FFs:=getZP(R);
  for f in Fam do
    if not fastIsPlanarDOPoly(f,FFs) then error Sprintf("ZP %o", f); end if;
  end for;
end for;
