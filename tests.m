load "lib/FamiliesPlanar.m";
load "lib/planar.m";
for n:=2 to 8 do
  printf "test dimension %o\n",n;
  p:=3;
  F:=GF(p^n);
  R:=PolynomialRing(F);
  Fam:=getAllDOPlanar(R);
  FFs:=getFFs(F);
  for f in Fam do
    if not fastIsPlanarDOPoly(f,FFs) then error""; end if;
  end for;
end for;
