n:=4;
p:=3;
F:=GF(p^n);
R:=PolynomialRing(F);
Fam:=getAllPlanar(R);
FFs:=getFFs(F);
for f in Fam do
  fastIsPlanarDOPoly(f);
end for;
