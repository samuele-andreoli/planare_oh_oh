load "lib/semifields.m";
load "lib/planar.m";
load "lib/representatives.m";
load "lib/invariantTable.m";


// Correct version from Robert
EvaluateMod := function(f,l, FE)
  if IsZero(f) then
    return f;
  else
    return &+[Evaluate(ft, l) mod FE : ft in Terms(f)];
  end if;
end function;

getCHK2:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);

  if [p,n] ne [3,8] then
    return [];
  end if;

  FE := x^p^n + 2*x;

  
  t := x^9 + 2*x;
  CHK:=[];
  L := x^243 + x^9 + x^3;
  D := 2*x^270 + x^90 + 2*x^82;
  Append(~CHK,EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2);

  L := x^243 + 2*x^27 + x^9 + x^3 + x;
  D := 2*x^246 + 2*x^10;
  Append(~CHK,EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2);

  L := 2*x^27 + x^9 + x;
  D := x^270 + x^30 + 2*x^10;
  Append(~CHK,EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2);

  L := x^27 + x^9 + 2*x;
  D := x^270 + x^82 + 2*x^10;
  Append(~CHK,EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2);

  return CHK;
end function;

n:=8;
F:=GF(3^8);
R<x>:=PolynomialRing(F);
CHK:=getCHK2(R);
OrbitsFun:=getOrbitsTable(n);
myRep:=PowerSequence(R)!getRepresentatives(n);
//5,6
for j:=1 to 4 do
    for i in [5,6] do
        f:=myRep[i];
        g:=CHK[j];
        if dupeq_with_l2_representatives(f,g,OrbitsFun[f]) then <i,j>; break; end if;
    end for;
end for;

for f in CHK do
    isPlanar(f);
    Nuclei(f,One(F));
end for;
