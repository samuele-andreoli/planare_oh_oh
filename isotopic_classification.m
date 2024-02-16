load "lib/representatives.m";
load "lib/dupeq.m";
load "lib/semifields.m";
load "lib/planar.m";
load "lib/invariantTable.m";


for n:=2 to 8 do
	OrbitsTable:=getOrbitsTable(n);
  F<a>:=GF(3^n);
  R<x>:=PolynomialRing(F);
  Fun:=PowerSequence(R)!getRepresentatives(n);
  E:={u: u in F|not IsZero(u)};
  for i:=1 to #Fun do
    f:=Fun[i];
    printf "\n%o.%o\t",n,i;
    star:=function(u,v)
        return Evaluate(f,u+v) - Evaluate(f,u) - Evaluate(f,v);
    end function;
    if isDOPolynomial(f) then
			CardN:=Nuclei(f,One(F));
			if IsEven(Floor(Log(3,CardN[2])/Log(3,CardN[1]))) then
				printf"CH candidate\t";
				flag:=false;
				e:=One(F);
				starPsi := Interpolation([star(u,e): u in F],[u: u in F]);

				asterisk := function(u,v)
					  return star(Evaluate(starPsi,u),Evaluate(starPsi,v));
				end function;
				CandidatesB:={Rep({u*b: u in N|not IsZero(u)}): b in (Nm diff N)};
				for b in CandidatesB do
					f1:=Interpolation([u: u in F],[asterisk(asterisk(b,u),u): u in F]);
					//the second dupeq is to double check
					if not dupeq_with_l2_representatives(f,f1,OrbitsTable[f]) and not dupeq(f,f1) then
					  printf "splits\t";
					  if not isPlanar(f1) then error""; end if;
					  f1;
					  flag:=true;
					  break;
					end if;
				end for;
				if not flag then
					printf "does not split";
				end if;
			end if;
		end if;
  end for;
end for;
