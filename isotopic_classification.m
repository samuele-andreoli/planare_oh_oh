load "lib/representatives.m";
load "lib/dupeq.m";
load "lib/semifields.m";
load "lib/planar.m";
for n:=2 to 8 do
  F<a>:=GF(3^n);
  R<x>:=PolynomialRing(F);
  Fun:=PowerSequence(R)!getRepresentatives(n);
  e:=One(F);
  for i:=1 to #Fun do
    f:=Fun[i];
    printf "\n%o.%o\t",n,i;
    star:=function(u,v)
        return Evaluate(f,u+v) - Evaluate(f,u) - Evaluate(f,v);
    end function;

    starPsi := Interpolation([star(u,e): u in F],[u: u in F]);

    asterisk := function(u,v)
        return star(Evaluate(starPsi,u),Evaluate(starPsi,v));
    end function;
    if isDOPolynomial(f) then
		  N,Nm:=getNuclei(f,e);
		  if IsEven(Floor(Log(3,#Nm)/Log(3,#N))) then
		    printf"CH candidate\t";
		    bol:=true;
		    for b in Nm diff N do
		      f1:=Interpolation([u: u in F],[asterisk(asterisk(b,u),u): u in F]);
		      //if not isPlanar(f1) then error""; end if;
		      if not dupeq(f,f1) then
		        printf "splits\t";
		        if not isPlanar(f1) then error""; end if;
		        f1;
		        bol:=false;
		        break;
		      end if;
		    end for;
		    if bol then
		      printf "does not split";
		    end if;
		  end if;
    end if;
  end for;
end for;
