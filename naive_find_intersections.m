clear;
load "lib/representatives.m";
load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";
load "lib/semifields.m";

isMonomial:=function(f)
	return #SequenceToSet(Coefficients(f)) le 2;
end function;

StrFam:=["G","ZP","CG","D","BH","B","ZKW","CMDY","A","FF"];
for n:=2 to 8 do	
	R<x>:=PolynomialRing(GF(3^n));
	myRep:=PowerSequence(R)!getRepresentatives(n);
	Funs:=[fun(R): fun in [getG,getZP,getCG,getD,getBHB,getB,getZKW,getCMDY,getA,getFF]];
	printf "Number of functions =%o\n",#(&cat(Funs));
	for i:=1 to #myRep do
		f:=myRep[i];
		bol1:=isMonomial(f);
		printf "\n%o.%o\t",n,i;
		for j:=1 to #Funs do
			for g in Funs[j] do
				if bol1 then
					if dupeq(f,g:monomial:=true) then
						printf "%o\t",StrFam[j];
						break;
					end if;
				elif  isMonomial(g) then
					if dupeq(g,f:monomial:=true) then
						printf "%o\t",StrFam[j];
						break;
					end if;
				elif dupeq(f,g) then
					printf "%o\t",StrFam[j];
					break;
				end if;
			end for;
		end for;
	end for;
end for;
