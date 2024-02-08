load "lib/representatives.m";
load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";
load "lib/semifields.m";

R<x>:=PolynomialRing(GF(3^8));
//The families of DO for 3^8 are FF,D,BHB,B,ZP,CG
// Functions D are not in the classification, but according to their nuclei they are either 8.8, 8.9, or 8.9
myRep:=PowerSequence(R)!getRepresentatives(8);




//CG TODO
f1:=myRep[9];
f2:=myRep[10];
CG:=getCG(R);

i:=0;
for f in CG do
        i +:=1;
        i;
        N:=Nuclei(f,One(GF(3^8)));
        if N eq [3,81] then
                if dupeq(f,f1) then
                        Exclude(~CG,f);
                elif dupeq(f,f2) then
                        Exclude(~CG,f);
                end if;
        else
                N;
        end if;
end for;



//BHB OK
f1:=myRep[5];
f2:=myRep[6];
f3:=myRep[7];
BHB:=getBHB(R);

for f in BHB do
        if dupeq(f,f1) then
                Exclude(~BHB,f);
        elif dupeq(f,f2) then
                Exclude(~BHB,f);
        elif dupeq(f,f3) then
                Exclude(~BHB,f);
        end if;
end for;


//B OK
f0:=myRep[6];
B:=getB(R);

for f in B do
        if dupeq(f,f0) then
                Exclude(~B,f);
        end if;
end for;

//ZP OK
f0:=myRep[8];
ZP:=getZP(R)[1..2]; //The third one is FF
for f in ZP do
        if dupeq(f,f0) then
                Exclude(~ZP,f);
        end if;
end for;


//D
f1:=myRep[8];
f2:=myRep[9];
f3:=myRep[10];
D:=getD(R)[1..2]; //the third one is FF
for f in D do
        if dupeq(f,f1) then
                Exclude(~D,f);
        elif dupeq(f,f2) then
                Exclude(~D,f);
        elif dupeq(f,f3) then
                Exclude(~D,f);
        end if;
end for;


