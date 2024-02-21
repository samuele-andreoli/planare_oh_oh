load "lib/dupeq.m";
load "lib/semifields.m";
load "lib/planar.m";




RemovePower:=procedure(~Fun)
  if not IsEmpty(Fun) then
    R:=Parent(Fun[1]);
    getFF:=function()
      x:=R.1;
      return [x^2];
    end function;

    getA:=function()
      x:=R.1;
      F:=BaseRing(R);
      n:=Degree(F);
      p:=Characteristic(F);
      return [x^(p^i+1): i in [1..Floor(n/2)]|IsOdd(n div GCD(n,i))];
    end function;
    Mon:=getFF() cat getA();
    for i:=#Fun to 1 by -1 do
      for m in Mon do
        if dupeq(m,Fun[i]:monomial:=true) then
          Remove(~Fun,i);
          break;
        end if;
      end for;
    end for;
  end if;
end procedure;
//also removes all function eq to monomials
ReduceFun:=procedure(~Fun:NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray(),AutomorphismFun:=AssociativeArray())
  testEquivalence:=function(f,g)
    iObol:=IsDefined(OrbitsFun,f);
    jObol:=IsDefined(OrbitsFun,g);
    Nbol:=IsDefined(NucleiFun,f) and IsDefined(NucleiFun,g);
    Abol:=IsDefined(AutomorphismFun,f) and IsDefined(AutomorphismFun,g);
    if Nbol and [#NN:NN in NucleiFun[f]] ne [#NN:NN in NucleiFun[g]] then
      return false;
    elif Abol and AutomorphismFun[f] ne AutomorphismFun[g] then
      return false;
    elif iObol then
      return dupeq_with_l2_representatives(f,g,OrbitsFun[f]);
    elif jObol then
      return dupeq_with_l2_representatives(g,f,OrbitsFun[g]);
    else
      return dupeq(f,g);
    end if;
    error "";
  end function;
  if not IsEmpty(Fun) then
    R:=Parent(Fun[1]);
    for i:=#Fun to 1 by -1 do
      for j:=1 to (i-1) do
        if testEquivalence(Fun[i],Fun[j]) then
          Remove(~Fun,i);
          break;
        end if;
      end for;
    end for;
  end if;
end procedure;

SplitFun:=procedure(~Fun:NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray())

  if not IsEmpty(Fun) then
    R:=Parent(Fun[1]);
    F:=BaseRing(R);
    if IsOdd(Degree(F)) then
      return;
    end if;
    for f in Fun do
      if not IsDefined(NucleiFun,f) then
        NucleiFun[f]:=getNuclei(f,One(F));
      end if;
    end for;

    myIsEquivalent:=function(f,f1)
      if IsDefined(OrbitsFun,f) then
        return dupeq_with_l2_representatives(f,f1,OrbitsFun[f]);
      elif IsDefined(OrbitsFun,f1) then
        return dupeq_with_l2_representatives(f1,f,OrbitsFun[f1]);
      else
        return dupeq(f,f1);
      end if;
    end function;

    getNewSplit:=function(f)
      star:=function(u,v)
          return Evaluate(f,u+v) - Evaluate(f,u) - Evaluate(f,v);
      end function;
      starPsi := Interpolation([star(u,One(F)): u in F],[u: u in F]);

      asterisk := function(u,v)
          return star(Evaluate(starPsi,u),Evaluate(starPsi,v));
      end function;
      N:=NucleiFun[f][1];
      Nm:=NucleiFun[f][2];
      CandidatesB:={Rep({u*b: u in N|not IsZero(u)}): b in (Nm diff N)};
      for b in CandidatesB do
        f1:=Interpolation([u: u in F],[asterisk(asterisk(b,u),u): u in F]);
        if not myIsEquivalent(f,f1) then
          if not isPlanar(f1) then error""; end if;
          return f1;
        end if;
      end for;
      return f;
    end function;
    p:=Characteristic(F);
    NewFun:=[];
    for f in Fun do
      if IsEven(Floor(Log(p,#NucleiFun[f][2])/Log(p,#NucleiFun[f][1]))) then
        f0:=getNewSplit(f);
        Append(~NewFun,f0);
      else
        Append(~NewFun,f);
      end if;
    end for;
    card:=#Fun;
    for i:=card to 1 by -1 do
      if not Fun[i] eq NewFun[i] then
        bolNew:=true;
        for j in Exclude([1..card],i) do
          if ([#NN:NN in NucleiFun[Fun[i]]] eq [#NN:NN in NucleiFun[Fun[j]]]) and myIsEquivalent(Fun[j],NewFun[i]) then
            Remove(~Fun,i);
            bolNew:=false;
            break;
          end if;
        end for;
        if bolNew then
          Append(~Fun,NewFun[i]);
        end if;
      end if;
    end for;
  end if;
end procedure;



load "lib/FamiliesPlanar.m";
n:=8;
F<a>:=GF(3^n);
R<x>:=PolynomialRing(F);
Funs:=[fun(R): fun in [getG,getZP,getCG,getD,getBH,getB,getZKW,getCMDY,getA,getFF]];
myNuclei:=AssociativeArray();
myOrbits:=AssociativeArray();
StrFam:=["G","ZP","CG","D","BH","B","ZKW","CMDY","A","FF"];
for i:=5 to #Funs do
  printf "\n\n\n\n---------\nFamily %o\n\n",StrFam[i];
  printf "removing monomials...";
  RemovePower(~Funs[i]);
  printf "done\n";
  printf "computing invariants...";
  for f in Funs[i] do
    if not IsDefined(myNuclei,f) then
      myNuclei[f]:=getNuclei(f,One(F));
    end if;
    //myOrbits[f]:=partitionByL2(f);
  end for;
  printf "done\n";
  printf "reducing functions...";
  ReduceFun(~Funs[i]:NucleiFun:=myNuclei,OrbitsFun:=myOrbits);
  printf "done\n";
  printf "splitting functions...";
  SplitFun(~Funs[i]:NucleiFun:=myNuclei,OrbitsFun:=myOrbits);
  printf "done\n";
  printf "\nNumber of classes %o",#Funs[i];
end for;
