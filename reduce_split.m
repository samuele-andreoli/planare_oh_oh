load "lib/dupeq.m";
load "lib/semifields.m";
load "lib/planar.m";
load "lib/FamiliesPlanar.m";
load "lib/representatives.m";

isMonomial:=function(f)
  return #SequenceToSet(Coefficients(f)) eq 2;
end function;


//Functions that are not power but are equivalent to monomials
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
        if not isMonomial(Fun[i]) and dupeq(m,Fun[i]:monomial:=true) then
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
      if isMonomial(f) then
        return dupeq(f,g:monomial:=true);
      elif isMonomial(g) then 
        return dupeq(g,f:monomial:=true);
      else
        return dupeq(g,f);
      end if;
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

SplitFun:=procedure(~Fun,~NucleiFun,OrbitsFun:=AssociativeArray())

  if IsEmpty(Fun) then
    return;
  end if;

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
      if isMonomial(f) then
        return dupeq(f,g:monomial:=true);
      elif isMonomial(g) then 
        return dupeq(g,f:monomial:=true);
      else
        return dupeq(g,f);
      end if;
    end if;
    error "";
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
    CandidatesB:={Rep({asterisk(u,b): u in N|not IsZero(u)}): b in (Nm diff N)};
    for b in CandidatesB do
      f1:=Interpolation([u: u in F],[asterisk(asterisk(b,u),u): u in F]);
      if not testEquivalence(f,f1) then
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
      NucleiFun[f0]:=NucleiFun[f];
    else
      Append(~NewFun,f);
    end if;
  end for;
  card:=#Fun;
  for i:=card to 1 by -1 do
    if not Fun[i] eq NewFun[i] then
      bolNew:=true;
      for j in Exclude([1..card],i) do
        if testEquivalence(Fun[j],NewFun[i]) then
          bolNew:=false;
          break;
        end if;
      end for;
      if bolNew then
        Append(~Fun,NewFun[i]);
      end if;
    end if;
  end for;
end procedure;

//I assume that Funs have already been in the previous steps
listIntersectionsFam:=function(Funs, StrFam :NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray(),AutomorphismFun:=AssociativeArray())
  allFun:=[];
  FamList:=AssociativeArray();
  for i:=1 to #Funs do
    for f in Funs[i] do
      FamList[f]:=[StrFam[i]];
    end for;
  end for;
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
      if isMonomial(f) then
        return dupeq(f,g:monomial:=true);
      elif isMonomial(g) then 
        return dupeq(g,f:monomial:=true);
      else
        return dupeq(g,f);
      end if;
    end if;
    error "";
  end function;
  for i:=1 to #Funs do
    for f in Funs[i] do
      for j:=(i+1) to #Funs do
        for g in Funs[j] do
          if testEquivalence(f,g) then
            Exclude(~Funs[j]
            NewFams:=FamList[f] cat FamList[g];
            for fam in NewFams do
              Include(~FamList[f],fam);
              Include(~FamList[g],fam);
            end for;
          end if;
        end for;
      end for;
    end for;
  end for;
  return FamList;
end function;


ReducePolyForm:=function(f)
  R:=Parent(f);
  F:=BaseRing(R);
  return R!Interpolation([u: u in F],[Evaluate(f,u): u in F]);
end function;


ClassifyFun:=procedure(n)
  F<a>:=GF(3^n);
  R<x>:=PolynomialRing(F);
  Funs:=[fun(R): fun in [getG,getZP,getCG,getD,getBH,getB,getZKW,getCMDY,getA,getFF]];
  Funs:=[[ReducePolyForm(f): f in Fun]: Fun in Funs];
  myNuclei:=AssociativeArray();
  myOrbits:=AssociativeArray();
  myAuthomorphisms:=AssociativeArray();
  StrFam:=["G","ZP","CG","D","BH","B","ZKW","CMDY","A","FF"];
  for i:=1 to #Funs do
    printf "\n\n\n\n---------\nFamily %o\n\n",StrFam[i];
    printf "removing monomials...";
    RemovePower(~Funs[i]);
    printf "done\n";
    printf "computing invariants...";
    for f in Funs[i] do
      if not IsDefined(myNuclei,f) then
        myNuclei[f]:=getNuclei(f,One(F));
      end if;
    end for;
    printf "done\n";
    printf "reducing functions...";
    ReduceFun(~Funs[i]:NucleiFun:=myNuclei,OrbitsFun:=myOrbits,AuthomorphismsFun:=myAuthomorphisms);
    printf "done\n";
    printf "splitting functions...";
    SplitFun(~Funs[i],~myNuclei:OrbitsFun:=myOrbit,AuthomorphismsFun:=myAuthomorphisms);
    printf "done\n";
    printf "\nNumber of classes %o",#Funs[i];
  end for;
  printf "completing invariants..";
  for f in &cat(Funs) do
    if not IsDefined(myNuclei,f) then
      myNuclei[f]:=getNuclei(f,One(F));
    end if;
  end for;
  printf "done\n";
  printf "\n\n\n\n---------\nCheck intersections between families\n\n";
  FamList:=listIntersectionsFam(Funs, StrFam :NucleiFun:=myNuclei,OrbitsFun:=myOrbits,AuthomorphismsFun:=myAuthomorphisms);
  
  myRep:=PowerSequence(R)!getRepresentatives(n);
  for f in myRep do
    for g in Keys(FamList)
  
end procedure;
