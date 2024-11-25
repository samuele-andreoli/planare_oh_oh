load "lib/dupeq.m";
load "lib/semifields_polynomial.m";
load "lib/planar.m";
load "lib/familiesPlanar.m";
load "lib/representatives.m";
load "lib/invariantTable.m";

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

testEquivalence:=function(f,g:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun)
    iObol:=IsDefined(OrbitsFun,f);
    jObol:=IsDefined(OrbitsFun,g);
    Nbol:=IsDefined(NucleiFun,f) and IsDefined(NucleiFun,g);
    Abol:=IsDefined(AutomorphismsFun,f) and IsDefined(AutomorphismsFun,g);

    if Nbol and [#NN:NN in NucleiFun[f]] ne [#NN:NN in NucleiFun[g]] then
      return false;
    elif Abol and AutomorphismsFun[f] ne AutomorphismsFun[g] then
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


//this is to check dupeq_with_...
testEquivalenceFlag:=function(f,g:NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray(),AutomorphismsFun:=AssociativeArray())
  iObol:=IsDefined(OrbitsFun,f);
  jObol:=IsDefined(OrbitsFun,g);
  Nbol:=IsDefined(NucleiFun,f) and IsDefined(NucleiFun,g);
  Abol:=IsDefined(AutomorphismsFun,f) and IsDefined(AutomorphismsFun,g);

  if Nbol and [#NN:NN in NucleiFun[f]] ne [#NN:NN in NucleiFun[g]] then
    return false;
  elif Abol and AutomorphismsFun[f] ne AutomorphismsFun[g] then
    return false;
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



ReduceFun:=procedure(~Fun:NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray(),AutomorphismsFun:=AssociativeArray())
  if not IsEmpty(Fun) then
    R:=Parent(Fun[1]);
    for i:=#Fun to 1 by -1 do
      for j:=1 to (i-1) do
        if testEquivalence(Fun[i],Fun[j]:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun) then
          Remove(~Fun,i);
          break;
        end if;
      end for;
    end for;
  end if;
  Fun:=SetToSequence(SequenceToSet(Fun));
end procedure;

ReduceRepFun:=procedure(~Fun,myRep:NucleiFun:=AssociativeArray(),OrbitsFun:=AssociativeArray(),AutomorphismsFun:=AssociativeArray())
  if not IsEmpty(Fun) then
    R:=Parent(Fun[1]);
    for i:=#Fun to 1 by -1 do
      f:=Fun[i];
      if not f in myRep then
        flag:=true;
        for g in myRep do
          if isDOPolynomial(g) and testEquivalence(f,g:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun) then
            Fun[i]:=g;
            flag:=false;
            break;
          end if;
        end for;
        if flag then 
          printf "\n\n function %o is new !!!",f;
          //this is to check dupeq_with_...
          for g in myRep do
            if isDOPolynomial(g) and testEquivalenceFlag(f,g:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun) then
              error "";
            end if;
          end for; 
        end if;
      end if;
    end for;
  end if;
  Fun:=SetToSequence(SequenceToSet(Fun));
end procedure;


SplitFun:=procedure(~Fun,~NucleiFun:OrbitsFun:=AssociativeArray(),AutomorphismsFun:=AssociativeArray())

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
      NucleiFun[f]:=getNuclei(f);
    end if;
  end for;

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
      if not testEquivalence(f,f1:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun) then
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
        if testEquivalence(Fun[j],NewFun[i]:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun) then
          bolNew:=false;
          break;
        end if;
      end for;
      if bolNew then
        Append(~Fun,NewFun[i]);
      end if;
    end if;
  end for;
  Fun:=SetToSequence(SequenceToSet(Fun));
end procedure;
ReducePolyForm:=function(f)
  R:=Parent(f);
  F:=BaseRing(R);
  return R!Interpolation([u: u in F],[Evaluate(f,u): u in F]);
end function;


ClassifyFun:=procedure(n)
  NucleiFun:=getNucleiTable(n);
  OrbitsFun:=getOrbitsTable(n);
  AutomorphismsFun:=AssociativeArray();
  R<x>:=Parent(Rep(Keys(OrbitsFun)));
  F<a>:=BaseRing(R);
  myRep:=PowerSequence(R)!getRepresentatives(n);
  assert Keys(OrbitsFun) subset SequenceToSet(myRep);
  printf "\ncomputing invariants of my representatives...";
  for f in myRep do 
    if isDOPolynomial(f) and not IsDefined(NucleiFun,f) then
      NucleiFun[f]:=getNuclei(f);
    end if; 
  end for;
  printf "done\n";
  //Removed CM
  Funs:=[fun(R): fun in [getA,getACW,getB,getBH,getCG,getCHK,getCK,getCMDY, getD,getFF,getG,getGK,getPW,getZKW,getZP]];
  Funs:=[[ReducePolyForm(f): f in Fun]: Fun in Funs];
  StrFam:=["A", "ACW", "B", "BH", "CG", "CHK", "CK", "CMDY", "D", "FF", "G", "GK", "PW", "ZKW", "ZP"];
  printf "\n\nNumber of functions %o\n",#(&cat(Funs));
  for i:=1 to #Funs do
    printf "\n\n\n---------\nFamily %o\n\n",StrFam[i];
    printf "removing monomials...";
    RemovePower(~Funs[i]);
    printf "done\t Number of functions %o\n",#Funs[i];
    printf "reducing functions with respect to my representatives...";
    ReduceRepFun(~Funs[i],myRep:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun);
    printf "done\t Number of functions %o\n",#Funs[i];
    for f in Funs[i] do
       if  not IsDefined(NucleiFun,f) then
        NucleiFun[f]:=getNuclei(f);
      end if;
    end for;
    printf "reducing functions...";
    ReduceFun(~Funs[i]:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun);
    printf "done\t Number of functions %o\n",#Funs[i];
    printf "splitting functions...";
    SplitFun(~Funs[i],~NucleiFun:OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun);
    printf "done\t Number of functions %o\n",#Funs[i];
    for f in Funs[i] do
      if not IsDefined(NucleiFun,f) then
        NucleiFun[f]:=getNuclei(f);
      end if;
    end for;
    printf "reducing functions with respect to my representatives...";
    ReduceRepFun(~Funs[i],myRep:NucleiFun:=NucleiFun,OrbitsFun:=OrbitsFun,AutomorphismsFun:=AutomorphismsFun);
    printf "done\t Number of functions %o\n",#Funs[i];
  end for;
  printf "\n\n\n---------\nCheck intersections between families\n\n";
  for i:=1 to #myRep do
    printf "\n%o.%o\t",n,i;
    f:=myRep[i];
    for j:=1 to #Funs do
      if f in Funs[j] then
        printf "%o\t",StrFam[j];
      end if;
    end for;
  end for;
end procedure;

ClassifyFun(8);
