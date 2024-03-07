//Semifields are AssociativeArrays
//Functions are polynomials

pickNonSquare:=function(F)
  for a in F do
    if not IsZero(a) and not IsSquare(a) then
      return a;
    end if;
  end for;
  error "";
end function;

getFF:=function(R)
  x:=R.1;
  return [x^2];
end function;

getA:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  return [x^(p^i+1): i in [1..Floor(n/2)]|IsOdd(n div GCD(n,i))];
end function;

getCMDY:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if p ne 3 or IsEven(n) or (n le 5) then
    return [];
  end if;
  return [x^10+x^6-x^2,x^10-x^6-x^2];
end function;

getCM:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if p ne 3 then
    return [];
  end if;
  return [x^((3^i+1) div 2): i in [3..n]|IsOne(GCD(n,i)) and IsOdd(i)];
end function;

getZKW:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if not IsDivisibleBy(n,3) or not IsOne(GCD(3,(n div 3))) then
    return [];
  end if;
  k:=n div 3;
  ZKW:=[];
  reduceCoefficients:=function(U,s)
    for i:=1 to #U do
      if i gt #U then
        break;
      else
        for a in F do
          j:=Index(U,a^((p^n-2)*(p^s+1)) *U[i]*a^(p^k+p^(2*k+s)) );
          if j gt i then
            Remove(~U,j);
          end if;
        end for;
      end if;
    end for;
    return U;
  end function;
  U:=[u: u in F|not IsZero(u) and Order(u) eq (p^(2*k)+p^k+1)];
  for s:=1 to n do
    if IsZero( (k-s) mod 3) and IsOdd(n div GCD(s,n)) then
      U0:=reduceCoefficients(U,s);
      for u in U0 do
        Append(~ZKW,x^(p^s+1)-u*x^(p^k+p^(2*k+s)));
      end for;
    end if;
  end for;
  return ZKW;
end function;

getB:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if not IsDivisibleBy(n,4) or not IsOne(p^(n div 4) mod 4) then
    return [];
  end if;
  k:=n div 4;
  B:=[];
  reduceCoefficients:=function(U,s)
    for i:=1 to #U do
      if i gt #U then
        break;
      else
        for a in F do
          j:=Index(U,a^((p^n-2)*(p^s+1)) *U[i]*a^(p^(3*k)+p^(k+s)) );
          if j gt i then
            Remove(~U,j);
          end if;
        end for;
      end if;
    end for;
    return U;
  end function;
  U:=[u: u in F|not IsZero(u) and Order(u) eq (p^(3*k)+p^(2*k)+p^k+1)];
  for s:=1 to (3*k) do
    if IsOne( p^s mod 4) and IsOdd((2*k) div GCD(2*k,s)) then
      U0:=reduceCoefficients(U,s);
      for u in U0 do
        Append(~B,x^(p^s+1)-u*x^(p^(3*k)+p^(k+s)));
      end for;
    end if;
  end for;
  return B;
end function;


getBH:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  BH:=[];
  vDyadic:=function(s)
    v:=0;
    while IsEven(s div 2^v) do
      v +:=1;
    end while;
    return v;
  end function;
  b:=pickNonSquare(F);
  o:=F.1;
  for s:=1 to (m-1) do
    if IsZero(s) or not vDyadic(m) eq vDyadic(s) then
      g:=b*x^(p^s+1)+b^(p^m) *x^(p^m *(p^s+1));
      Append(~BH,x^(p^m+1)+o*g);
    end if;
  end for;
  return BH;
end function;

//Op,Op1,Op2 are polynomials
//The semifield is defined over F^2
//These are the semifields that are defined similarly
getFunFromSpecialSemifield:=function(R,Op,Op1,Op2)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  //supposed to be already checked
  m:=n div 2;
  Out:=[];
  for a in GF(p^(2*m)) do
          s:=Eltseq(a);
          s1:=s[1..m];
          s2:=s[(m+1)..2*m];
          a1:=Seqelt(s1,GF(p^m));
          a2:=Seqelt(s2,GF(p^m));
          b1:=Evaluate(Op,a1)+Evaluate(Op1,Evaluate(Op,a2) );
          b2:=2*a1*a2+Evaluate(Op2,a2^2);
          t1:=Eltseq(b1);
          t2:=Eltseq(b2);
          Append(~Out,Seqelt(t1 cat t2,GF(p^(2*m))));
  end for;
  return R!Interpolation([a: a in GF(p^(2*m))],Out);
end function;


getD:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  ns:=pickNonSquare(GF(p^m));
  Op:=y^2;
  Op2:=Zero(RR);
  cop:=[i: i in [1..(m div 2)]];
  return [getFunFromSpecialSemifield(R,Op,ns*y^(p^i) ,Op2): i in cop];
end function;


//There are 2 up to isotopism
getCG:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if p ne 3 or not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  Op:=y^2;
  ns:=pickNonSquare(GF(p^m));
  return [getFunFromSpecialSemifield(R,Op,ns*y+ ns^3 *y^9 ,ns*y^3 )];
end function;

getZP:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  Op2:=Zero(RR);
  ZP:=[];
  ns:=pickNonSquare(GF(p^m));
  cop:=[i: i in [1..(m div 2)]] cat [0];
  for k:=0 to (m div 2) do
    if IsOdd(m div GCD(m,k)) then
      Op:=2*y^(p^k+1);
      for i:=0 to (m div 2) do
        if not [i,k] eq [0,0] then
          Op1:=ns*y^(p^i);
          Append(~ZP,getFunFromSpecialSemifield(R,Op,Op1,Op2));
        end if;
      end for;
    end if;
  end for;
  return ZP;
end function;


getG:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if (n lt 6) or p ne 3 or not IsDivisibleBy(n,2) or IsEven(n div 2) then
    return [];
  end if;
  m:=n div 2;
  Out:=[];
  for a in GF(p^(2*m)) do
          s:=Eltseq(a);
          s1:=s[1..m];
          s2:=s[(m+1)..2*m];
          a1:=Seqelt(s1,GF(p^m));
          a2:=Seqelt(s2,GF(p^m));
          b1:=a1^2-2*a2^10;
          b2:=2*a1*a2+a2^6;
          t1:=Eltseq(b1);
          t2:=Eltseq(b2);
          Append(~Out,Seqelt(t1 cat t2,GF(p^(2*m))));
  end for;
  return [R!Interpolation([a: a in GF(p^(2*m))],Out)];
end function;


getPW:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if [p,n] ne [3,10] then
    return [];
  end if;
  m:=n div 2;
  Out:=[];
  for a in GF(p^(2*m)) do
          s:=Eltseq(a);
          s1:=s[1..m];
          s2:=s[(m+1)..2*m];
          a1:=Seqelt(s1,GF(p^m));
          a2:=Seqelt(s2,GF(p^m));
          b1:=(a1^2+a2^2)^9;
          b2:=2*a1*a2+a2^(2*27);
          t1:=Eltseq(b1);
          t2:=Eltseq(b2);
          Append(~Out,Seqelt(t1 cat t2,GF(p^(2*m))));
  end for;
  return [R!Interpolation([a: a in GF(p^(2*m))],Out)];
end function;

getACW:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not [p,n] eq [3,5] then
    return [];
  end if;
  x:=R.1;
  return x^90 + x^2; 
end function;

// Correct version from Robert
EvaluateMod := function(f,l, FE)
  if IsZero(f) then
    return f;
  else
    return &+[Evaluate(ft, l) mod FE : ft in Terms(f)];
  end if;
end function;

getCHK:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);

  if [p,n] ne [3,8] then
    return [];
  end if;

  FE := x^p^n + 2*x;

  L := x^243 + 2*x^81 + x^9 + x^3 + 2*x;
  D := x^246 + 2*x^10;
  t := x^9 + 2*x;

  f := EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2;

  return [f];
end function;

getCK:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  t := x^(p) -x;
  FE := x^(p^n) -x;
  if [p,n] eq [3,5] then
    L:= -x;
    D:= -x^36 + x^28 + x^12 + x^4; 
  elif [p,n] eq [5,5] then
    D:=Zero(R);
    L:=x^(5^3) + x^(5^2) + 2*x^5 + 3*x;
  else
    return [];
  end if;
  f := EvaluateMod(L, t^2, FE) + EvaluateMod(D, t, FE) + x^2/2;

  return [f];
end function;


//TO FIND some reduction of functions
getGK:=function(R)
  F<u>:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsZero(n mod 4) then 
    return [];
  elif Log(2,(n div 4)) in Integers() then
    return [];
  end if;
  GK:=[];
  m:=n div 2;
  ns:={a: a in GF(p^m)|not IsZero(a) and not IsSquare(a)};
  PowP:={b^(p^m+1): b in GF(p^m)};
  candB:={b: b in GF(p^m)|not b in PowP};
  l:= m div 2;
  for k:=1 to m do
    if IsOdd(m div GCD(k,m)) then
      for a in ns do
        for b in candB do
          Append(~GK,Interpolation([x+u*y:x,y in GF(p^m)],[(x^(p^k+1)+a*y^(p^k+1) )+u*( x^(p^(k+l))*y+b*a^(-1)*y^(p^(k+l))*x ):x,y in GF(p^m)]));
        end for;
      end for;
    end if;
  end for;
  return GK;
end function;

getAllDOPlanar:=function(R)
  return &cat[fun(R): fun in [getA,getACW,getB,getBH,getCG,getCHK,getCK,getCMDY,getCM, getD,getFF,getG,getGK,getPW,getZKW,getZP]];
end function;

getMyFam:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if IsOdd(n) then
    return [];
  end if;
  m:=n div 2;
  if not (IsEven(m) or IsOne(p mod 4)) then
    return [];
  end if;
  q:=p^m;
  Fam:=[];
  for s:=1 to (m-1) do
    if GCD(s,m) eq GCD(s,n) then
      r:=p^s;
      Append(~Fam,x^2-x^(2*r)+x^(q+1)+x^((q+1)*r));
      Append(~Fam,x^2-x^(2*r)-x^(q+1)-x^((q+1)*r));
    end if;
  end for;
  return Fam;
end function;

getMyFamS:=function(R,s)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if IsOdd(n) then
    return [];
  end if;
  m:=n div 2;
  if not (IsEven(m) or IsOne(p mod 4)) or not (GCD(s,m) eq GCD(s,n)) then
    return [];
  end if;
  q:=p^m;
  Fam:=[];
  r:=p^s;
  Append(~Fam,x^2-x^(2*r)+x^(q+1)+x^((q+1)*r));
  Append(~Fam,x^2-x^(2*r)-x^(q+1)-x^((q+1)*r));
  return Fam;
end function;


