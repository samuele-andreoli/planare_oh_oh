//Semifields are AssociativeArrays
//Functions are polynomials


PresemifieldToDO:=function(PSF)
  F:=Parent(Rep(Keys(PSF)));
  return Interpolation([a: a in F],[PSF[{a,a}]/2: a in F]);
end function;


DOtoPresemifield:=function(f)
  F:=BaseRing(Parent(f));
  PSF:=AssociativeArray();
  for a,b in F do
    if not {a,b} in Keys(PSF) then
      PSF[{a,b}]:=Evaluate(f,a+b)-Evaluate(f,a)-Evaluate(f,b);
    end if;
  end for;
  return PSF;
end function;

PresemifieldToSemifield:=function(PSF,e)
  if IsZero(e) then error "e is zero"; end if;
  SF:=AssociativeArray();
  F:=Parent(e);
  for a,b in F do
    a0:=PSF[{a,e}];
    b0:=PSF[{b,e}];
    if not {a0,b0} in Keys(SF) then
      SF[{a0,b0}]:=PSF[{a,b}];
    end if;
  end for;
  return SF;
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
  if p ne 3 or IsEven(n) then
    return [];
  end if;
  return [x^10+x^6-x^2,x^10-x^6-x^2];
end function;

getCMH:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if p ne 3 then
    return [];
  end if;
  return [x^((3^i+1) div 2): i in [3..n]|IsOne(GCD(n,i))];
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
  U:=[u: u in F|not IsZero(u) and Order(u) eq (p^(2*k)+p^k+1)];
  for s:=1 to n do
    if IsZero( (k+s) mod 3) and IsOdd(n div GCD(s,n)) then
      for u in U do
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
  U:=[u: u in F|not IsZero(u) and Order(u) eq (p^(3*k)+p^(2*k)+p^k+1)];
  for s:=1 to n do
    if IsOne( p^s mod 4) and IsOdd((2*k) div GCD(2*k,s)) then
      for u in U do
        Append(~B,x^(p^s+1)-u*x^(p^(3*k)+p^(k+s)));
      end for;
    end if;
  end for;
  return B;
end function;

getBHB:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  n:=Degree(F);
  p:=Characteristic(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  BHB:=[];
  O:={o: o in F|not IsZero(o) and IsZero(o^(p^m)+o)};
  o:=Rep(O);
  ConditionBHB:=function(s)
    for a in O do
      if IsZero(a^(p^s)+a) then
        return false;
      end if;
    end for;
    return true;
  end function;
  for s:=1 to m do
    if ConditionBHB(s) then
      orderB:=(p^m+1) div GCD(p^m+1,p^s+1);
      for b in F do
        if not IsZero(b) and not (IsDivisibleBy(orderB,Order(b^(p^m-1)))) then
          g:=b*x^(p^s+1)+b^(p^m) *x^(p^m *(p^s+1));
          Append(~BHB,x^(p^m+1)+o*g);
        end if;
      end for;
    end if;
  end for;
  return BHB;
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

//TO CHECK
getD:=function(R)
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if not IsDivisibleBy(n,2) then
    return [];
  end if;
  m:=n div 2;
  RR<y>:=PolynomialRing(GF(p^m));
  Op:=y^2;
  Op2:=Zero(RR);
  cop:=[i: i in [1..(m-1)]|IsOne(GCD(i,m))];
  return [getFunFromSpecialSemifield(R,Op,a*y^(p^i) ,Op2): a in GF(p^m), i in cop|not IsZero(a) and not IsSquare(a)];
end function;

//TO CHECK
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
  return [getFunFromSpecialSemifield(R,Op1,ay^3, a*y+a^3 *y^9 ): a in GF(p^m)|not IsZero(a) and not IsSquare(a)];
end function;

//TO CHECK
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
  ns:=[a: a in GF(p^m)|not IsZero(a) and not IsSquare(a)];
  cop:=[i: i in [1..(m-1)]|IsOne(GCD(i,m))];
  for k:=1 to m do
    if IsOdd(m div GCD(m,k)) then
      Op:=2*y^(p^k+1);
      for i in cop do
        for a in ns do
          Op1:=a*y^(p^i);
          Append(~ZP,getFunFromSpecialSemifield(R,Op,Op1,Op2));
        end for;
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

getAllDOPlanar:=function(R)
  return &cat[fun(R): fun in [getG,getZP,getCG,getD,getBHB,getB,getZKW,getCMDY,getA,getFF]];
end function;

//it is our version
getCHK:=function(R)
  x:=R.1;
  F:=BaseRing(R);
  p:=Characteristic(F);
  n:=Degree(F);
  if [p,n] ne [3,8] then
    return [];
  end if;
  return [x^2-x^6+x^82+x^246];
end function;
