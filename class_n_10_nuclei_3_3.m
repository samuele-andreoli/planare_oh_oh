load "lib/familiesPlanar.m";
load "lib/dupeq.m";

i := 1; // to 4

F<a> := GF(3^10);
R<x> := PolynomialRing(F);

getZP_rest:=function(R)
    F:=BaseRing(R);
    p:=Characteristic(F);
    n:=Degree(F);

    if not IsDivisibleBy(n,2) then
        return [];
    end if;

    m:=n div 2;
    Fq := GF(p^m);

    ZP:=[];
    ns:=pickNonSquare(GF(p^m));

    for k in [1..(m div 2)] do
        OpTT := AssociativeArray();

        for a in Fq do
            OpTT[a] := 2*a^(p^k+1);
        end for;

        Append(~Op, OpTT);

        if IsEven(m div GCD(m,k)) then
        continue;
        end if;
        
        Op1TT := AssociativeArray();
        for a in Fq do
            Op1TT[a] := ns * a^(p^k);
        end for;

        Append(~Op1, Op1TT);
    end for;

  for OpTT in Op do
    for Op1TT in Op1 do
      Append(~ZP, getFunFromSpecialSemifieldTT_zero_op2(R, OpTT, Op1TT));
    end for;
  end for;

  return ZP;
end function;

ganley := getGTT(R);
gTT := ganley[1];

invgTT := AssociativeArray();
for k->v in gTT do
    // Really hope magma short circuits.
    if not (IsDefined(invgTT, v) and (k ge invgTT[v])) then
        invgTT[v] := k;
    end if;
end for;

zhoupott := getZP_rest(R);
zTT := zhoupott[i];

invzTT := AssociativeArray();
for k->v in zTT do
    // Really hope magma short circuits.
    if not (IsDefined(invzTT, v) and (k ge invzTT[v])) then
        invzTT[v] := k;
    end if;
end for;

s, l1, l2 := dupeq_tt(gTT, invgTT, zTT, invzTT);
if s then 
    printf "Eqiuvalent to %o\n", z;
    Interpolation([u : u in F], [l1[u] : u in F]);
    Interpolation([u : u in F], [l2[u] : u in F]);
end if;
