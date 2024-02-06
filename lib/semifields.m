DOToSemifieldPoly:=function(f, e)
    F := Parent(e);
    if IsZero(e) then error "e is zero"; end if;
    RR<a,b>:=PolynomialRing(F,2);
    R0:=PolynomialRing(RR);
    f:=R0!f;
    FE:=[a^(#F)-a,b^(#F)-b];
    Ev:=function(f0,u)
      r:=Zero(Parent(u));
      for t in Terms(f0) do
        r+:=NormalForm(Evaluate(t,u),FE);
      end for;
      return r;
    end function;
    star:=function(u,v)
      return Ev(f,u+v)-Ev(f,u)-Ev(f,v);
    end function;
    starPsi:=R0!Interpolation([F!star(u,e): u in F],[u: u in F]);
    asterisk:=function(u,v)
      return star(Ev(starPsi,u),Ev(starPsi,v));
    end function;
    return asterisk(a,b);
end function;

PrecomputeSubfields := function(F)
    n := Degree(F);

    divisors := Divisors(n);

    Reverse(~divisors);
    subfields := [{x : x in sub<F|d> | not IsZero(x)} : d in divisors];
    sizes := [#s +1: s in subfields];

    Reverse(~divisors);
    for i := 1 to #divisors do
        to_remove := {x : x in sub<F|divisors[i]>};

        for j := 1 to #subfields-i do
            subfields[j] diff:= to_remove;
        end for;
    end for;

    return subfields, sizes;
end function;

CombineSubfieldsWithIdentity := function(S, e)
    combined := [];
    for s in S do
        Append(~combined, {e*si : si in s});
    end for;

    return combined;
end function;

Nuclei:=function(f, e,subfields, sizes)
    F := Parent(e);
    if IsZero(e) then error "e is zero"; end if;
    RR<a,b,c>:=PolynomialRing(F,3);
    R0:=PolynomialRing(RR);
    f:=R0!f;
    FE:=[a^(#F)-a,b^(#F)-b,c^(#F)-c];
    Ev:=function(f0,u)
      r:=Zero(Parent(u));
      for t in Terms(f0) do
        r+:=NormalForm(Evaluate(t,u),FE);
      end for;
      return r;
    end function;
    star:=function(u,v)
      return Ev(f,u+v)-Ev(f,u)-Ev(f,v);
    end function;
    starPsi:=R0!Interpolation([F!star(u,e): u in F],[u: u in F]);
    asterisk:=function(u,v)
      return star(Ev(starPsi,u),Ev(starPsi,v));
    end function;
    fl:=asterisk(asterisk(a,b),c);
    fr:=asterisk(a,asterisk(b,c));
    g:=fl-fr;
    cosets := CombineSubfieldsWithIdentity(subfields,star(e,e));
    for cos in cosets do
        if IsZero(Evaluate(g,[a,Rep(cos),c])) then
          remaining_cosets := cosets[Index(cosets, cos)..#cosets];
          mn := sizes[Index(cosets, cos)];
          break;
        end if;
    end for;
    for cos in remaining_cosets do
        if IsZero(Evaluate(g,[a,b,Rep(cos)])) then
          remaining_cosets := cosets[Index(cosets, cos)..#cosets];
          rn := sizes[Index(cosets, cos)];
          break;
        end if;
    end for;
    return [rn,mn];
end function;
