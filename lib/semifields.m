DOToSemifieldPoly:=function(f, e)
    assert not IsZero(e);

    F := Parent(e);

    RR<a,b> := PolynomialRing(F,3);
    R0 := PolynomialRing(RR);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b];

    // Fast evaluation of a polynomial and reduction by the field equations.
    EvaluateMod := function(f0,u)
        return &+[NormalForm(Evaluate(t,u), FE) : t in Terms(f0)];
    end function;

    star:=function(u,v)
        return EvaluateMod(f,u+v) - EvaluateMod(f,u) - EvaluateMod(f,v);
    end function;

    starPsi:=R0!Interpolation([F!star(u,e): u in F],[u: u in F]);

    asterisk:=function(u,v)
        return star(EvaluateMod(starPsi,u),EvaluateMod(starPsi,v));
    end function;

    return asterisk(a,b);
end function;

Nuclei:=function(f, e)
    assert not IsZero(e);

    F := Parent(e);

    RR<a,b,c> := PolynomialRing(F,3);
    R0 := PolynomialRing(RR);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b,c^(#F)-c];

    // Fast evaluation of a polynomial and reduction by the field equations.
    EvaluateMod := function(f0,u)
        return &+[NormalForm(Evaluate(t,u), FE) : t in Terms(f0)];
    end function;

    // Construct polynomials for the star and * products
    star:=function(u,v)
        return EvaluateMod(f,u+v) - EvaluateMod(f,u) - EvaluateMod(f,v);
    end function;

    starPsi := R0!Interpolation([F!star(u,e): u in F],[u: u in F]);

    asterisk := function(u,v)
        return star(EvaluateMod(starPsi,u),EvaluateMod(starPsi,v));
    end function;

    // Associativity equation
    fl := asterisk(asterisk(a,b),c);
    fr := Evaluate(fl,[b,c,a]);
    g  := fl-fr;

    // Max order of a non trivial (Fq) nucleus
    p:=Characteristic(F);
    D:=Divisors(Degree(F));
    MaxOrder:=p^D[#D-1]+1;

    mn:=0;
    rn:=0;
    for u in F do
        if mn eq MaxOrder then
            return [#F,#F];
        end if;

        if IsZero(Evaluate(g,[a,b,u])) then
            rn +:=1;
            mn +:=1;
        elif IsZero(Evaluate(g,[a,u,b])) then
            mn +:=1;
        end if;
    end for;

    return [rn,mn];
end function;

getNuclei:=function(f, e)
    assert not IsZero(e);

    F := Parent(e);

    RR<a,b,c> := PolynomialRing(F,3);
    R0 := PolynomialRing(RR);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b,c^(#F)-c];

    // Fast evaluation of a polynomial and reduction by the field equations.
    EvaluateMod := function(f0,u)
        return &+[NormalForm(Evaluate(t,u), FE) : t in Terms(f0)];
    end function;

    // Construct polynomials for the star and * products
    star:=function(u,v)
        return EvaluateMod(f,u+v) - EvaluateMod(f,u) - EvaluateMod(f,v);
    end function;

    starPsi := R0!Interpolation([F!star(u,e): u in F],[u: u in F]);

    asterisk := function(u,v)
        return star(EvaluateMod(starPsi,u),EvaluateMod(starPsi,v));
    end function;

    // Associativity equation
    fl := asterisk(asterisk(a,b),c);
    fr := Evaluate(fl,[b,c,a]);
    g  := fl-fr;

    // Max order of a non trivial (Fq) nucleus
    p:=Characteristic(F);
    D:=Divisors(Degree(F));
    Nm:={};
    N:={};

    mn:=0;
    rn:=0;
    for u in F do
        if IsZero(Evaluate(g,[a,b,u])) then
            Include(~N,u);
            Include(~Nm,u);
        elif IsZero(Evaluate(g,[a,u,b])) then
            Include(~Nm,u);
        end if;
    end for;

    return [N,Nm];
end function;
