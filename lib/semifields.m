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


getNuclei:=function(f, e)
    assert not IsZero(e);

    F := BaseRing(Parent(f));
    n:=Degree(F);
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
    id:=star(e,e);
    astrP:=Evaluate(fl,[a,b,id]);
    Nm:={id*a: a in PrimeField(F)};
    N:=Nm;
    dN:=1;
    dNm:=dN;
    dnextN:=Divisors(n)[2];
    dnextNm:=dnextN;
    uN:=#F;
    uNm:=uN;
    SpanNuclei:=procedure(~M,~dM,u)
        u0:=u;
        M0:=M;
        dM0:=dM;
        while not u0 in M do
            dM *:=dM0;
            M1:=M;
            for a in M0 do
                if not IsZero(a) then
                    a1:=asterisk(a,u0);
                    for b1 in M1 do
                        Include(~M,a1+b1);
                    end for;
                end if;
            end for;
            u0:=Evaluate(astrP,[u,u0,id]);
        end while;
    end procedure;
    flagN:=true;
    flagNm:=true;
    for u in F do
        if flagN and not u in N and IsZero(Evaluate(g,[a,b,u])) then
            SpanNuclei(~N,~dN,u);
            if dN eq n then
                Nm:=N;
                break;
            else
                dnextN:=Divisors(n div dN)[2];
            end if;
            SpanNuclei(~Nm,~dNm,u);
            if dNm eq n then
                break;
            else
                dnextNm:=Divisors(n div dNm)[2];
            end if;
        elif flagNm and not u in Nm and IsZero(Evaluate(g,[a,u,b])) then
            uN -:=1;
            if flagN and Log(p,uN) lt dnextN then
                flagN:=false;
            end if;
            SpanNuclei(~Nm,~dNm,u);
            if dNm eq n then
                break;
            else
                dnextNm:=Divisors(n div dNm)[2];
            end if;
        else
            uN -:=1;
            uNm -:=1;
            if flagN and Log(p,uN) lt dnextN then
                flagN:=false;
            end if;
            if flagNm and Log(p,uNm) lt dnextNm then
                flagNm:=false;
            end if;
        end if;
        if not (flagN or flagNm) then
            break;
        end if;
    end for;
    return [N,Nm];
end function;


Nuclei:=function(f, e)
    NN:=getNuclei(f,e);
    return [#NN[1],#NN[2]];
end function;
