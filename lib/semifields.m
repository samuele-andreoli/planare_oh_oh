DOToSemifieldPoly:=function(f, e)
    assert not IsZero(e);

    F := Parent(e);

    RR<a,b> := PolynomialRing(F,2);
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
    id:=star(e,e);
    // Associativity equation
    astrP:=asterisk(a,b);
    fl :=asterisk(astrP,c);
    fr := Evaluate(fl,[b,c,a]);
    g  := fl-fr;

    // Max order of a non trivial (Fq) nucleus
    p:=Characteristic(F);
    D:=Divisors(Degree(F));
    Nm:={id*a: a in PrimeField(F)};
    N:=Nm;
    dN:=1;
    dNm:=dN;
    nextN:=p^Divisors(n)[2];
    nextNm:=nextN;
    uN:=#F;
    uNm:=uN;

    UpdateFlag:=procedure(~flagM,uM,nextM)
        flagM:=uM ge nextM;
    end procedure;

    UpdateNextDimension:=procedure(~nextM,dM)
        nextM:=p^(dM*Divisors(n div dM)[2]);
    end procedure;

    SpanNuclei:=procedure(~M,~dM,u)
        u0:=u;
        M0:=M;
        dM0:=dM;
        while not u0 in M do
            dM +:=dM0;
            M1:=M;
            for a in M0 do
                if not IsZero(a) then
                    a1:=Evaluate(astrP,[a,u0,id]);
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
                UpdateNextDimension(~nextN,dN);
                UpdateFlag(~flagN,uN,nextN);
            end if;

            SpanNuclei(~Nm,~dNm,u);
            if dNm eq n then
                break;
            else
                UpdateNextDimension(~nextNm,dNm);
                UpdateFlag(~flagNm,uNm,nextNm);
            end if;
        elif flagNm and not u in Nm and IsZero(Evaluate(g,[a,u,b])) then
            uN -:=1;
            SpanNuclei(~Nm,~dNm,u);
            if dNm eq n then
                break;
            else
                UpdateNextDimension(~nextNm,dNm);
                UpdateFlag(~flagNm,uNm,nextNm);
            end if;
        else
            uN -:=1;
            uNm -:=1;
            UpdateFlag(~flagN,uN,nextN);
            UpdateFlag(~flagNm,uNm,nextNm);
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
