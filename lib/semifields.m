/* Vandermonde interpolation for linear functions. */
VandermondeInterpolation := function(R, X, Y)
    // Use X[1] instead of R since we want to support polynomial rings
    // different from PolynomialRing(F).
    F<a> := Parent(X[1]);
    n := Degree(F);
    p := Characteristic(F); 

    assert #Y eq n;
    assert #X eq n;

    V := Matrix(F, #X, #X, [[xi^(p^j) : j in [0..(n-1)]] : xi in X]);
    V := Transpose(V);
    Y := Vector(F, Y);
    C := Solution(V,Y);

    return &+[C[i+1] * R.1^(p^i) : i in [0..(n-1)]];
end function;

DOToSemifieldPoly:=function(f, e)
    assert not IsZero(e);

    R := Parent(f);
    F := BaseRing(R);
    p := Characteristic(F);
    n := Degree(F);
    D := Divisors(n);

    RR<a,b> := PolynomialRing(F,2);
    R0 := PolynomialRing(RR);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b];

    // Fast evaluation of a linear polynomial and reduction by the field equations.
    EvaluateLinMod := function(l, u)
        return &+[&+[NormalForm(Evaluate(tl, tu), FE) : tl in Terms(l)] : tu in Terms(u)];
    end function;

    // Fast evaluation of a multivariate linear polynomial and reduction by the field equations.
    MultiEvaluateLinMod := function(l, ul)
        return &+[&+[NormalForm(Evaluate(tl, ull), FE) : tl in Terms(l)] : ull in car<Terms(ul[1]),Terms(ul[2])>];
    end function;

    // Construct polynomials for the star and * products
    star := Evaluate(f,a+b) - Evaluate(f,a) - Evaluate(f,b);

    B := Basis(F);
    starE := Evaluate(star, b, e);
    starPsi := VandermondeInterpolation(R, [F!Evaluate(starE, a, bi) : bi in B], B);
    id := F!Evaluate(starE, a, e);

    asterisk := MultiEvaluateLinMod(star, [Evaluate(starPsi,a), Evaluate(starPsi,b)]);

    return asterisk, id;
end function;

SpanAsterisk := function(asterisk, M, dM, u)
    S := M;
    ui := u;
    dS := dM;

    R := Parent(asterisk);
    F := BaseRing(R);

    astrU := Evaluate(asterisk, R.2, u);

    while not ui in S do
        astrUI := Evaluate(asterisk, R.2, ui);

        dS +:= dM;

        for a in M do
            if IsZero(a) then
                continue;
            end if;

            ua := Evaluate(astrUI, R.1, a);
            S join:= {ua + b : b in S};
        end for;

        ui := F!Evaluate(astrU, R.1, ui);
    end while;

    return S, dS;
end function;

getNuclei:=function(f, e)
    assert not IsZero(e);

    R := Parent(f);
    F := BaseRing(R);
    p := Characteristic(F);
    n := Degree(F);
    D := Divisors(n);

    RR<a,b,c> := PolynomialRing(F,3);
    R0 := PolynomialRing(RR);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b,c^(#F)-c];

    // Fast evaluation of a linear polynomial and reduction by the field equations.
    EvaluateLinMod := function(l, u)
        return &+[&+[NormalForm(Evaluate(tl, tu), FE) : tl in Terms(l)] : tu in Terms(u)];
    end function;

    // Fast evaluation of a multivariate linear polynomial and reduction by the field equations.
    MultiEvaluateLinMod := function(l, ul)
        return &+[&+[NormalForm(Evaluate(tl, ull), FE) : tl in Terms(l)] : ull in car<Terms(ul[1]),Terms(ul[2]),Terms(ul[3])>];
    end function;

    // Construct polynomials for the star and * products
    star := Evaluate(f,a+b) - Evaluate(f,a) - Evaluate(f,b);

    B := Basis(F);
    starE := Evaluate(star, b, e);
    starPsi := VandermondeInterpolation(R, [F!Evaluate(starE, a, bi) : bi in B], B);
    id := F!Evaluate(starE, a, e);

    asterisk := function(u,v)
        return MultiEvaluateLinMod(star, [EvaluateLinMod(starPsi,u), Evaluate(starPsi,v), id]);
    end function;

    // Associativity equation
    astrP := asterisk(a,b);
    fl := asterisk(astrP,c);
    fr := Evaluate(fl,[b,c,a]);
    g  := fl-fr;

    NextDim := function(d)
        D := Divisors(n div d);
        return p^(d * (Divisors(n div d)[2])) - p^d;
    end function;

    Nm:={id*a: a in PrimeField(F)};
    N:=Nm;

    dN  := 1;
    dNm := 1;

    F_elements := {x : x in F | not x in Nm};
    elements_for_next_middle_nucleus := NextDim(dN);
    elements_for_next_nucleus := NextDim(dNm);

    while #F_elements ge elements_for_next_middle_nucleus do
        /* Choose an element and test Nm membership */
        ExtractRep(~F_elements, ~u);

        if not IsZero(Evaluate(g, b, u)) then
            // If u is not in Nm, then it is also not in N. Remove all x1 + u * x2, x1,x2 in Nm
            astrU := Evaluate(astrP, b, u);
            X2 := {Evaluate(astrU, a, x) : x in Nm};
            F_elements diff:= {x1 + x2 : x1 in Nm, x2 in X2};

            continue;
        end if;

        // u belongs to Nm, so span it
        newNm, dNm := SpanAsterisk(astrP, Nm, dNm, u);
        if dNm eq n then
            return [newNm,newNm];
        end if;

        elements_for_next_middle_nucleus := NextDim(dNm);
        F_elements diff:= newNm;

        /* Test if the new elements spanned in Nm belong to N, too. */
        to_test_for_nucleus := newNm diff Nm;
        Nm := newNm;

        while #to_test_for_nucleus ge elements_for_next_nucleus do
            ExtractRep(~to_test_for_nucleus, ~t);

            if IsZero(Evaluate(g, c, t)) then
                // t belongs to N, so span it
                N, dN := SpanAsterisk(astrP, N, dN, t);
                elements_for_next_nucleus := NextDim(dN);
                to_test_for_nucleus diff:= N;
            else
                // t not in N. Remove all x1 + u * x2, s.t. x1, x2 in N
                astrT := Evaluate(astrP, b, t);
                X2 := {Evaluate(astrT, a, x) : x in N};
                to_test_for_nucleus diff:= {x1 + x2 : x1 in N, x2 in X2};
            end if;
        end while;
    end while;

    return [N,Nm];
end function;


Nuclei:=function(f, e)
    NN:=getNuclei(f,e);
    return [#NN[1],#NN[2]];
end function;
