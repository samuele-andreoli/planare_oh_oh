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

/* Vandermonde interpolation for linear functions. */
VandermondeInterpolation := function(R, X, Y)
    // Use X[1] instead of R since we want to support polynomial rings
    // different from PolynomialRing(F).
    F<a> := Parent(X[1]);
    n := Degree(F);
    p := Characteristic(F); 

    assert #Y eq n;

    V := Matrix(F, #X, #X, [[xi^(p^j) : j in [0..(n-1)]] : xi in X]);
    V := Transpose(V);
    Y := Vector(F, Y);
    C := Solution(V,Y);

    return &+[C[i+1] * R.1^(p^i) : i in [0..(n-1)]];
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

    B := [F.1^(p^i) : i in [0..(n-1)]]; 
    fe := Evaluate(f, e);
    starPsi := VandermondeInterpolation(R, [Evaluate(f,b+e) - Evaluate(f,b) - fe : b in B], B);
    id := Evaluate(f, 2*e) - 2 * Evaluate(f, e);

    f := R0!f;
    FE := [a^(#F)-a,b^(#F)-b,c^(#F)-c];

    // Fast evaluation of a polynomial and reduction by the field equations.
    EvaluateMod := function(f0,u)
        return &+[NormalForm(Evaluate(t,u), FE) : t in Terms(f0)];
    end function;

    // Fast evaluation of a linear polynomial and reduction by the field equations.
    EvaluateLinMod := function(l, u)
        return &+[&+[NormalForm(Evaluate(tl, tu), FE) : tl in Terms(l)] : tu in Terms(u)];
    end function;

    // Construct polynomials for the star and * products
    star:=function(u,v)
        return EvaluateMod(f,u+v) - EvaluateMod(f,u) - EvaluateMod(f,v);
    end function;

    asterisk := function(u,v)
        return star(EvaluateLinMod(starPsi,u), EvaluateLinMod(starPsi,v));
    end function;

    // Associativity equation
    astrP := asterisk(a,b);
    fl := asterisk(astrP,c);
    fr := Evaluate(fl,[b,c,a]);
    g  := fl-fr;

    Span := function(M, dM, u)
        S := M;
        ui := u;
        dS := dM;

        while not ui in S do
            dS +:= dM;

            for a in M do
                if IsZero(a) then
                    continue;
                end if;

                ua := Evaluate(astrP, [a, ui, id]);
                S join:= {ua + b : b in S};
            end for;

            ui := Evaluate(astrP, [ui, u, id]);
        end while;

        return S, dS;
    end function;

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

        if not IsZero(Evaluate(g, [a,u,b])) then
            // If u is not in Nm, then it is also not in N. Remove all x1 + u * x2, x1,x2 in Nm
            F_elements diff:= {x1 + Evaluate(astrP, [x2, u, id]) : x1,x2 in Nm};

            continue;
        end if;

        // u belongs to Nm, so span it
        newNm, dNm := Span(Nm, dNm,u);
        if dNm eq n then
            return [newNm,newNm];
        end if;

        elements_for_next_middle_nucleus := NextDim(dNm);
        F_elements diff:= newNm;

        /* Test if the new elements spanned in Nm belong to N, too. */
        to_test_for_nucleus := newNm diff Nm;
        Nm := newNm;

        while #to_test_for_nucleus gt elements_for_next_nucleus do
            ExtractRep(~to_test_for_nucleus, ~t);

            if IsZero(Evaluate(g,[a,b,t])) then
                // t belongs to N, so span it
                N, dN := Span(N,dN,t);
                elements_for_next_nucleus := NextDim(dN);
                to_test_for_nucleus diff:= N;
            else
                // t not in N. Remove all x1 + u * x2, s.t. x1, x2 in N
                to_test_for_nucleus diff:= {x1 + Evaluate(astrP, [x2, t, id]) : x1,x2 in N};
            end if;
        end while;
    end while;

    return [N,Nm];
end function;


Nuclei:=function(f, e)
    NN:=getNuclei(f,e);
    return [#NN[1],#NN[2]];
end function;
