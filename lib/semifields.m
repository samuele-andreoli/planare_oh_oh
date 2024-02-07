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

    // Construct polynomials for the * and star products
    asterisk:=function(u,v)
        return star(EvaluateMod(starPsi,u),EvaluateMod(starPsi,v));
    end function;

    return asterisk(a,b);
end function;

/*
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
*/

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
    rn:=0;
    bolRn:=true;
    //Max order of a Nuclei
    n:=Degree(F);
    p:=Characteristic(F);
    D:=Divisors(n);
    MaxOrder:=p^D[#D-1]+1;
    mn:=0;
    rn:=0;
    for u in F do
        if mn eq MaxOrder then
            return [#F,#F];
        elif IsZero(Evaluate(g,[a,b,u])) then
            rn +:=1;
            mn +:=1;
        elif IsZero(Evaluate(g,[a,u,b])) then
            mn +:=1;
        end if;
    end for;
    /*
    // Compute the commutative cosets for the nuclei search
    identity := star(e,e);
    cosets :=  [{identity * si : si in s} : s in subfields];

    // Check smaller and smaller cosets to find the middle nucleus
    for cos in cosets do
        if IsZero(Evaluate(g,[a,Rep(cos),c])) then
            remaining_cosets := cosets[Index(cosets, cos)..#cosets];
            mn := sizes[Index(cosets, cos)];
            break;
        end if;
    end for;

    // Check cosets subsets of the middle nucleus to find the left/right nucleus
    // since N = Nl = Nr is subset of Nm for commutative semifields.
    for cos in remaining_cosets do
        if IsZero(Evaluate(g,[a,b,Rep(cos)])) then
            remaining_cosets := cosets[Index(cosets, cos)..#cosets];
            rn := sizes[Index(cosets, cos)];
            break;
        end if;
    end for;
    */
    return [rn,mn];
end function;
