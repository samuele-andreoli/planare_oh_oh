/* Method 2 - Using multiplication maps
    This method is only viable for generic planar functions.
    If you plan on having sparse polynomial use the alternative method using the polynomial representation
*/

function MultiplicationMaps(f)
    invStarPsiTT := AssociativeArray();
    finvStarPsiTT := AssociativeArray();

    R := Parent(f);
    F := BaseRing(R);
    B := Basis(F);

    e := B[1];
    fe := Evaluate(f, e);

    // Compute b_i star e
    starPsi := Matrix([Eltseq(Evaluate(f, x + e) - Evaluate(f, x) - fe) : x in B]);
    invStarPsi := starPsi^(-1);

    for i in [1..#B] do
        x := Seqelt(Eltseq(invStarPsi[i]), F);
        invStarPsiTT[B[i]]  := x;
        finvStarPsiTT[B[i]] := Evaluate(f, x);
    end for;

    id := starPsi[1];

    // Multiplication maps for B
    MM := [Matrix([Eltseq(Evaluate(f, invStarPsiTT[x] + invStarPsiTT[y]) - finvStarPsiTT[x] - finvStarPsiTT[y]) : x in B]) : y in B];

    return MM, id;
end function;

SpanMultiplicationMap := function(Ma, M, dM)
    S := M;
    dS := dM;
    Mu := Ma;

    while not Mu in S do
        dS +:= dM;

        for Mm in M do
            Mum := Mu * Mm;

            S join:= {Mum + b : b in S};
        end for;

        Mu := Ma * Mu;
    end while;

    return S, dS;
end function;

getNuclei:=function(f)
    R := Parent(f);
    F := BaseRing(R);
    p := Characteristic(F);
    n := Degree(F);

    MM, id := MultiplicationMaps(f);

    NextDim := function(d)
        return p^(d * (Divisors(n div d)[2])) - p^d;
    end function;

    Nm  := {ScalarMatrix(PrimeField(F), n, a) : a in PrimeField(F)};
    N:=Nm;

    dN  := 1;
    dNm := 1;

    F_elements := {Eltseq(x) : x in F | not x in PrimeField(F)};
    F_elements := {&+[x[i] * MM[i] : i in [1..n]] : x in F_elements};

    elements_for_next_middle_nucleus := NextDim(dN);
    elements_for_next_nucleus := NextDim(dNm);

    while #F_elements ge elements_for_next_middle_nucleus do
        /* Choose an element and test Nm membership */
        ExtractRep(~F_elements, ~Mu);

        // Test for middle nucleus membership
        membership := true;
        for Mbi in MM do
            MuMbi := Mu * Mbi;
            ubi := id * MuMbi;
            Mubi := &+[MM[i] * ubi[i] : i in [1..n]];

            if not IsZero(MuMbi - Mubi) then
                membership := false;
                break;
            end if;
        end for;

        if not membership then
            // Remove all x1 + u * x2, x1, x2 in Nm
            X2 := {Mu * x : x in Nm};
            F_elements diff:= {x1 + x2 : x1 in Nm, x2 in X2};

            // If u is not in Nm, then it is also not in N.
            continue;
        end if;

        // u belongs to Nm, so span it
        newNm, dNm := SpanMultiplicationMap(Mu, Nm, dNm);
        if dNm eq n then
            return [newNm,newNm];
        end if;

        elements_for_next_middle_nucleus := NextDim(dNm);
        F_elements diff:= newNm;

        /* Test if the new elements spanned in Nm belong to N, too. */
        to_test_for_nucleus := newNm diff Nm;
        Nm := newNm;

        while #to_test_for_nucleus ge elements_for_next_nucleus do
            ExtractRep(~to_test_for_nucleus, ~Mt);

            // Test for nucleus membership
            membership := true;
            for Mbi in MM do
                MbiMt := Mbi * Mt;
                bit := id * MbiMt;
                Mbit := &+[bit[i] * MM[i] : i in [1..n]];

                if not IsZero(MbiMt - Mbit) then
                    membership := false;
                    break;
                end if;
            end for;

            if membership then
                // t belongs to N, so span it
                N, dN := SpanMultiplicationMap(Mt, N, dN);
                elements_for_next_nucleus := NextDim(dN);
                to_test_for_nucleus diff:= N;
            else
                // t not in N. Remove all x1 + t * x2, s.t. x1, x2 in N
                X2 := {Mt * x : x in N};
                to_test_for_nucleus diff:= {x1 + x2 : x1 in N, x2 in X2};
            end if;
        end while;
    end while;

    return [N,Nm];
end function;


Nuclei:=function(f)
    NN:=getNuclei(f);
    return [#NN[1],#NN[2]];
end function;
