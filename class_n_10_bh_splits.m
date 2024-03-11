load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

p := 3;
n := 10;

F<u> := GF(p^n);
R<x> := PolynomialRing(F);

// Re-generalize to find better representative
testBHequivalence := procedure(fTT, invfTT, orbits)
    m:=n div 2;

    vDyadic:=function(s)
        v:=0;
        while IsEven(s div 2^v) do
        v +:=1;
        end while;
        return v;
    end function;    

    subfields := {sub<F|d> : d in Divisors(n)};

    for b in F:
        if IsZero(b) or IsSquare(a) then
            continue;
        end if;

        bpm :=b^(p^m);

        for o in F do
            if o in GF(p^m) then
                continue;
            end if;

            for s:=1 to (m-1) do
                if not vDyadic(m) eq vDyadic(s) then
                    g:=b*x^(p^s+1)+ bpm * x^(p^m *(p^s+1));
                    cand := x^(p^m+1) + o*g;
                
                    coeff := {c : c in Coefficients(f)};
                    for s in subfields do
                        if coeff subset s then
                            d := Degree(s);
                            m := n div d;

                            break;
                        end if;
                    end for;

                    // We don't want worse representatives, just let it go
                    if m gt 2 then
                        continue;
                    end if;

                    candTT, invcandTT := get_tt_with_inv(cand);
                    
                    s, l1, l2 := dupeq_with_l2_representatives_tt(fTT, invfTT, candTT, invcandTT, orbits);
                    if s then
                        printf "Found candindate %o\n", cand;
                    end if;
                end if;
            end for;
        end for;
    end for;

    return BH;
end function;

BH := [
    x^2430 + x^244 + u^44286*x^10,
    x^19926 + x^244 + u^44286*x^82
];

bh1TT, invbh1TT := get_tt_with_inv(BH[1]);
bh2TT, invbh2TT := get_tt_with_inv(BH[2]);

orbit_rep := {u^17, One(F), u, u^2, u^3, u^4, u^5, u^6, u^8, u^10, u^11, u^12, u^13};

/* Check if BH1/2 splits (into BH2/1) */
SetLogFile("logs/bh_split.txt": Overwrite := true);

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

    idS := star(e,e);

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
    Nm:={Zero(F), idS, -idS};
    N:={Zero(F), idS, -idS};

    mn:=0;
    rn:=0;
    for u in F do
        if IsZero(Evaluate(g,[a,u,b])) then
            Include(~Nm, u);
            u_new := u;
            for i in [2..8] do
                u_new := asterisk(u_new, u);
                Include(~Nm,u);
            end for;
        end if;

        if #N eq 3 and #Nm eq 3^2 then
            break;
        end if;
    end for;

    return [N,Nm];
end function;

split_BH := procedure(f, BH1TT, BH1TTinv, BH2TT, BH2TTinv)
    star:=function(u,v)
        return BH1TT[u+v] - BH1TT[u] - BH1TT[v];
    end function;

    e := One(F);
    idS := star(e,e);

    starPsi := AssociativeArray();
    for u in F do
        starPsi[star(u,e)] := u;
    end for;

    asterisk := function(u,v)
        return star(starPsi[u],starPsi[v]);
    end function;

    nuclei := getNuclei(f,e);
    N := nuclei[1];
    Nm := nuclei[2];

    CandidatesB:={Rep({asterisk(u,b): u in N| not IsZero(u)}): b in Nm | not b in N};

    for b in CandidatesB do
        f1TT:= AssociativeArray();
        invf1TT := AssociativeArray();
        for x in F do
            if IsDefined(f1TT, x) then
                continue;
            end if;

            f1TT[x] := asterisk(asterisk(b,x),x);
            f1TT[-x] := f1TT[x];
            invf1TT[f1TT[x]] := Min({x,-x});
        end for;

        s, l1, l2 := dupeq_with_l2_representatives_tt(BH1TT, BH1TTinv, f1TT, invf1TT, orbit_rep);
        if s then
            continue;
        end if;

        print "Splits!";

        s, l1, l2 := dupeq_with_l2_representatives_tt(BH2TT, BH2TTinv, f1TT, invf1TT, orbit_rep);
        if s then
            print "Splits into BH2";
            b;
            e;
            Interpolation([u : u in F], [l1[u] : u in F]);
            Interpolation([u : u in F], [l2[u] : u in F]);
        else
            b;
            e;
            print "Splits into new function";
        end if;

        break;
    end for;
end procedure;

SetMemoryLimit(10^10);

print "Split bh1";
// split_BH(BH[1], bh1TT, invbh1TT, bh2TT, invbh2TT);
star:=function(u,v)
    return bh1TT[u+v] - bh1TT[u] - bh1TT[v];
end function;

e := One(F);

starPsi := AssociativeArray();
for u in F do
    starPsi[star(u,e)] := u;
end for;

asterisk := function(u,v)
    return star(starPsi[u],starPsi[v]);
end function;

f1TT:= AssociativeArray();
invf1TT := AssociativeArray();
for x in F do
    if IsDefined(f1TT, x) then
        continue;
    end if;

    f1TT[x] := asterisk(asterisk(One(F),x),x);
    f1TT[-x] := f1TT[x];
    invf1TT[f1TT[x]] := Min({x,-x});
end for;

orbits := {}; // TODO orbits

testBHequivalence(f1TT, invf1TT, orbits);

print "Split bh2";

star:=function(u,v)
    return bh2TT[u+v] - bh2TT[u] - bh2TT[v];
end function;

e := One(F);

starPsi := AssociativeArray();
for u in F do
    starPsi[star(u,e)] := u;
end for;

asterisk := function(u,v)
    return star(starPsi[u],starPsi[v]);
end function;

f1TT:= AssociativeArray();
invf1TT := AssociativeArray();
for x in F do
    if IsDefined(f1TT, x) then
        continue;
    end if;

    f1TT[x] := asterisk(asterisk(One(F),x),x);
    f1TT[-x] := f1TT[x];
    invf1TT[f1TT[x]] := Min({x,-x});
end for;

orbits := {}; // TODO orbits

testBHequivalence(f1TT, invf1TT, orbits);

UnsetLogFile();
