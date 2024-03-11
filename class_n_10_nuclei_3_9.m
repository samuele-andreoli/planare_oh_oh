BH_i := 2; // to 2;

load "lib/FamiliesPlanar.m";
load "lib/dupeq.m";

F<u> := GF(3^10);
R<x> := PolynomialRing(F);

// R is over GF(3^10)
getBH_n_10:=function(R)
    F<u>:=BaseRing(R);
    o:=u^61;
    b:=u^44225;
    x:=R.1;

    n:=Degree(F);
    p:=Characteristic(F);

    if not IsDivisibleBy(n,2) then
    return [];
    end if;

    m:=n div 2;

    BH:=[];

    vDyadic:=function(s)
        v:=0;
        while IsEven(s) do
            s := s div 2;
            v +:=1;
        end while;

        return v;
	end function;

    dm := vDyadic(m);
    
    for s:=1 to (m-1) do
        if not dm eq vDyadic(s) then
            g:=b*x^(p^s+1)+b^(p^m) *x^(p^m *(p^s+1));
            Append(~BH,x^(p^m+1)+o*g);
        end if;
    end for;

  	return BH;
end function;

getZP_cop0_TT:=function(R)
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

    Op1TT := AssociativeArray();
    for a in Fq do
        // Op1:=ns*y;
        Op1TT[a] := ns * a;
    end for;

    for k:=1 to (m div 2) do
        if IsEven(m div GCD(m,k)) then
            continue;
        end if;

        OpTT := AssociativeArray();
        for a in Fq do
            // Op := 2*y^(p^k+1)
            OpTT[a] := 2*a^(p^k+1);
        end for;

        Append(~ZP, getFunFromSpecialSemifieldTT_zero_op2(R,OpTT,Op1TT));
    end for;

    return ZP;
end function;

// BH := getBH_n_10(R);
BH := [
    x^2430 + x^244 + u^44286*x^10,
    x^19926 + x^244 + u^44286*x^82
];

fTT, invfTT := get_tt_with_inv(BH[BH_i]);

/* To compute orbits. Then use precomputed */
// tp := trivialPartition(BH[BH_i]);
// orbits := partitionByL2tt(fTT, invfTT, tp);
// {* #o : o in orbits*};
// orbit_rep := {Min(o) : o in orbits};
// orbit_rep;



// Both have same orbits with the following multiset and representatives.
// {* 968, 4840^^12 *}
orbit_rep := { One(F), u, u^2, u^3, u^4, u^5, u^6, u^8, u^10, u^11, u^12, u^13, u^17 };

/* Compute equivalence with ZP 
 * Result: all inequivalent
 */
// SetLogFile("logs/bh_%o_zp.txt": Overwrite := true);

// for zTT in getZP_cop0_TT(R) do
//     invzTT := AssociativeArray();
//     for k->v in zTT do
//         // Really hope magma short circuits.
//         if not (IsDefined(invzTT, v) and (k ge invzTT[v])) then
//             invzTT[v] := k;
//         end if;
//     end for;

//     s, l1, l2 := dupeq_with_l2_representatives_tt(fTT, invfTT, zTT, invzTT, orbit_rep);
//     s;
//     if s then
//         Interpolation([u : u in F], [l1[u] : u in F]);
//         Interpolation([u : u in F], [l2[u] : u in F]);
//     end if;
// end for;

// UnsetLogFile();

/* Compute equivalence among themselves */
SetLogFile("logs/bh.txt": Overwrite := true);

fTT2, invfTT2 := get_tt_with_inv(BH[3-BH_i]);

s, l1, l2 := dupeq_with_l2_representatives_tt(fTT, invfTT, fTT2, invfTT2, orbit_rep);
s;
if s then
    Interpolation([u : u in F], [l1[u] : u in F]);
    Interpolation([u : u in F], [l2[u] : u in F]);
end if;

UnsetLogFile();