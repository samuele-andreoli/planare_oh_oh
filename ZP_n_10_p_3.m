p:=3;
n:=10;
m:=n div 2;
q:=p^m;
F<u>:=GF(q^2);
F0:={a: a in F|not a in GF(q)};
R<x>:=PolynomialRing(F);
iPow:=AssociativeArray();
kPow:=AssociativeArray();
lambdaA:=AssociativeArray();
for i:=0 to Floor(n/4) do
    for a in F do
        b:=a^(p^i);
        iPow[<a,i>]:=b;
        kPow[<a,i>]:=2*a*b;
    end for;
    lambdaA[i]:={lambda: lambda in F0| lambda^(p^i+1) in GF(q) and not IsSquare(GF(q)!(lambda^(p^i+1)))};
end for;
for k:=1 to Floor(n/4) do 
    if IsOdd(m div GCD(m,k)) then
        for i:=0 to Floor(n/4) do
            "\n\n";
            for lambda in lambdaA[k] do
                f:=Interpolation([a+lambda*b: a,b in GF(q)],[(kPow[<a,k>]+ iPow[<kPow[<lambda*b,k>],i>])+lambda*(2*a*b): a,b in GF(q)]);
                f;
                <i,k,[Coefficients(f) in PowerSequence(GF(3^l)): l in [1,2,5]]>;
                "\n";
                if Coefficients(f) in PowerSequence(GF(3)) then break; end if;
            end for;
        end for;
    end if;
end for;
    

//(i,k)=(0,2)
//x^2430 + x^486 + x^10 + 2*x^2

//(i,k)=(1,2)
//2*x^7290 + x^6564 + 2*x^2430 + 2*x^2188 + x^756 + x^486 + 2*x^252 + 2*x^30 + 2*x^10 + 2*x^2


//(i,k)=(2,2)
//2*x^21870 + x^19692 + 2*x^2430 + x^2268 + 2*x^2188 + x^486 + 2*x^252 + 2*x^90 + 2*x^10 + 2*x^2
