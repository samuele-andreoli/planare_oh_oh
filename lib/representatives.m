//The classification in n=8 could be incomplete
getRepresentatives:=function(n)
    F<a>:=GF(3^n);
    R<x>:=PolynomialRing(F);

    if n eq 2 then
        return [x^2];
    elif n eq 3 then
        return [x^2, x^4];
    elif n eq 4 then
        return [
            x^2, 
            x^14, 
            x^36 +2*x^10 +2*x^4
        ];
    elif n eq 5 then
        return [
            x^2,
            x^4,
            x^10,
            x^14,
            x^10 + x^6 + 2*x^2,
            x^10 + 2*x^6 + 2*x^2,
            x^90 + x^2,
            x^162 + x^108 +2*x^84 + x^2
        ];
    elif n eq 6 then
        return [
            x^2,
            x^10,
            x^14,
            x^122,
            2*x^270 + 2*x^244 + x^54 + x^36 + x^10 + x^2,
            a^455*x^270 + x^28 + a^273*x^10,
            2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2,
            x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2,
            x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2,
            x^162 + 2*x^108 + 2*x^90 + x^82 + 2*x^10 + x^4 + x^2,
            a^91 * x^30 + x^10 + x^2, 
            a^91 * x^486 + x^10 + x^2,  
            a^182 * x^82 + 2 * x^10 + a^91 * x^6 + x^2, 
            a^182 * x^82 + 2 * x^10 + a^273 * x^6 + x^2,  
            a^91 * x^486 + a^182 * x^90 + 2 * x^10 + x^2,  
            a^273 * x^486 + a^182 * x^90 + 2 * x^10 + x^2, 
            a^273 * x^246 + a^182 * x^82 + a^91 * x^6 + x^2
            ];
    elif n eq 7 then
        return [
            x^2,
            x^4,
            x^10,
            x^28,
            x^14,
            x^122,
            x^10 +x^6+2*x^2,
            x^10 +2*x^6+2*x^2,
        ];
    elif n eq 8 then
        return [
            x^2,
            x^14,
            x^122,
            x^1094,
            x^244 + 2*x^84 + 2*x^82,
            x^324 + x^246 + 2*x^4,
            x^738 + x^82 + 2 * x^18 + x^2,
            x^246+x^82+2 * x^6+x^2,
            a^3608 * x^1458 + a^3608 * x^738 + a^3810 * x^486 + a^3810 * x^246 + a^3413 * x^162 +a^3413 * x^82 + a^3608 * x^18 + a^3810 * x^6 + a^2565 * x^2,
            a^164 * x^1458 + a^164 * x^738 + a^950 * x^486 + a^950 * x^246 + a^616 * x^162 +a^616 * x^82 + a^164 * x^18 + a^950 * x^6 + a^6297 * x^2
        ];
    end if;

    return [];
end function;
