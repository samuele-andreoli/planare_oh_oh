load "lib/representatives.m";
load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/planar.m";
load "lib/dupeq_orbits.m";


computeInvariantTable := procedure(n)
    FuctionList:=getRepresentatives(n);
    R<x>:=Parent(FuctionList[1]);
    F<a>:=BaseRing(R);

    invariantTable := AssociativeArray();

    for f in FuctionList do
        N:=[0,0];
        if isDOPolynomial(f) then
            N:=Nuclei(f, One(F));
        end if;

        order := "NA";
        if ((n eq 6) and not N in {[3^6,3^6],[3^(2),3^(2)]}) then
            order := AutomoriphismGroupOrderFromFunction(f);
        end if;

        key := Sprintf("%o.%o", N, order);

        if not key in Keys(invariantTable) then
            invariantTable[key] := {f};
        else
            Include(~invariantTable[key],f);
        end if;
    end for;

    for key in Keys(invariantTable) do
        printf "invariantTable[\"%o\"]:=%o;\n\n",key,invariantTable[key];
    end for;
end procedure;

getInvariantTable:=function(n)
    F<a>:=GF(3^n);
    R<x>:=PolynomialRing(F);

    invariantTable := AssociativeArray();

    if n eq 6 then
        invariantTable["[ 3, 3 ].113724"]:={
            x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2
        };
        
        invariantTable["[ 3, 27 ].227448"]:={
            x^162 + x^84 + a^58*x^54 + a^58*x^28 + x^6 + a^531*x^2
        };
        
        invariantTable["[ 729, 729 ].NA"]:={
            x^2
        };
        
        invariantTable["[ 3, 9 ].454896"]:={
            a^455*x^270 + x^28 + a^273*x^10,
            2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2
        };
        
        invariantTable["[ 3, 3 ].227448"]:={
            x^162 + 2*x^108 + 2*x^90 + x^82 + 2*x^10 + x^4 + x^2
        };
        
        invariantTable["[ 3, 9 ].17496"]:={
            a^91*x^486 + x^10 + x^2,
            a^91*x^30 + x^10 + x^2,
            a^273*x^486 + a^182*x^90 + 2*x^10 + x^2,
            a^273*x^246 + a^182*x^82 + a^91*x^6 + x^2,
            a^91*x^486 + a^182*x^90 + 2*x^10 + x^2,
            a^182*x^82 + 2*x^10 + a^273*x^6 + x^2,
            a^182*x^82 + 2*x^10 + a^91*x^6 + x^2
        };
        
        invariantTable["[ 3, 27 ].34992"]:={
            x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2
        };
        
        invariantTable["[ 0, 0 ].8736"]:={
            x^122
        };
        
        invariantTable["[ 9, 9 ].NA"]:={
            x^10
        };
    elif n eq 8 then
        invariantTable["[ 6561, 6561 ].NA"]:={
            x^2
        };
        
        invariantTable["[ 3, 9 ].NA"]:={
            a^714*x^244 + a^2074*x^84 + x^82,
            a^418*x^2188 + a^4338*x^108 + x^82
        };
        
        invariantTable["[ 3, 81 ].NA"]:={
            a^3608*x^1458 + a^3608*x^738 + a^3810*x^486 + a^3810*x^246 + a^3413*x^162 + a^3413*x^82 + a^3608*x^18 + a^3810*x^6 + a^2565*x^2,
            x^246 + x^82 + 2*x^6 + x^2,
            a^164*x^1458 + a^164*x^738 + a^950*x^486 + a^950*x^246 + a^616*x^162 + a^616*x^82 + a^164*x^18 + a^950*x^6 + a^6297*x^2
        };
        
        invariantTable["[ 9, 81 ].NA"]:={
            x^738 + x^82 + 2 * x^18 + x^2
        };

        invariantTable["[ 0, 0 ].NA"]:={
            x^1094,
            x^14,
            x^122
        };
    end if;

    return invariantTable;
end function;

computeOrbitsTable := procedure()
    printf "getOrbitsTable := function(n)";
    printf "\tF<a> := GF(3^n);\n\tR<x> := PolynomialRing(F);\n";
    printf "\torbitsTable := AssociativeArray();\n\n";

    for n := 3 to 8 do
        printf "\tif n eq %o then\n", n;
        
        FunctionList:=getRepresentatives(n);
        R<x>:=Parent(FunctionList[1]);
        F<a>:=BaseRing(R);

        for f in FunctionList do
            orbits := partitionByL2(f);
            printf "\t\torbitsTable[%o] := %o;\n", f, {Min(o) : o in orbits};
        end for;

        printf "\tend if;\n";
    end for;
    printf "\n\treturn orbitsTable;\n";
    printf "end function;\n";
end procedure;

getOrbitsTable := function(n)
    F<a> := GF(3^n);
    R<x> := PolynomialRing(F);

    orbitsTable := AssociativeArray();

    if n eq 3 then        
        orbitsTable[x^2] := {One(F)};
        orbitsTable[x^4] := {One(F)};
    elif n eq 4 then        
        orbitsTable[x^2] := {One(F)};
        orbitsTable[x^14] := {One(F)};
        orbitsTable[x^36 + 2*x^10 + 2 * x^4] := {One(F), a};
    elif n eq 5 then        
        orbitsTable[x^2] := {One(F)};
        orbitsTable[x^4] := {One(F)};
        orbitsTable[x^10] := {One(F)};
        orbitsTable[x^10 + x^6 + 2 * x^2] := {One(F), a, a^2, a^4, a^5, a^7, a^8, a^10, a^11, a^13, a^16, a^17, a^19, a^20, a^22, a^25, a^26, a^31, a^34, a^35, a^38, a^40, a^61, a^67, a^76};
        orbitsTable[x^10 + 2 * x^6 + 2 * x^2] := {One(F), a, a^2, a^4, a^5, a^7, a^8, a^10, a^11, a^13, a^16, a^17, a^19, a^20, a^22, a^25, a^26, a^31, a^34, a^35, a^38, a^40, a^61, a^67, a^76};
        orbitsTable[x^14] := {One(F)};
        orbitsTable[x^90 + x^2] := {One(F), a, a^2};
        orbitsTable[x^162 + x^108 + 2 * x^84 + x^2] := {One(F), a, a^2, a^4, a^5, a^7, a^8, a^10, a^11, a^13, a^16, a^17, a^19, a^20, a^22, a^25, a^26, a^31, a^34, a^35, a^38, a^40, a^61, a^67, a^76};
    elif n eq 6 then
        orbitsTable[x^2] := {One(F)};
        orbitsTable[x^10] := {One(F)};
        orbitsTable[x^122] := {One(F)};
        orbitsTable[2*x^270 + 2*x^244 + x^54 + x^36 + x^10 + x^2] := {One(F), a, a^2, a^3, a^6, a^7, a^44};
        orbitsTable[a^455*x^270 + x^28 + a^273*x^10] := {One(F), a, a^2};
        orbitsTable[2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2] := {One(F), a, a^2, a^7};
        orbitsTable[x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2] := {One(F), a, a^2, a^3, a^4, a^5, a^6, a^8, a^10, a^15, a^17, a^20};
        orbitsTable[x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2] := {0, a^1, a^2, a^3, a^4, a^5, a^6, a^7, a^8, a^9, a^10, a^12, a^13, a^16, a^17, a^19, a^22, a^23, a^31, a^34, a^35, a^36, a^38, a^39, a^44, a^45, a^47, a^48, a^50, a^54, a^66, a^72, a^90};
        orbitsTable[x^162 + 2*x^108 + 2*x^90 + x^82 + 2*x^10 + x^4 + x^2] := {One(F), a, a^2, a^6, a^8, a^13, a^15};
        
        novelOrbit := {One(F), a, a^2, a^3, a^4, a^5, a^6, a^7, a^8, a^10, a^11, a^12, a^13, a^14, a^15, a^16, a^17, a^19, a^20, a^23, a^24, a^26, a^28, a^29, a^30, a^31, a^32, a^33, a^35, a^37, a^38, a^39, a^40, a^46, a^47, a^48, a^49, a^51, a^53, a^55, a^56, a^57, a^58, a^60, a^69, a^71, a^73, a^74, a^76, a^78, a^80, a^91, a^92, a^94, a^96, a^98, a^101, a^114, a^119, a^121, a^137, a^139};
        orbitsTable[a^91 * x^30 + x^10 + x^2] := novelOrbit;
        orbitsTable[a^91 * x^486 + x^10 + x^2] := novelOrbit;
        orbitsTable[a^182 * x^82 + 2 * x^10 + a^91 * x^6 + x^2] := novelOrbit;
        orbitsTable[a^182 * x^82 + 2 * x^10 + a^273 * x^6 + x^2] := novelOrbit;
        orbitsTable[a^91 * x^486 + a^182 * x^90 + 2 * x^10 + x^2] := novelOrbit;
        orbitsTable[a^273 * x^486 + a^182 * x^90 + 2 * x^10 + x^2] := novelOrbit;
        orbitsTable[a^273 * x^246 + a^182 * x^82 + a^91 * x^6 + x^2] := novelOrbit;
    elif n eq 7 then
        orbitsTable[x^2] := {One(F)};
        orbitsTable[x^4] := {One(F)};
        orbitsTable[x^10] := {One(F)};
        orbitsTable[x^28] := {One(F)};
        orbitsTable[x^14] := {One(F)};
        orbitsTable[x^122] := {One(F)};

        polyOrbit := {One(F), a, a^2, a^4, a^5, a^7, a^8, a^10, a^11, a^13, a^14, a^16, a^17, a^19, a^20, a^22, a^23, a^25, a^26, a^28, a^29, a^31, a^32, a^34, a^35, a^37, a^38, a^40, a^43, a^44, a^46, a^47, a^49, a^50, a^52, a^53, a^55, a^56, a^58, a^59, a^61, a^62, a^64, a^65, a^67, a^70, a^71, a^73, a^74, a^76, a^77, a^79, a^80, a^85, a^86, a^88, a^89, a^91, a^92, a^94, a^97, a^98, a^100, a^101, a^103, a^104, a^106, a^107, a^110, a^112, a^113, a^115, a^116, a^118, a^119, a^121, a^137, a^139, a^142, a^143, a^145, a^146, a^148, a^151, a^152, a^154, a^155, a^157, a^160, a^161, a^169, a^170, a^172, a^173, a^175,  a^178, a^179, a^181, a^182, a^184, a^187, a^188, a^193, a^196, a^197, a^199, a^200, a^202, a^211, a^214, a^215, a^220, a^223, a^224, a^226, a^227,  a^229, a^233, a^235, a^236, a^238, a^241, a^242, a^274, a^277, a^278, a^281, a^283, a^295, a^296, a^301, a^304, a^305, a^308, a^310, a^317, a^319,  a^322, a^323, a^337, a^344, a^346, a^349, a^350, a^358, a^359, a^362, a^364, a^547, a^553, a^562, a^565, a^589, a^592, a^607, a^688, a^715};
        orbitsTable[x^10 +x^6+2*x^2] := polyOrbit;
        orbitsTable[x^10 +2*x^6+2*x^2] := polyOrbit;
    elif n eq 8 then
        orbitsTable[x^2]:={One(F)};
        orbitsTable[x^14]:={One(F)};
        orbitsTable[x^122]:={One(F)};
        orbitsTable[x^1094]:={One(F)};
        orbitsTable[a^714 * x^244 + a^2074 * x^84 + x^82]:={a^i: i in [0, 1, 2, 4, 5, 29]};
        orbitsTable[x^738 + x^82 + 2 * x^18 + x^2]:={a^i: i in [0, 1, 2, 4, 5, 7]};
        orbitsTable[a^418 * x^2188 + a^4338 * x^108 + x^82]:={a^i: i in [0, 1, 2, 3, 6, 35]};
        orbitsTable[x^246 + x^82 + 2*x^6 + x^2] := { One(F), a, a^2, a^4, a^10, a^11, a^13, a^16, a^17, a^28, a^35, a^41 };
        // 8.9 orbits give false negatives
        // orbitsTable[a^3608 * x^1458 + a^3608 * x^738 + a^3810 * x^486 + a^3810 * x^246 + a^3413 * x^162 +a^3413 * x^82 + a^3608 * x^18 + a^3810 * x^6 + a^2565 * x^2]:={a^i: i in [0, 1, 2, 4, 7, 10, 13, 14, 17, 20, 41, 43]};
        // 8.10 orbit not computed yet.
        // orbitsTable[a^164 * x^1458 + a^164 * x^738 + a^950 * x^486 + a^950 * x^246 + a^616 * x^162 +a^616 * x^82 + a^164 * x^18 + a^950 * x^6 + a^6297 * x^2]:={};//?
    end if;

    return orbitsTable;
end function;
