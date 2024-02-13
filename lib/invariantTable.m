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
            a^569*x^82 + a^439*x^30 + x^28,
            2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2
        };
        
        invariantTable["[ 3, 3 ].227448"]:={
        a^438*x^486 + a^180*x^324 + a^458*x^270 + a^672*x^252 + a^622*x^246 + a^94*x^244 + a^650*x^162 + a^441*x^108 + a^50*x^90 + x^84 + a^77*x^82 + a^328*x^36 + a^583*x^30 + a^407*x^28 + a^178*x^18 + a^492*x^12 + a^692*x^10 + a^78*x^6 + a^219*x^4 + a^69*x^2
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
            a^264*x^1458 + x^82
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
        orbitsTable[x^162 + x^84 + a^58*x^54 + a^58*x^28 + x^6 + a^531*x^2] := {One(F), a, a^2, a^3, a^6, a^7, a^44};
        orbitsTable[a^569 *x^82 + a^439 *x^30 + x^28] := {One(F), a, a^2};
        orbitsTable[2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2] := {One(F), a, a^2, a^7};
        orbitsTable[x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2] := {One(F), a, a^2, a^3, a^4, a^5, a^6, a^8, a^10, a^15, a^17, a^20};
        orbitsTable[x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2] := {0, a^1, a^2, a^3, a^4, a^5, a^6, a^7, a^8, a^9, a^10, a^12, a^13, a^16, a^17, a^19, a^22, a^23, a^31, a^34, a^35, a^36, a^38, a^39, a^44, a^45, a^47, a^48, a^50, a^54, a^66, a^72, a^90};
        orbitsTable[a^438*x^486 + a^180*x^324 + a^458*x^270 + a^672*x^252 + a^622*x^246 + a^94*x^244 + a^650*x^162 + a^441*x^108 + a^50*x^90 + x^84 + a^77*x^82 + a^328*x^36 + a^583*x^30 + a^407*x^28 + a^178*x^18 + a^492*x^12 + a^692*x^10 + a^78*x^6 + a^219*x^4 + a^69*x^2] := {One(F), a, a^2, a^6, a^8, a^13, a^15};
        
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

        polyOrbit := {One(1), a, a^2, a^4, a^5, a^7, a^8, a^10, a^11, a^13, a^14, a^16, a^17, a^19, a^20, a^22, a^23, a^25, a^26, a^28, a^29, a^31, a^32, a^34, a^35, a^37, a^38, a^40, a^43, a^44, a^46, a^47, a^49, a^50, a^52, a^53, a^55, a^56, a^58, a^59, a^61, a^62, a^64, a^65, a^67, a^70, a^71, a^73, a^74, a^76, a^77, a^79, a^80, a^85, a^86, a^88, a^89, a^91, a^92, a^94, a^97, a^98, a^100, a^101, a^103, a^104, a^106, a^107, a^110, a^112, a^113, a^115, a^116, a^118, a^119, a^121, a^137, a^139, a^142, a^143, a^145, a^146, a^148, a^151, a^152, a^154, a^155, a^157, a^160, a^161, a^169, a^170, a^172, a^173, a^175,  a^178, a^179, a^181, a^182, a^184, a^187, a^188, a^193, a^196, a^197, a^199, a^200, a^202, a^211, a^214, a^215, a^220, a^223, a^224, a^226, a^227,  a^229, a^233, a^235, a^236, a^238, a^241, a^242, a^274, a^277, a^278, a^281, a^283, a^295, a^296, a^301, a^304, a^305, a^308, a^310, a^317, a^319,  a^322, a^323, a^337, a^344, a^346, a^349, a^350, a^358, a^359, a^362, a^364, a^547, a^553, a^562, a^565, a^589, a^592, a^607, a^688, a^715};
        orbitsTable[x^10 +x^6+2*x^2] := polyOrbit;
        orbitsTable[x^10 +2*x^6+2*x^2] := polyOrbit;
    elif n eq 8 then
        orbitsTable[x^2]:={One(F)};
        orbitsTable[x^14]:={One(F)};
        orbitsTable[x^122]:={One(F)};
        orbitsTable[x^1094]:={One(F)};
        orbitsTable[a^714 * x^244 + a^2074 * x^84 + x^82]:={a^i: i in [0, 1, 2, 4, 5, 29]};
        orbitsTable[a^264 * x^1458 + x^82]:={a^i: i in [0, 1, 2, 3, 4, 7]};
        orbitsTable[a^418 * x^2188 + a^4338 * x^108 + x^82]:={a^i: i in [0, 1, 2, 3, 6, 35]};
        orbitsTable[x^246+x^82+2 * x^6+x^2]:={One(F), a, a^2, a^3, a^4, a^5, a^6, a^7, a^8, a^9, a^10, a^11, a^12, a^13, a^14, a^15, a^16, a^17, a^18, a^19, a^20, a^21, a^22, a^23, a^24, a^25, a^26, a^27, a^28, a^29, a^30, a^31, a^32, a^33, a^35, a^36, a^37, a^38, a^39, a^40, a^41, a^42, a^43, a^44, a^45, a^46, a^47, a^48, a^49, a^50, a^51, a^52, a^53, a^54, a^55, a^56, a^57, a^58, a^59, a^60, a^62, a^63, a^64, a^65, a^66, a^67, a^68, a^69, a^70, a^72, a^73, a^75, a^76, a^78, a^79, a^81, a^82, a^83, a^84, a^85, a^86, a^87, a^88, a^89, a^90, a^91, a^92, a^93, a^94, a^95, a^96, a^97, a^99, a^100, a^101, a^102, a^103, a^104, a^105, a^107, a^109, a^110, a^111, a^112, a^113, a^114, a^115, a^117, a^118, a^119, a^120, a^121, a^122, a^123, a^125, a^126, a^127, a^129, a^130, a^131, a^132, a^133, a^134, a^135, a^136, a^137, a^139, a^142, a^143, a^146, a^147, a^148, a^149, a^150, a^151, a^153, a^154, a^155, a^157, a^158, a^159, a^161, a^162, a^163, a^164, a^165, a^166, a^167, a^171, a^172, a^173, a^174, a^175, a^177, a^178, a^179, a^181, a^182, a^183, a^185, a^186, a^188, a^189, a^190, a^191, a^192, a^195, a^196, a^197, a^199, a^200, a^201, a^202, a^203, a^204, a^205, a^207, a^208, a^209, a^210, a^211, a^212, a^213, a^214, a^215, a^216, a^217, a^219, a^220, a^222, a^224, a^225, a^226, a^227, a^228, a^231, a^232, a^233, a^234, a^235, a^236, a^237, a^238, a^239, a^241, a^242, a^243, a^244, a^246, a^247, a^248, a^249, a^253, a^254, a^256, a^257, a^258, a^260, a^261, a^263, a^264, a^266, a^267, a^269, a^270, a^271, a^274, a^275, a^278, a^281, a^282, a^284, a^287, a^289, a^291, a^292, a^293, a^294, a^299, a^304, a^305, a^306, a^307, a^308, a^309, a^311, a^312, a^314, a^315, a^317, a^320, a^321, a^323, a^324, a^326, a^329, a^333, a^334, a^336, a^340, a^342, a^346, a^347, a^349, a^351, a^359, a^360, a^361, a^363, a^365, a^369, a^372, a^373, a^374, a^377, a^378, a^380, a^381, a^382, a^383, a^386, a^390, a^394, a^396, a^397, a^400, a^401, a^402, a^405, a^406, a^412, a^414, a^415, a^419, a^420, a^427, a^429, a^431, a^434, a^435, a^439, a^442, a^445, a^447, a^449, a^455, a^456, a^457, a^461, a^462, a^469, a^470, a^472, a^473, a^475, a^477, a^493, a^495, a^496, a^497, a^498, a^500, a^504, a^506, a^507, a^513, a^515, a^519, a^520, a^521, a^523, a^525, a^529, a^533, a^539, a^540, a^544, a^547, a^552, a^557, a^558, a^560, a^564, a^565, a^567, a^568, a^576, a^583, a^584, a^591, a^593, a^598, a^601, a^611, a^613, a^620, a^621, a^623, a^637, a^641, a^643, a^646, a^649, a^652, a^653, a^656, a^658, a^659, a^667, a^668, a^670, a^679, a^681, a^685, a^694, a^697, a^699, a^703, a^704, a^716, a^721, a^724, a^736, a^775, a^784, a^787, a^791, a^796, a^807, a^810, a^816, a^822, a^830, a^837, a^845, a^855, a^865, a^867, a^880, a^933, a^935, a^939, a^954, a^975, a^986, a^994, a^1080, a^1107, a^1134, a^1194};
        // 8.9 orbits give false negatives
        // orbitsTable[a^3608 * x^1458 + a^3608 * x^738 + a^3810 * x^486 + a^3810 * x^246 + a^3413 * x^162 +a^3413 * x^82 + a^3608 * x^18 + a^3810 * x^6 + a^2565 * x^2]:={a^i: i in [0, 1, 2, 4, 7, 10, 13, 14, 17, 20, 41, 43]};
        // 8.10 orbit not computed yet.
        // orbitsTable[a^164 * x^1458 + a^164 * x^738 + a^950 * x^486 + a^950 * x^246 + a^616 * x^162 +a^616 * x^82 + a^164 * x^18 + a^950 * x^6 + a^6297 * x^2]:={};//?
    end if;

    return orbitsTable;
end function;
