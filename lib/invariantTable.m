load "representatives.m";

load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/planar.m";


computeInvariantTable := procedure(n)

    FuctionList:=getFun(n);
    R<x>:=Parent(FuctionList[1]);
    F<a>:=BaseRing(R);
    e:=One(F);

    invariantTable := AssociativeArray();

    for f in FuctionList do
        N:=[0,0];
        if isDOPolynomial(f) then
            N:=Nuclei(f, e);
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
            x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + 
            x^10 + a^449*x^6 + a^279*x^2
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
            a^438*x^486 + a^180*x^324 + a^458*x^270 + a^672*x^252 + a^622*x^246 + a^94*x^244
            + a^650*x^162 + a^441*x^108 + a^50*x^90 + x^84 + a^77*x^82 + a^328*x^36 + 
            a^583*x^30 + a^407*x^28 + a^178*x^18 + a^492*x^12 + a^692*x^10 + a^78*x^6 + 
            a^219*x^4 + a^69*x^2
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
            x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + 
            a^561*x^6 + a^209*x^2
            };
            
            invariantTable["[ 0, 0 ].8736"]:={
            x^122
            };
            
            invariantTable["[ 9, 9 ].NA"]:={
            x^10
            };

  elif n eq 8
        invariantTable["[ 6561, 6561 ].NA"]:={
        x^2
        };
        
        invariantTable["[ 3, 9 ].NA"]:={
        a^714*x^244 + a^2074*x^84 + x^82,
        a^418*x^2188 + a^4338*x^108 + x^82
        };
        
        invariantTable["[ 3, 81 ].NA"]:={
        a^3608*x^1458 + a^3608*x^738 + a^3810*x^486 + a^3810*x^246 + a^3413*x^162 + 
        a^3413*x^82 + a^3608*x^18 + a^3810*x^6 + a^2565*x^2,
        x^246 + x^82 + 2*x^6 + x^2,
        a^164*x^1458 + a^164*x^738 + a^950*x^486 + a^950*x^246 + a^616*x^162 + 
        a^616*x^82 + a^164*x^18 + a^950*x^6 + a^6297*x^2
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

