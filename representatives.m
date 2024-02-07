//The classification in n=8 could be incomplete
getFun:=function(n)
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
  		x^10 + x^6 + 2*x^2,
  		x^10 + 2*x^6 + 2*x^2,
  		x^14,
  		x^90 + x^2,
  		x^162 + x^108 +2*x^84 + x^2
  	];
  elif n eq 6 then
    return [
    x^2,
		x^10,
		x^122,
		x^162 + x^84 + a^58*x^54 + a^58*x^28 + x^6 + a^531*x^2,
		a^569 *x^82 + a^439 *x^30 + x^28,
		2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2,
		x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2,
		x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2,
		a^438*x^486 + a^180*x^324 + a^458*x^270 + a^672*x^252 + a^622*x^246 + a^94*x^244 + a^650*x^162 + a^441*x^108 + a^50*x^90 + x^84 + a^77*x^82 + a^328*x^36 + a^583*x^30 + a^407*x^28 + a^178*x^18 + a^492*x^12 + a^692*x^10 + a^78*x^6 + a^219*x^4 + a^69*x^2,
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
  	x^10 +x^6+2*x^2,
   	x^10 +2*x^6+2*x^2,
    	x^14,
     	x^122
	];
  elif n eq 8 then
  	return [
   	x^2,
	x^14,
	x^122,
	x^1094,
	a^714 * x^244 + a^2074 * x^84 + x^82,
	a^264 * x^1458 + x^82,
	a^418 * x^2188 + a^4338 * x^108 + x^82,
	x^246+x^82+2 * x^6+x^2,
	a^3608 * x^1458 + a^3608 * x^738 + a^3810 * x^486 + a^3810 * x^246 + a^3413 * x^162 +a^3413 * x^82 + a^3608 * x^18 + a^3810 * x^6 + a^2565 * x^2,
	a^164 * x^1458 + a^164 * x^738 + a^950 * x^486 + a^950 * x^246 + a^616 * x^162 +a^616 * x^82 + a^164 * x^18 + a^950 * x^6 + a^6297 * x^2
	];
  end if;
  return [];
end function;

/*
load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/dupeq.m";
load "lib/planar.m";
for n:=3 to 8 do
  Fun:=getFun(n);
  printf "\n\ndimension %o\n",n;
  i:=0;
  F:=BaseRing(Parent(Fun[1]));
  e:=One(F);
  subfields,sizes:=PrecomputeSubfields(F);
  for f in Fun do
    i +:=1;
    printf "\n%o.%o \t",n,i;
    N:=[0,0];
    if isDOPolynomial(f) then
    	N:=Nuclei(f, e,subfields,sizes);
    end if;
    printf "%o ",N;
    if (n lt 6) or ((n eq 6) and not N in {[3^6,3^6],[3^(2),3^(2)]}) then
    	printf "%o ",AutomoriphismGroupOrderFromFunction(f);
    end if;
    //P:=partitionByL2(f);
    //printf "%o %o",#P,[Rep(o): o in P];
  end for;
end for;
*/
