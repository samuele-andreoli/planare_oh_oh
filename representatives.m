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
  end if;
  return [];
end function;

/*
load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/dupeq.m";
load "lib/planar.m";
for n:=3 to 6 do
  Fun:=getFun(n);
  printf "\n\ndimension %o\n",n;
  Subfields:=PrecomputeSubfields(GF(3^n));
  i:=0;
  for f in Fun do
    i +:=1;
    printf "\n%o.%o \t",n,i;
    if isDOPolynomial(f) then
    	printf "%o ",NucleiInvariantsCommutativeSemifield(f, Subfields);
    end if;
    printf "%o ",AutomoriphismGroupOrderFromFunction(f);
    P:=partitionByL2(f);
    printf "%o %o",#P,[Rep(o): o in P];
  end for;
end for;
*/
