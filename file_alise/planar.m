function findInequivalentFunctions(listOfPNs, dimension)
	inequivalentFunctions := [];
	while #listOfPNs gt 0 do
		#listOfPNs;
		CCZ := CCZforFunction(listOfPNs, 3, dimension);
		Append(~inequivalentFunctions, CCZ);
		listOfPNs := removeElementsFromList(listOfPNs, CCZ);
	end while;
return inequivalentFunctions;
end function;


function isPlanarOrNot(F)
	FF := BaseRing(Parent(F));
	PR<x> := PolynomialRing(FF);

	isPotentiallyTrue := true;

	for a in FF do
		if a eq 0 then
			continue;
		end if;
		df := Evaluate(F, x+a) - F;
		if #{ Evaluate(df, x) : x in FF } ne #FF then
			isPotentiallyTrue := false;
			break;
		end if;
	end for;

	return isPotentiallyTrue;
end function;

function isAllPlanar(Fs)
	isPlanar := true;
	for f in Fs do
		if not isPlanarOrNot(f) then;
			isPlanar := false;
			break;
		end if;
	end for;
	return isPlanar;
end function;

function genLinearCodeFromFunction(poly_f, p, n)
	GF<z> := FiniteField(p,n);
	f:= func< x| Evaluate(poly_f, x)>;
	M := Matrix(FiniteField(p), 2*n+1, p^n,
		[1: x in GF]
		cat [Trace(z^i * x): x in GF, i in [0..n-1]]
		cat [Trace(z^i * f(x)): x in GF, i in [0..n-1]]
	);
	// printf "GenMatrix :=%o\n", M;
	return LinearCode(M);
end function;

// Code for testing CCZ equivalence 
function isCCZEquivalent(f1, f2, p, n)
	Code1 := genLinearCodeFromFunction(f1, p, n);
	Code2 := genLinearCodeFromFunction(f2, p, n);
	res, map := IsIsomorphic(Code1, Code2);
	return res;
end function;

// When should I use this?
function getEquivalentCodes(f1, f2, p, n)
	Code1 := genLinearCodeFromFunction(f1, p, n);
	Code2 := genLinearCodeFromFunction(f2, p, n);
	return <Code1,Code2>;
end function;

// PN number 1: x^2 in F_(p^n)
// Verified that this are planar functions, at least for p = 3
function f1(p, n)
	FF<a> := FiniteField(p^n);
	PR<x> := PolynomialRing(FF);
	f := x^2;
	return f;
end function;

// PN number 2: x^(p^k + 1) in F_(p^n)
// Verified that this are planar functions.
function f2(p, n, k)
	assert k le n div 2;
	assert IsOdd(n div Gcd(k, n));
	FF<a> := FiniteField(p^n);
	PR<x> := PolynomialRing(FF);
	f := x^((p^k) + 1);
	return f;
end function;

// Generate all f2 functions.
function f2all(p, n)
	Fs := [];
	for k in [1 .. 50] do
		if k le n div 2 then
			if IsOdd(n div Gcd(k, n)) then
				f := f2(p, n, k);
				Append(~Fs, f);
			end if;
		end if;
	end for;
	return Fs;
end function;

// PN number 3
// Verified
function f3(n)
	assert n ge 5;
	assert IsOdd(n);
	FF<a> := FiniteField(3^n);
	PR<x> := PolynomialRing(FF);
	f := x^(10) + x^6 - x^2;
	return f;
end function;

// PN number 4
// Verified
function f4(n)
	assert n ge 5;
	assert IsOdd(n);
	FF<a> := FiniteField(3^n);
	PR<x> := PolynomialRing(FF);
	f := x^(10) - x^6 -x^2;
	return f;
end function;

// PN number 5
function f5(p, s, k)
	assert Gcd(k, 3) eq 1;
	assert (k-s) div 3 eq 0;
	assert IsOdd(k div Gcd(k, s));
	FF<a> := FiniteField(p^(3*k));
	PR<x> := PolynomialRing(FF);
	f := x^(p^s + 1) - a^(p^k - 1)*x^(p^k) + p^(2*k+s);
	return f;
end function;

// Generate all f5 functions. Gcd(k, 3) eq 1, (k-s)/3 eq 0
// Verified
function f5all(p)
	Fs := [];
	range := 15;
	for k in [1 .. range] do
		if Gcd(k, 3) eq 1 then
			for s in [1 .. range] do
				if (k-s) div 3 eq 0 then
					if IsOdd(k div Gcd(k, s)) then
						f := f5(p, s, k);
						Append(~Fs, f);
					end if;
				end if;
			end for;
		end if;
	end for;
	return Fs;
end function;

// PN number 6
// Verified
function f6(n, k)
	assert k ge 3;
	assert IsOdd(k);
	assert Gcd(k, n) eq 1;
	FF<a> := FiniteField(3^n);
	PR<x> := PolynomialRing(FF);
	f := x^((3^k + 1) div 2);
	return f;
end function;

// Generate all f6 functions. K >= 3 and gcd(k, n) = 1
function f6all()
	Fs := [];
	range := 15;
	for k in [3 .. range] do
		if IsOdd(k) then
		//	for n in [1 .. range] do
			n := 5;
				if Gcd(k, n) eq 1 then
					f := f6(n, k);
					Append(~Fs, f);
				end if;
		//	end for;
		end if;
	end for;
	return Fs;
end function;

// PN number 7
// Working
function f7(p, n, r)
	FF := GF(p^n); /* Finite Field*/
	BF := GF(p^n^2); /* Base Field*/
	lambda := Random({x : x in BF | not x in FF}); /* So that (a,b) = a + l*b */
	f := [x : x in FF | not IsPower(x,2)][1];
	/* Truth table for x |-> x*x */
	/* Multiplication is defined by (a,b)*(c,d) = (ac + f t(bd), ad + bc */
	FROM := [];
	TO := [];
	
	for a in FF do
		for b in FF do
			/* Map (a,b)*(a,b) to (a^2 + f t(b^2), 2ab) */
			left_side := a^2 + f*(b^2)^(p^r);
			right_side := 2*a*b;
			from := a + lambda*b;
			too := left_side + lambda*right_side;
			Append(~FROM, from);
			Append(~TO, too);
		end for;
	end for;
	F := Interpolation(FROM, TO);
	return F;
end function;

// Generate all f7 functions
function f7all()
	// create appropriate variables for p, n and r
	p := 3; /* p characteristic */
	n := 2; /* n dimention */
	r := 2; /* r exponent in the automorphism t(x) = x^(p^r) */

	Fs := [];
	f := f7(p, n, r);
	Append(~Fs,f);
	return Fs;
end function;

// PN number 8
// Verified
function f8(p, n, s, k)
	assert n mod 3 eq 0;
	assert Gcd(3, k) eq 1;
	assert (k-s) mod 3 eq 0;
	FF<a> := GF(p^n);
	PR<x> := PolynomialRing(FF);
	t := GCD(s, n);
	assert ((n div t) mod 2) eq 1;
	f := x^(p^s+1) - a^(p^k-1)*x^(p^k + p^(2*k+s));
	return f;
end function;

// Generate all f8 PN functions
function f8all(p)
	Fs := [];
	for n in [1..15] do
		if n mod 3 eq 0 then
			k := n div 3;
			if Gcd(3, k) eq 1 then
				for s in [0..n-1] do
					if (k-s) mod 3 eq 0 then
						t := GCD(s,n);
						if (n div t) mod 2 eq 1 then
							if n eq 15 and s eq 11 and k eq 5 then
								// Stopping her because the arguments becomes too large to handle.
								break;
							end if;
							F := f8(p,n,s,k);
							Append(~Fs,F);
							//s;
						end if;
					end if;
				end for;
			end if;
		end if;
	end for;
	return Fs;
end function;

// PN number 9
// Not planar.. Figure out what's wrong.
function f9(p, n)
	assert IsPrime(p);
	Fs := [];
	st := {<s,t> : s, t in [1..n] | (2*s div Gcd(2*s, t)) mod 2 eq 0 and (q mod 4) eq 1 and (qprime mod 4) eq 1 where q is p^s where qprime is p^t};
	st;

	for pair in st do
		s := pair[1];
		t := pair[2];
		q := p^s;
		qprime := p^t;
		FF<a> := GF(q^4);
		PR<x> := PolynomialRing(FF);
		x;
		V := { v : v in GF(q^4) | v ne 0 and Order(v) eq (q^3 + q^2 + q + 1)};
		V;
		for v in V do
			f := x^(1 + qprime) - v*x^(q^3 + qprime*q);
			isPlanarOrNot(f);
			Append(~Fs, f);
		end for;
	end for;
	return Fs;
end function;

// PN number 10
function f10(p)
	Fs := [];
	assert IsPrime(p);
	m := 2; // TODO find m
	q := p^m;
	FF<a> := GF(q^2);
	PR<x> := PolynomialRing(FF);
	omega_beta := {<omega, beta> : omega, beta in FF | Trace(omega) eq 0};
	for pair in omega_beta do
		beta := pair[1];
		omega := pair[2];
		for s in [1 .. 50] do
			order := (q+1) div GCD(q+1, p^s +1);
			size_of_multiplicative_group := #FF - 1;
			divisors := Divisors(size_of_multiplicative_group);
			if order in divisors then
				Ks := [k : k in [1..#FF] | size_of_multiplicative_group div GCD(k, size_of_multiplicative_group) eq order];
				for k in Ks do
					b := a^k;
					subgroup := {b^n : n in [1..#FF] };
					if beta^(q-1) notin subgroup then
						elem := {a : a in FF | a ne 0 and Trace(a) eq 0 and a^(p^s) eq -a};
						if IsEmpty(elem) then
							f := Trace(x^(q+1)) + Trace(beta * x^(p^s + 1)*omega);
							return f;
							Append(~Fs, f);
						end if;
					end if;
				end for;
			end if;
		end for;
	end for;
	return Fs;
end function;

//g// PN number 11
//g// What is k???
//g// Figure out the whole G(x) = h(x - x^q^m)
//gfunction f11(p)
//g	assert IsPrime(p);
//g	Fs := [];
//g	k := 1; // TODO, what is k?
//g	m := 2*k + 1;
//g	q := 2; // q is a power of an odd prime p.
//g	size_FF := q^(2*m);
//g	FF<a> := GF(q^(2*m));;
//g	PR<x> := PolynomialRing(FF);
//g	h_x_first := h_x_func(x^(q^2 + 1), k, q);
//g	h_x_sec := h_x_func((x^q^2 + 1)^(q^m), k, q);
//g	f := Trace(x^2) + 1;
//gend function;

function h_x_func(x, k, q)
	h_x := 0;
	for i in [0..k] do
		h_x = h_x + (-1)^i * x^(q^(2*1));
	end for;
	for j in [0..k-1] do
		h_x = h_x + (-1)^(k+j)*x^(q^(2*j + 1));
	end for;
	return h_x;
end function;

// PN number 12, Cohen-Ganley semifield: "Commutative Semifields, Two Dimensional over Their Middle Nuclei."
// Verified that this is produces planar functions. TODO: Try different values of k.
function f12(k)
	FF := GF(3^(k));
	BF := GF(3^(2*k));
	t := Random({x : x in BF | not x in FF}); // lambda in the f7 (dikson semifield)
	n := [x : x in FF | not IsPower(x, 2)][1]; // Go through all possible choices of n
	// f(x) = n*x^3
	// g(x) = n*x^9 + n^3 * x

	// (t*alpha + beta)*(t*gamma + delta) = t {f(alpha*gamma) + beta*gamma} + {g(alpha*gamma) + beta*delta}
	// Assuming it's the same as with the Dikson semifield, we can do (t*alpha + beta)(t*alpha + beta) instead.
	// Nikolay should probably have a look at this..
	FROM := [];
	TO := [];

	for a in FF do
		for b in FF do
			right_side := (n * a^6 + 2*b*a);
			left_side := (n * a^(18) + n^3 * a^2 + b^2);
			from := t*a + b;
			too := left_side + t*right_side;
			Append(~FROM, from);
			Append(~TO, too);
			
		end for;
	end for;
	F := Interpolation(FROM, TO);
	return F;
end function;

// PN number 13, Ganley semifield: "Central weak nucleus semifields."
// TODO: Understand th. 5.1 in paper.
function f13(k)
	assert IsOdd(k);
	FF := GF(3^k);
	BF := GF(3^(2*k));
	t := Random({x : x in BF | not x in FF});
	n_1 := [x : x in FF | not IsPower(x, 2)][1];
	n_2 := [x : x in FF | not IsPower(x, 2) and x ne n_1][1];
	a_square := n_1 * n_2;
	a := Sqrt(a_square);
	
	FROM := [];
	TO := [];	

	for alpha in FF do
		for beta in FF do
			right_side := a * alpha^4 + 2*alpha*beta;
			left_side := n_1 * alpha^(10) + n_1 * n_2^2 + alpha^2 + beta^2;
			from := t*alpha + beta;
			too := left_side + t*right_side;
			Append(~FROM, from);
			Append(~TO, too);
		end for;
	end for;
	F := Interpolation(FROM, TO);
	return F;
end function;

// PN number 14
// Verified that it is planar.
function f14()
	FF<a> := GF(3^5);
	PR<x> := PolynomialRing(FF);
	f := x^2 + x^(90);
	return f;
end function;

// PN number 15, Coulter-Henderson-Kosick semifield: "Planar polynomials for commutativesemifields with specified nuclei"
// Verified that it is planar.
function f15()
	FF := GF(3^8);
	PR<x> := PolynomialRing(FF);
	L_x := x^(243) - x^(81) + x^9 + x^3 - x;
	D_x := x^(246) - x^(10);
	t_x := x^9 - x;
	f := Evaluate(L_x, t_x^2) + Evaluate(D_x, t_x) + x^2 div 2;
	return f;
end function;

// PN number 16, Penttila-Wiliams: "Ovoids of parabolic spaces."
function f16()
	1;
end function;

// PN number 17
// From "A New Tool for Assurance of Perfect Nonlinearity, p. 418, case studies, f_1
function f18()
	FF<a> := GF(7^3);
	PR<x> := PolynomialRing(FF);
	f := x^2 + x^56;
	return f;
end function;

function createListOfPNs()
	allPNs := [];
	func1 := f1(3, 5);
	func2 := f2all(3, 5);
	func3 := f3(5);
	func4 := f4(5);
	func6 := f6all();
	func14 := f14();
	Append(~allPNs, func1);
	allPNs cat:= func2;
	Append(~allPNs, func3);
	Append(~allPNs, func4);
	allPNs cat:= func6;
	Append(~allPNs, func14);
	return allPNs;
end function;

function checkPlanar()
	allFunctions := createListOfPNs();
	for func in allFunctions do
		func;
		if isPlanarOrNot(func) eq false then
			return false;
		end if;
	end for;
	return true;
end function;

function CCZforFunction(list_to_test, p, n)
	CCZ_to_function := [];
	func_to_test := list_to_test[1];
	for func in list_to_test do
		if isCCZEquivalent(func_to_test, func, p, n) eq true then
			Append(~CCZ_to_function, func);
		end if;
	end for;
	return CCZ_to_function;
end function;

function removeElementsFromList(list, elements_to_remove);
	new_list := [];
	for elem in list do
		in_both := false;
		for remove in elements_to_remove do
			if elem eq remove then
				in_both := true;
			end if;
		end for;
		if in_both eq false then
			Append(~new_list, elem);
		end if;
	end for;
	return new_list;
end function;
