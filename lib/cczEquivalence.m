/* Linear code associated to f */
function LinearCodeFromFunction(f)
	F := BaseRing(Parent(f));
	n := Degree(F);
    Fp := GF(Characteristic(F));

	bits := &cat[[Fp!1] cat Flat(x) cat Flat(Evaluate(f,x)) : x in F];
	M := Transpose(Matrix(Fp, #F, 2*n+1, bits));
	C := LinearCode(M);

	return C;
end function;

// Code for testing CCZ equivalence. Runs out of memory for high dimension
function IsCCZEquivalent(f1, f2)
	code1 := LinearCodeFromFunction(f1);
	code2 := LinearCodeFromFunction(f2);
	res, map := IsIsomorphic(code1, code2);

	return res;
end function;


// Code for testing CCZ equivalence of a list of functions against a fixed function
function CCZInequivalentToF(f, List)
    code_f := LinearCodeFromFunction(f);

    CCZInequiv := [];

    for g in List do
        code_g := LinearCodeFromFunction(g);

        if not IsIsomorphic(code_f, code_g) then
            Append(~CCZInequiv, g);
        end if;
    end for;

    return CCZInequiv;
end function;


/* Finds the code invariant for the given function */
function AutomoriphismGroupOrderFromFunction(f)
	C := LinearCodeFromFunction(f);
	A := AutomorphismGroup(C);

	return Order(A);
end function;
