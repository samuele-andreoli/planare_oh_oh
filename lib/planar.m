/* Compute p-weight of n */
weight := function(p,n)
	w := 0;
	while n gt 0 do
		r := n mod p;
		n := n div p;

		if r ne 0 then
			w := w+1;
		end if;
	end while;

    return w;
end function;

/* FFs is a list of nonzero elements a in GF(p^n) such that -a is not in FFs */

getFFs:=function(F)
	FFs:=[a: a in F|not IsZero(a)];
	for i:=1 to ((#F-1) div 2) do
  		Remove(~FFs,Index(FFs,-FFs[i]));
	end for;

	return FFs;
end function;

fastIsPlanarDOPoly:=function(f,FFs)
	S:={};

	for a in FFs do
		b:=Evaluate(f,a);

		if b in S then
			return false;
		end if;

		Include(~S, b);
	end for;

	return true;
end function;

/* Check if a function is DO poly */
isDOPolynomial := function(f)
	F := BaseRing(Parent(f));
    p := Characteristic(F);

    e := -1;
    for c in Coefficients(f) do
        e := e+1;
        if IsZero(c) then
            continue;
        end if;

        if weight(3,e) gt 2 then
            return false;
        end if;
    end for;

    return true;
end function;


/* Checks if the given funciton is a planar function,
 * works for all functions
 */
isPlanarGeneric := function(f)
	FF := BaseRing(Parent(f));
	PR<x> := PolynomialRing(FF);

	for a in FF do
		if a eq 0 then
			continue;
		end if;

		df := Evaluate(f, x+a) - f;
		if #{Evaluate(df, x) : x in FF} ne #FF then
			return false;
		end if;
	end for;

	return true;
end function;

isPlanarDOPoly := function(f)
    K:=[x : x in BaseRing(Parent(f)) | not IsZero(x)];
    S:={};

    while #K ne 0 do
        a := K[1];
        b := Evaluate(f,a);
        if b in S then
            return false;
        end if;

        Include(~S, b);
        K := K[2..#K];
        Remove(~K,Index(K,-a));
    end while;

    return true;
end function;


/* Will select the fastest planarity check when possible, otherwise the normal one */
isPlanar := function(f)
    // Quick linear check whether f is a DO polynmomial.
	if isDOPolynomial(f) then
		return isPlanarDOPoly(f);
	else
		return isPlanarGeneric(f);
	end if;
end function;


/* Check if all the functions in a list are planar. */
isAllPlanar := function(Fs)
	for f in Fs do
		if not isPlanar(f) then;
			return false;
		end if;
	end for;

	return true;
end function;

