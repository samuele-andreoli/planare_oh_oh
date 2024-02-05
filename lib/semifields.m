PresemifieldToDO:=function(PSF)
  F:=Parent(Rep(Keys(PSF)));
  return Interpolation([a: a in F],[PSF[{a,a}]/2: a in F]);
end function;


DOtoPresemifield:=function(f)
    F:=BaseRing(Parent(f));
    PSF:=AssociativeArray();
    for a,b in F do
        if not {a,b} in Keys(PSF) then
            PSF[{a,b}]:=Evaluate(f,a+b)-Evaluate(f,a)-Evaluate(f,b);
        end if;
    end for;

    return PSF;
end function;


PresemifieldToSemifield:=function(PSF, e)
    F := Parent(e);
    if IsZero(e) then error "e is zero"; end if;
    SF:=AssociativeArray();
    for a,b in F do
        a0:=PSF[{a,e}];
        b0:=PSF[{b,e}];
        if not {a0,b0} in Keys(SF) then
            SF[{a0,b0}]:=PSF[{a,b}];
        end if;
    end for;

    return SF;
end function;

/* For verifying that the semifields produced by the function above have 1 as the identity */
function aux_verify_identity(SF,e)
	F := Parent(e);
	for x in F do
		if SF[{x,e}] ne x then
			return false;
		end if;
	end for;

	return true;
end function;

/* Checks whether "a" is in the left nucleus of the semifield defined by "f" */
function is_in_left_nucleus(SF,a)
	F := Parent(a);
	for x in F do
		for y in F do
			lhs := SF[{a, SF[{x,y}]}];
			rhs := SF[{SF[{a,x}], y}];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;

	return true;
end function;

/* Checks whether "a" is in the middle nucleus of the semifield defined by "f" */
function is_in_middle_nucleus(SF,a)
	F := Parent(a);
	for x in F do
		for y in F do
			lhs := SF[{x, SF[{a,y}]}];
			rhs := SF[{SF[{x,a}], y}];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;

	return true;
end function;

/* Checks whether "a" is in the right nucleus of the semifield defined by "f" */
function is_in_right_nucleus(SF,a)
	F := Parent(a);
	for x in F do
		for y in F do
			lhs := SF[{x, SF[{y,a}]}];
			rhs := SF[{SF[{x,y}], a}];
			if lhs ne rhs then
				return false;
			end if;
		end for;
	end for;

	return true;
end function;


function left_nucleus_with_identity(SF,e)
	F := Parent(e);
    p := Characteristic(F);
    n := Degree(F);

	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { e * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff {e *  x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_left_nucleus(SF, alpha);
		if condition then
			return p^current;
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;

	return 0;
end function;


/* Find the subfield that represents the middle nucleus of a function in the given dimension. */
middle_nucleus_with_identity := function(SF,e)
	F := Parent(e);
    p := Characteristic(F);
    n := Degree(F);

	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { e * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff {e *  x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_middle_nucleus(SF, alpha);
		if condition then
			return p^current;
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;

	return 0;
end function;


right_nucleus_with_identity := function(SF,e)
	F := Parent(e);
    p := Characteristic(F);
    n := Degree(F);

	possible_dimensions := Divisors(n);

	while #possible_dimensions gt 0 do
		current := possible_dimensions[#possible_dimensions];
		current_set := { e * x : x in GF(p^current) };
		for i in [1..#possible_dimensions-1] do
			current_set := current_set diff {e *  x : x in GF(p^possible_dimensions[i]) };
		end for;
		alpha := Random(current_set);

		condition := is_in_right_nucleus(SF, alpha);
		if condition then
			return p^current;
		else
			Exclude(~possible_dimensions, current);
		end if;
	end while;

	return 0;
end function;

/* Compute the nuclei invariants */
function NucleiInvariants(f)
    F:=BaseRing(Parent(f));

    PSF := DOtoPresemifield(f);
    SF := PresemifieldToSemifield(PSF, One(F));

    e := PSF[{One(F)}];
    assert aux_verify_identity(SF,e);

	ln := left_nucleus_with_identity(SF,e);
	mn := middle_nucleus_with_identity(SF,e);
	rn := right_nucleus_with_identity(SF,e);

	return [ln, mn, rn];
end function;
