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
function VerifyIdentity(SF,e)
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

LeftNucleus := function(SF,cosets)
    for c in cosets do
        if is_in_left_nucleus(SF, Random(c)) then
            return #c;
        end if;
    end for;

    return 0;
end function;

MiddleNucleus := function(SF,cosets)
    for c in cosets do
        if is_in_middle_nucleus(SF, Random(c)) then
            return #c;
        end if;
    end for;

    return 0;
end function;

RightNucleus := function(SF,cosets)
    for c in cosets do
        if is_in_right_nucleus(SF, Random(c)) then
            return #c;
        end if;
    end for;

    return 0;
end function;

/* Precomputation utilities for the subfields for the nuclei invariants */
PrecomputeSubfields := function(F)
    n := Degree(F);

    divisors := Divisors(n);

    Reverse(~divisors);
    Subfields := [{x : x in sub<F|d>} : d in divisors];
    Subfields;

    Reverse(~divisors);
    for i := 1 to #divisors do
        to_remove := {x : x in sub<F|divisors[i]>};
        
        for j := 1 to #Subfields-i do
            Subfields[j] diff:= to_remove;
        end for;
    end for;

    return Subfields;
end function;

CombineSubfieldsWithIdentity := function(S, e)
    combined := [];
    for s in S do
        Append(~combined, {e*si : si in s});
    end for;

    return combined;
end function;

/* Compute the nuclei invariants */
function NucleiInvariants(f, Subfields)
    F:=BaseRing(Parent(f));

    PSF := DOtoPresemifield(f);
    SF := PresemifieldToSemifield(PSF, One(F));

    e := PSF[{One(F)}];
    assert VerifyIdentity(SF,e);

    cosets := CombineSubfieldsWithIdentity(Subfields, e);

	ln := LeftNucleus(SF,cosets);
	mn := MiddleNucleus(SF,cosets);
	rn := RightNucleus(SF,cosets);

    assert ln ne 0;
    assert mn ne 0;
    assert rn ne 0;

	return [ln, mn, rn];
end function;
