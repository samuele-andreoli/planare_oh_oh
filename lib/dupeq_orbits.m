/*
 * Nikolay's brilliant way of classifying functions up tp equivalence.
 */

/* A modified version of the duplicate equivalence test for reconstructing the automorphism group
 * of a given function. More specifically, we want to partition the non-zero elements of FF into
 * "orbits" so that if X and Y belong to the same orbit, then there is a permutation pair (L1,L2)
 * with L1 * F * L2 = F and L1(X) = Y. Note that if L1 * F * L2 = F, then L1^(-1) * F * L2^(-1) = F
 * as well, so this realation is symmetric and gives a correctly defined equivalence relation.
 */

/* The state is represented by a triple (L1, L2, P) where L1 and L2 are partial truth tables
   for l1 and l2, and P is a set of pairs of the form <x,y> meaning that {+- x} maps to {+- y}
   but we do not know the exact signs.
*/

forward derivel2;

function firstFree(L2)
	F := Universe(L2);

	if #F eq #L2 then
		return Zero(F);
	end if;

	for x in F do
		if not IsDefined(L2, x) then
			return x;
		end if;
	end for;
end function;

function codomain(L2)
	return {x : x in Universe(L2)} diff {l2x : x->l2x in L2};
end function;

/* Given a list of newly set values for L1, derives all values of L1 that can be
 * obtained from them and the currently known values. Returns:
 * - a Boolean value indicating whether a contradiction has been encountered;
 * - the newly derived pairs for L1;
 * - the new TT for L1;
 * - the new TT for L2;
 *   The new values are given as a sequence of inputs, e.g. newValues = [ a, b, c ]
 *   means that we now know L1[a], L1[b], and L1[c], which we did not know before.
 */
function derivel1(f,g,finv,ginv,L1,L2,P,newValues)
	primeField := {x : x in PrimeField(Universe(f)) | x ne 0};

	/* To derive new values, we combine all known values of L1 with the new ones
	 * using linear combinations.
	 */
	for v in newValues do
		for c2 in primeField do
			newX2 := c2*v;
			newY2 := c2*L1[v];

			for x->l1x in L1 do
				for c1 in primeField do
					newX := newX2 + c1 * x;
					newY := newY2 + c1 * l1x;

					if IsDefined(L1,newX) then
						if L1[newX] ne newY then
							return false, [], [], [];
						end if;
					else
						L1[newX] := newY;

						/* Since we have l1(f(l2(x))) = g(x), and we know L1[newX], we can obtain
						 * a contradiction in several ways:
						 * - if newX is in the image of f, but newY is not in the image of g;
						 * - if newX is not in the image of f, but newY is in the image of g
						 * - if L2[newX] or L2[-newX] is already defined, but the value is
						 *   not one of newY or -newY
						 */
						if IsDefined(finv, newX) then
							if not IsDefined(ginv,newY) then
								/* This has been confirmed to cut off unnecessary branches */
								return false, [], [], [];
							end if;

							L2x := ginv[newY];
							L2y := finv[newX];

							if IsDefined(L2,L2x) then
								if not L2[L2x] in {L2y, -L2y} then
									return false, [], [], [];
								end if;
							end if;

							if IsDefined(L2,-L2x) then
								if not L2[-L2x] in {L2y, -L2y} then
									return false, [], [], [];
								end if;
							end if;

							if not IsDefined(L2,L2x) then
								/* Now we know that { -x, +x } maps to { -y, +y } via L2,
								 * but we do not know how, so we add it to the list of
								 * pairs that need to be resolved
								 */
								Include(~P, <L2x, L2y>);
							end if;
						else
							if IsDefined(ginv,newY) then
								/* This has been confirmed to cut off unnecessary branches */
								return false, [], [], [];
							end if;
						end if;
					end if;
				end for;
			end for;
		end for;
	end for;

	return true, L1, L2, P;
end function;

/* Given a list of newly set values for L2, derives all values of L2 that can be
 * obtained from them and the known values. Returns:
 * - a Boolean value indicating whether a contradiction has been encountered;
 * - the new TT for L1;
 * - the new TT for L2;
 *   The new values are given as a sequence of inputs, e.g. newValues = [ a, b, c ]
 *   means that we now know L2[a], L2[b], and L2[c], which we did not know before.
 */
function derivel2(f,g,finv,ginv,L1,L2,P,newValues)
	newL1 := {};

	primeField := {x : x in PrimeField(Universe(f)) | x ne 0};

	/* To derive new values, we combine all known values of L2 with the new ones
	 * using linear combinations.
	 */

	for v in newValues do
		for c2 in primeField do
			newX2 := c2 * v;
			newY2 := c2 * L2[v];

			for x->l2x in L2 do
				for c1 in primeField do
					newX := newX2 + c1 * x;
					newY := newY2 + c1 * l2x;

					/* Possible contradiction */
					if IsDefined(L2, newX) then
						if L2[newX] ne newY then
							/* This has been confirmed to cut off unnecessary branches */
							return false, [], [], [], [];
						end if;
					else
						L2[newX] := newY;

						/* Since we know L2(newX) = newY, and L1(f(L2(x))) = g(x),
						* we have that L1[ f(L2(newX)) ] = g( newX ), i.e. we can
						* derive a new value of L1 (if it has not been defined yet
						*/

						newL1x := f[newY];
						newL1y := g[newX];

						/* Possible contradiction for L1 */
						if IsDefined(L1,newL1x) then
							if L1[newL1x] ne newL1y then
								/* This has been confirmed to cut off unnecessary branches */
								return false, [], [], [], [];
							end if;
						else
							L1[newL1x] := newL1y;
							Include(~newL1, newL1x);
						end if;
					end if;
				end for;
			end for;
		end for;
	end for;

	/* If we have derived new values for L1, we now call the companion function for L1
	 * to derive all possible values. If we encounter contradiction, we fail altogether.
	 */
	return derivel1(f,g,finv,ginv,L1,L2,P,newL1);
end function;

/* Note that f and g should be given as TT's (associative arrays), and finv and ginv should
 * be partially filled TT's, with the inverse of any element being one of its two preimages
 */
function process(f, g, finv, ginv, L1, L2, P, monomial)
	F := Universe(f);

	if #L1 eq #F and #L2 eq #L1 then
		return true, L1, L2;
	end if;

	/* If we are here, we assume that all linear combinations for L1 and L2
	   have already been derived. We thus need to either:
	   1) Process more pairs from P, or
	   2) Guess a new value of e.g. L2 if no pairs remain to be processed
	*/

	if #P ne 0 then
		pair := Rep(P);
		Exclude(~P, pair);

		x := pair[1];
		y := pair[2];

		/* We know that { -x, +x } will map to { -y, +y }, but we guess
		   which of two possibilities will take place
		*/
		L2[-x] := -y;
		L2[x] := y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P,[x]);

		if hope then
			success, l1, l2 := process(f,g,finv,ginv,newL1,newL2,newP,monomial);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */
		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P,[x]);
		if hope then
			success, l1, l2 := process(f,g,finv,ginv,newL1,newL2,newP,monomial);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If both options lead to contradictions, we are already in the soup */
		return false, [], [];
	end if;

	/* If there are no pairs to process, we guess a value of L2 instead */

	/* Get the first free element of L2 (whose value we will guess) */
	if #L2 eq 1 then
		b := One(F);
	else
		b := firstFree(L2);
	end if;

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq Zero(F) then
		/* Quick and easy sanity check */
		assert #L2 eq #L1;
		assert #L2 eq #F;

		return true, L1, L2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if monomial and b eq One(F) then
		D := [One(F)];
	else
		D := codomain(L2);
	end if;

	for v in D do
		L2[b] := v;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P,[b]);
		if hope then
			success, l1, l2 := process(f,g,finv,ginv,newL1,newL2,newP,monomial);
			if success then
				return true, l1, l2;
			end if;
		end if;
	end for;

	return false, [], [];
end function;

function process_fix_l2(f, g, finv, ginv, L1, L2, P, fixX, fixY)
	F := Universe(f);

	if #L1 eq #F and #L2 eq #L1 then
		return true, L1, L2;
	end if;

	/* If we are here, we assume that all linear combinations for L1 and L2
	   have already been derived. We thus need to either:
	   1) Process more pairs from P, or
	   2) Guess a new value of e.g. L2 if no pairs remain to be processed
	*/

	if #P ne 0 then
		pair := Rep(P);
		Exclude(~P, pair);

		x := pair[1];
		y := pair[2];
		/* We know that { -x, +x } will map to { -y, +y }, but we guess
		   which of two possibilities will take place
		*/
		L2[-x] := -y;
		L2[x] := y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P, [x]);

		if hope then
			success, l1, l2 := process_fix_l2(f, g, finv, ginv, newL1, newL2, newP, fixX, fixY);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */
		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P, [x]);
		if hope then
			success, l1, l2 := process_fix_l2(f, g, finv, ginv, newL1, newL2, newP, fixX, fixY);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If both options lead to contradictions, we are already in the soup */
		return false, [], [];
	end if;

	/* If there are no pairs to process, we guess a value of L2 instead */

	/* Get the first free element of L2 (whose value we will guess) */
	if #L2 eq 1 then
		b := fixX;
	else
		b := firstFree(L2);
	end if;

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq 0 then
		/* Quick and easy sanity check */
		assert #L2 eq #L1;
		assert #L2 eq #F;

		return true, L1, L2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if b eq fixX then
		D := [fixY];
	else
		D := codomain(L2);
	end if;

	for v in D do
		L2[b] := v;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P,[b]);
		if hope then
			success, l1, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l1, l2;
			end if;
		end if;
	end for;

	return false, [], [];
end function;

/* Fixes L1(fixX) to fixY, and tries to find a pair (L1, L2)
 * satisfying this condition
 */
function dupeq_fixed_l1(fTT,finvTT,gTT,ginvTT,fixX,fixY)
	F := Universe(fTT);

	L1 := AssociativeArray();
	L2 := AssociativeArray();

	L1[Zero(F)] := Zero(F);
	L1[fixX] := fixY;
	L1[-fixX] := -fixY;

	L2[Zero(F)] := Zero(F);

	success, L1, L2 :=  process(fTT,gTT,finvTT,ginvTT,L1,L2,[]);
	if success then
		for x in F do
			assert L1[fTT[L2[x]]] eq gTT[x];
		end for;

		assert L1[fixX] eq fixY;
	end if;

	return success, L1, L2;
end function;

/* Fixes L2(fixX) to fixY, and tries to find a pair (L1, L2)
 * satisfying this condition
 */
function dupeq_fixed_l2(fTT,finvTT,gTT,ginvTT,fixX,fixY)
	F := Universe(fTT);

	L1 := AssociativeArray();
	L2 := AssociativeArray();

	L1[Zero(F)] := Zero(F);
	L2[Zero(F)] := Zero(F);

	success, L1, L2 := process_fix_l2(fTT,gTT,finvTT,ginvTT,L1,L2,[],fixX,fixY);
	if success then
		for x in F do
			assert L1[fTT[L2[x]]] eq gTT[x];
		end for;

		assert L2[fixX] eq fixY;
	end if;

	return success, L1, L2;
end function;

function trivialPartition(f)
	F := BaseRing(Parent(f));
	n := Degree(F);
	p := Characteristic(F);

	coeff := {c : c in Coefficients(f)};

	subfields := {sub<F|d> : d in Divisors(n)};
	for s in subfields do
		if coeff subset s then
			d := Degree(s);
			m := n div d;

			break;
		end if;
	end for;

	elements := {x:x in F|not IsZero(x)};
	orbits := {};

	while #elements gt 0 do
		x := Rep(elements);
		orbit := {c*x^(3^(d*i)) : c in {1,2}, i in [0..m-1]};

		elements diff:= orbit;
		Include(~orbits, orbit);
	end while;

	return orbits;
end function;

closeOrbitsByL2 := function(orbits, L2, orbit_idx)
	to_close_idx := 1;

	/* If it is equal there is only one orbit left to close */
	while to_close_idx lt #orbits do
		orbit := orbits[to_close_idx];
		xs_to_examine := orbit;

		/* We might have merged all the orbits left to close, so check */
		while #xs_to_examine gt 0 and to_close_idx lt #orbits do
			x := xs_to_examine[1];
			xs_to_examine := xs_to_examine[2..#xs_to_examine];

			lx := L2[x];

			if lx in orbit then
				continue;
			end if;

			out_o := {};
			for o in orbits[(to_close_idx+1)..#orbits] do
				if lx in o then
					out_o := o;
					break;
				end if;
			end for;

			/* Keep track of the orbit before which we have checked there is no mapping with the current orbit.
			 * If we are removing a orbit before, then we need to reduce the index by one.
			 * If we are joining it, then then next one becomes the target (no action needed).
			 * If we are removing one after it, then no action is needed.
			 */
			merging_idx := Index(orbits, out_o);
			if merging_idx lt orbit_idx then
				orbit_idx -:= 1;
			end if;

			xs_to_examine cat:= out_o;
			orbit cat:= out_o;

			orbits[to_close_idx] := orbit;
			Remove(~orbits, merging_idx);
		end while;

		// At this point we tried merging this orbit and all the
		// orbits merged with it with all other orbits.
		to_close_idx +:= 1;
	end while;

	return orbits, orbit_idx;
end function;

partitionByL2 := function(f)
	F := BaseRing(Parent(f));

	raw_orbits := [[o : o in orbit] : orbit in trivialPartition(f)];

	orbits := [];

	fTT := AssociativeArray();
	finvTT := AssociativeArray();

	for x in F do
		fy := Evaluate(f,x);
		fTT[x] := fy;
		finvTT[fy] := Min({x,-x});
	end for;

	while #raw_orbits gt 0 do
		e := raw_orbits[1][1];

		target_index := 2;
		while target_index le #raw_orbits do
			success, l1, l2 := dupeq_fixed_l2(fTT, finvTT, fTT, finvTT, e, raw_orbits[target_index][1]);
			target_index +:= 1;

			if success then
				raw_orbits, target_index := closeOrbitsByL2(raw_orbits, l2, target_index);
			end if;
		end while;

		// We checked that raw_orbits[1] does not map to anything else.
		Append(~orbits, raw_orbits[1]);
		raw_orbits := raw_orbits[2..#raw_orbits];
	end while;

	return {{e : e in orbit} : orbit in orbits};
end function;

/* Given a list of representatives from each orbit of L2 w.r.t, checks equivalence */
function dupeq_with_l2_representatives(f, g, f_representatives)
	F := BaseRing(Parent(f));

	fTT := AssociativeArray();
	gTT := AssociativeArray();
	finvTT := AssociativeArray();
	ginvTT := AssociativeArray();
	for x in F do
		fy := Evaluate(f,x);
		gy := Evaluate(g,x);
		fTT[x] := fy;
		gTT[x] := gy;
		finvTT[fy] := Min({x,-x});
		ginvTT[gy] := Min({x,-x});
	end for;

	/* Attempt to assign L2(1) = r for each representative and see if something works */
	for r in f_representatives do
		tf, l1, l2 := dupeq_fixed_l2(fTT,finvTT,gTT,ginvTT,One(F),r);
		if tf then
			return tf, l1, l2;
		end if;
	end for;
	return false, [], [];
end function;

/* The monomial option specifies whether we can fix L2(1) = 1, which should be true
   whenever one of the tested functions is a monomial (and, more general, whenenver
   the automorphism group of one of the functions contains permutations mapping any
   non-zero element to 1.
*/
function dupeq(f,g:monomial := false)
	F := BaseRing(Parent(f));

	fTT := AssociativeArray();
	gTT := AssociativeArray();
	finvTT := AssociativeArray();
	ginvTT := AssociativeArray();
	for x in F do
		fy := Evaluate(f,x);
		gy := Evaluate(g,x);
		fTT[x] := fy;
		gTT[x] := gy;
		finvTT[fy] := Min({x,-x});
		ginvTT[gy] := Min({x,-x});
	end for;

	L1 := AssociativeArray();
	L2 := AssociativeArray();
	L1[Zero(F)] := Zero(F);
	L2[Zero(F)] := Zero(F);

	return process(fTT,gTT,finvTT,ginvTT,L1,L2,[],monomial);
end function;

