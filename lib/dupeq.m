/*
 * Nikolay's brilliant way of classifying functions up tp equivalence.
 */

/* A modified version of the duplicate equivalence test for reconstructing the automorphism group
 * of a given function. More specifically, we want to partition the non-zero elements of FF into
 * "orbits" so that if X and Y belong to the same orbit, then there is a permutation pair (L1,L2)
 * with L1 * F * L2 = F and L1(X) = Y. Note that if L1 * F * L2 = F, then L1^(-1) * F * L2^(-1) = F
 * as well, so this realation is symmetric and gives a correctly defined equivalence relation.
 */

/* Finds the linear span of the given set of elements */
function span(Els)
	FF := Parent(Els[1]);
	p := Characteristic(FF);

	vecs := [ Vector(GF(p), Eltseq(e)) : e in Els ];
	M := Matrix(vecs);
	return { SequenceToElement( Eltseq(v), FF ) : v in RowSpace(M) };
end function;

/* The state is represented by a triple (L1, L2, P) where L1 and L2 are partial truth tables
   for l1 and l2, and P is a set of pairs of the form <x,y> meaning that {+- x} maps to {+- y}
   but we do not know the exact signs.
*/

forward derivel2;

/* Given a list of newly set values for L1, derives all values of L1 that can be
 * obtained from them and the currently known values. Returns:
 * - a Boolean value indicating whether a contradiction has been encountered;
 * - the newly derived pairs for L1;
 * - the new TT for L1;
 * - the new TT for L2;
 *   The new values are given as a sequence of inputs, e.g. newValues = [ a, b, c ]
 *   means that we now know L2[a], L2[b], and L2[c], which we did not know before.
 */
function derivel1(f,g,finv,ginv,L1,L2,P,newValues)
	newP := [];

	p := Characteristic(Parent(Random(L1)));
	primeField := [ x : x in GF(p) | x ne 0 ];

	/* To derive new values, we combine all known values of L1 with the new ones
	 * using linear combinations.
	 */
	for v in newValues do
		for x in Keys(L1) do
			for c1 in primeField do
				for c2 in primeField do
					newX := c1*x + c2*v;
					newY := c1*L1[x] + c2*L1[v];
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
						 *   not one of newY or -neweY
						 */
						if IsDefined(finv, newX) then
							if not IsDefined(ginv,newY) then
								/* This has been confirmed to cut off unnecessary branches */
								return false, [], [], [];
							end if;
							L2x := ginv[newY];
							L2y := finv[newX];

							if IsDefined(L2,L2x) then
								if not L2[L2x] in { L2y, -L2y } then
									return false, [], [], [];
								end if;
							end if;

							if IsDefined(L2,-L2x) then
								if not L2[-L2x] in { L2y, -L2y } then
									return false, [], [], [];
								end if;
							end if;

							if not IsDefined(L2,L2x) then
								/* Now we know that { -x, +x } maps to { -y, +y } via L2,
								 * but we do not know how, so we add it to the list of
								 * pairs that need to be resolved
								 */
								Append(~newP, <L2x, L2y>);
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

	return true, L1, L2, P cat newP;
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
	newL1 := [];

	p := Characteristic(Parent(Random(L1)));
	primeField := [ x : x in GF(p) | x ne 0 ];

	/* To derive new values, we combine all known values of L2 with the new ones
	 * using linear combinations.
	 */

	for v in newValues do
		for x in Keys(L2) do
			for c1 in primeField do
				for c2 in primeField do
					newX := c1*x + c2*v;
					newY := c1*L2[x] + c2*L2[v];

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

						newL1x := f[L2[newX]];
						newL1y := g[newX];

						/* Possible contradiction for L1 */
						if IsDefined(L1,newL1x) and L1[newL1x] ne newL1y then
							/* This has been confirmed to cut off unnecessary branches */
							return false, [], [], [], [];
						else
							L1[newL1x] := newL1y;
							Append(~newL1, newL1x);
						end if;
					end if;
				end for;
			end for;
		end for;
	end for;

	/* If we have derived new values for L1, we now call the companion function for L1
	 * to derive all possible values. If we encounter contradiction, we fail altogether.
	 */
	hope, L1, L2, P := derivel1(f,g,finv,ginv,L1,L2,P,newL1);

	return hope, L1, L2, P;
end function;

function firstFreel2(TT)
	FF := Parent(Random(TT));
	B := Basis(FF);
	for i in [1..#B] do
		if not IsDefined(TT,B[i]) then
			return B[i];
		end if;
	end for;
	return FF ! 0;
end function;

function domainl2(f,g,L1,L2,P,b)
	/* The possible values of l2 at b are those that lie outside of the linear subspace
	 * spanned by the outputs of the assigned values
	 */

	/* Since b should be the first element in the basis of the finite field that
	 * has not been assigned a value, we simply take the images of all preceding
	 * basis elements and generate the spanned subspace.
	 */
	basis_elements := [];
	FF := Parent(Random(L1));
	B := Basis(FF);
	i := 1;
	while B[i] ne b do
		Append(~basis_elements,B[i]);
		i +:= 1;
	end while;
	if #basis_elements eq 0 then
		return [ x : x in FF | x ne 0 ];
	else
		return [ x : x in FF | not x in span(basis_elements) ];
	end if;
end function;

/* Note that f and g should be given as TT's (associative arrays), and finv and ginv should
 * be partially filled TT's, with the inverse of any element being one of its two preimages
 */
function process(f,g,finv,ginv,L1,L2,P,monomial)
	FF := Parent(Random(L1));

	if #Keys(L1) eq #FF and #Keys(L2) eq #Keys(L1) then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* If we are here, we assume that all linear combinations for L1 and L2
	   have already been derived. We thus need to either:
	   1) Process more pairs from P, or
	   2) Guess a new value of e.g. L2 if no pairs remain to be processed
	*/

	if #P ne 0 then
		x := P[1][1];
		y := P[1][2];
		/* We know that { -x, +x } will map to { -y, +y }, but we guess
		   which of two possibilities will take place
		*/

		L2[-x] := -y;
		L2[x] := y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ x ]);

		if hope then
			success, l1, l2 := process(f,g,finv,ginv,newL1,newL2,newP,monomial);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */

		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ -x, x ]);
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
	b := firstFreel2(L2);

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq 0 then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if monomial and b eq 1 then
		D := [ FF ! 1 ];
	else
		D := domainl2(f,g,L1,L2,P,b);
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

function process(f,g,finv,ginv,L1,L2,P,monomial)
	FF := Parent(Random(L1));

	if #Keys(L1) eq #FF and #Keys(L2) eq #Keys(L1) then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* If we are here, we assume that all linear combinations for L1 and L2
	   have already been derived. We thus need to either:
	   1) Process more pairs from P, or
	   2) Guess a new value of e.g. L2 if no pairs remain to be processed
	*/

	if #P ne 0 then
		x := P[1][1];
		y := P[1][2];
		/* We know that { -x, +x } will map to { -y, +y }, but we guess
		   which of two possibilities will take place
		*/

		L2[-x] := -y;
		L2[x] := y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ x ]);

		if hope then
			success, l1, l2 := process(f,g,finv,ginv,newL1,newL2,newP,monomial);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */

		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ -x, x ]);
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
	b := firstFreel2(L2);

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq 0 then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if monomial and b eq 1 then
		D := [ FF ! 1 ];
	else
		D := domainl2(f,g,L1,L2,P,b);
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

function process_fix_l2(f,g,finv,ginv,L1,L2,P,fixX,fixY)
	FF := Parent(Random(L1));

	if #Keys(L1) eq #FF and #Keys(L2) eq #Keys(L1) then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* If we are here, we assume that all linear combinations for L1 and L2
	   have already been derived. We thus need to either:
	   1) Process more pairs from P, or
	   2) Guess a new value of e.g. L2 if no pairs remain to be processed
	*/

	if #P ne 0 then
		x := P[1][1];
		y := P[1][2];
		/* We know that { -x, +x } will map to { -y, +y }, but we guess
		   which of two possibilities will take place
		*/

		L2[-x] := -y;
		L2[x] := y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ x ]);

		if hope then
			success, l1, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */

		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ -x, x ]);
		if hope then
			success, l1, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l1, l2;
			end if;
		end if;

		/* If both options lead to contradictions, we are already in the soup */

		return false, [], [];
	end if;

	/* If there are no pairs to process, we guess a value of L2 instead */

	/* Get the first free element of L2 (whose value we will guess) */
	b := firstFreel2(L2);

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq 0 then
		l1 := Interpolation([ x : x in FF ], [ L1[x] : x in FF ]);
		l2 := Interpolation([ x : x in FF ], [ L2[x] : x in FF ]);
		return true, l1, l2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if b eq fixX then
		D := [ FF ! fixY ];
	else
		D := domainl2(f,g,L1,L2,P,b);
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
function dupeq_fixed_l1(f,g,fixX,fixY)
	FF := BaseRing(Parent(f));
	fTT := AssociativeArray();
	gTT := AssociativeArray();
	finvTT := AssociativeArray();
	ginvTT := AssociativeArray();
	for x in FF do
		fy := Evaluate(f,x);
		gy := Evaluate(g,x);
		fTT[x] := fy;
		gTT[x] := gy;
		finvTT[fy] := Min({x,-x});
		ginvTT[gy] := Min({x,-x});
	end for;

	L1 := AssociativeArray();
	L2 := AssociativeArray();
	L1[FF ! 0] := FF ! 0;
	L2[FF ! 0] := FF ! 0;
	L1[fixX] := fixY;

	return process(fTT,gTT,finvTT,ginvTT,L1,L2,[],false);
end function;

/* Fixes L2(fixX) to fixY, and tries to find a pair (L1, L2)
 * satisfying this condition
 */
function dupeq_fixed_l2(f,g,fixX,fixY)
	FF := BaseRing(Parent(f));
	fTT := AssociativeArray();
	gTT := AssociativeArray();
	finvTT := AssociativeArray();
	ginvTT := AssociativeArray();
	for x in FF do
		fy := Evaluate(f,x);
		gy := Evaluate(g,x);
		fTT[x] := fy;
		gTT[x] := gy;
		finvTT[fy] := Min({x,-x});
		ginvTT[gy] := Min({x,-x});
	end for;

	L1 := AssociativeArray();
	L2 := AssociativeArray();
	L1[FF ! 0] := FF ! 0;
	L2[FF ! 0] := FF ! 0;
	L2[fixX] := fixY;

	return process_fix_l2(fTT,gTT,finvTT,ginvTT,L1,L2,[],fixX,fixY);
end function;

/* Partitions the non-zero elements of the finite field into orbits w.r.t. L2, as described above */
function partitionByL2(f)
	FF := BaseRing(Parent(f));
	remaining := { x : x in FF | x ne 0 };
	orbits := [];
	L2s := [];
	while #remaining gt 0 do
		e := Random(remaining);
		orbit := { e };
		for target in remaining do
			if target in orbit then
				continue;
			end if;
			doesEmapToTarget, l1, l2 := dupeq_fixed_l2(f,f,e,target);
			if doesEmapToTarget then
				Append(~L2s,l2);
				newElements := { e, target };
				countBefore := 0;
				while #newElements gt countBefore do
					newElements join:= { Evaluate(l2, x) : x in newElements, l2 in L2s };
					countBefore := #newElements;
				end while;
				orbit join:= newElements;
			end if;
		end for;
		Append(~orbits, orbit);
		remaining diff:= orbit;
	end while;

	return orbits;
end function;

/* Given a list of representatives from each orbit of L2, checks equivalence */
function dupeq_with_l2_representatives(f,g,representatives)
	/* Attempt to assign L2(1) = r for each representative and see if something works */
	for r in representatives do
		tf, l1, l2 := dupeq_fixed_l2(f,g,1,r);
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
	FF := BaseRing(Parent(f));
	fTT := AssociativeArray();
	gTT := AssociativeArray();
	finvTT := AssociativeArray();
	ginvTT := AssociativeArray();
	for x in FF do
		fy := Evaluate(f,x);
		gy := Evaluate(g,x);
		fTT[x] := fy;
		gTT[x] := gy;
		finvTT[fy] := Min({x,-x});
		ginvTT[gy] := Min({x,-x});
	end for;

	L1 := AssociativeArray();
	L2 := AssociativeArray();
	L1[FF ! 0] := FF ! 0;
	L2[FF ! 0] := FF ! 0;

	return process(fTT,gTT,finvTT,ginvTT,L1,L2,[],monomial);
end function;

function LinInqeuivalentToF(f, List)
    LinInequiv := [];

    if #List eq 0 then
	    return [f];
    end if;

    orbits := partitionByL2(f);
    orbits := [Rep(o) : o in orbits];

    for g in List do
        if not dupeq_with_l2_representatives(f,g,orbits) then
            Append(~LinInequiv, g);
        end if;
    end for;

    return LinInequiv;
end function;
