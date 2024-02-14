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

/* Finds the linear span of the given set of elements */
function span(Els)
	F := Parent(Els[1]);
	p := Characteristic(F);
	n := Degree(F);
	return { SequenceToElement( Eltseq(v), F) : v in sub<VectorSpace(GF(p),n)|[ Vector(Eltseq(e)) : e in Els ]> };
end function;

function firstFreel2(TT)
	F := Universe(TT);
	B := Basis(F);

	for i in [1..#B] do
		if not IsDefined(TT,B[i]) then
			return B[i];
		end if;
	end for;

	return Zero(F);
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

	F := Parent(b);
	p := Characteristic(F);
	n := Degree(F);

	B := Basis(F);


	basis := B[1..Index(B,b)-1];

	if #basis eq 0 then
		return [ x : x in F | x ne 0 ];
	else
		span_bi := { SequenceToElement( Eltseq(v), F) : v in sub<VectorSpace(GF(p),n)|[ Vector(Eltseq(e)) : e in basis ]> };
		return [ x : x in F | not x in span_bi ];
	end if;
end function;

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

	p := Characteristic(Universe(f));
	primeField := [ x : x in GF(p) | x ne 0 ];

	/* To derive new values, we combine all known values of L1 with the new ones
	 * using linear combinations.
	 */
	for x in Keys(L1) do	
		for c1 in primeField do
			newX1 := c1*x;
			newY1 := c1*L1[x];

			for v in newValues do
				for c2 in primeField do
					newX := newX1 + c2*v;
					newY := newY1 + c2*L1[v];

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

	p := Characteristic(Universe(f));
	primeField := [ x : x in GF(p) | x ne 0 ];

	/* To derive new values, we combine all known values of L2 with the new ones
	 * using linear combinations.
	 */

	for x in Keys(L2) do
		for c1 in primeField do
			newX1 := c1*x;
			newY1 := c1*L2[x];

			for v in newValues do
				for c2 in primeField do
					newX := newX1 + c2*v;
					newY := newY1 + c2*L2[v];

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
	return derivel1(f,g,finv,ginv,L1,L2,P,newL1);
end function;

function process_fix_l2(f,g,finv,ginv,L1,L2,P,fixX,fixY)
	if #Keys(L1) eq #Universe(f) and #Keys(L2) eq #Keys(L1) then
		return true, L2;
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
			success, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l2;
			end if;
		end if;

		/* If the first guess leads to a contradiction, do the second option */

		L2[-x] := y;
		L2[x] := -y;

		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P[2..#P], [ -x, x ]);
		if hope then
			success, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l2;
			end if;
		end if;

		/* If both options lead to contradictions, we are already in the soup */

		return false, [];
	end if;

	/* If there are no pairs to process, we guess a value of L2 instead */

	/* Get the first free element of L2 (whose value we will guess) */
	b := firstFreel2(L2);

	/* If all basis elements have been evaluated, firstFreel2() will return 0;
	 * in this case, we have completely reconstructed L2, and return.
	 */
	if b eq 0 then
		return true, L2;
	end if;

	/* Get a list of the possible values that can be assigned to L2 */
	if b eq fixX then
		D := [fixY];
	else
		D := domainl2(f,g,L1,L2,P,b);
	end if;

	for v in D do
		L2[b] := v;
		hope, newL1, newL2, newP := derivel2(f,g,finv,ginv,L1,L2,P,[b]);

		if hope then
			success, l2 := process_fix_l2(f,g,finv,ginv,newL1,newL2,newP,fixX,fixY);
			if success then
				return true, l2;
			end if;
		end if;
	end for;

	return false, [];
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
	L2[fixX] := fixY;
	L2[-fixX] := -fixY;

	return process_fix_l2(fTT,gTT,finvTT,ginvTT,L1,L2,[],fixX,fixY);
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
		orbit := { c*x^(3^(d*i)) : c in {1,2}, i in [0..m-1] };

		elements diff:= orbit;
		Include(~orbits, orbit);
	end while;

	return orbits;
end function;

/* Partitions the non-zero elements of the finite field into orbits w.r.t. L2, as described above */
function partitionByL2(f)
	F := BaseRing(Parent(f));
	K := GF(Characteristic(F));
	n := Degree(F);

	remaining := {x : x in F | x ne 0};
	orbits := [];
	L2s := [];

	fTT := AssociativeArray();
	finvTT := AssociativeArray();

	for x in F do
		fy := Evaluate(f,x);
		fTT[x] := fy;
		finvTT[fy] := Min({x,-x});
	end for;

	remaining := trivialPartition(f);

	while #remaining gt 0 do
		#remaining;

		base_orbit := Rep(remaining);
		orbit := base_orbit;
		Exclude(~remaining, orbit);

		e := Rep(base_orbit);

		// Take advantage of known L2s
		old_orbit_size := 0;
		while #orbit gt old_orbit_size do
			old_orbit_size := #orbit;
		
			for x in orbit do
				for l in L2s do
					lx := l[x];
					if not lx in orbit then
						out_new_orbit := {};
						for new_orbit in remaining do
							if lx in new_orbit then
								orbit join:= new_orbit;
								out_new_orbit := new_orbit;
								break;
							end if;
						end for;

						// print "pre";
						// out_new_orbit;
						Exclude(~remaining, out_new_orbit);
					end if;
				end for;
			end for;
		end while;

		next_remaining := {};
		while #remaining gt 0 do
			target_orbit := Rep(remaining);
			Exclude(~remaining, target_orbit);
			
			success, l2 := dupeq_fixed_l2(fTT, finvTT, fTT, finvTT, e, Rep(target_orbit));

			if not success then
				Include(~next_remaining, target_orbit);
				continue;
			end if;

			// We found a new element in the orbit
			Append(~L2s,l2);

			orbit join:= target_orbit;
			
			old_orbit_size := 0;
			while #orbit gt old_orbit_size do
				old_orbit_size := #orbit;

				for x in orbit do
					for l in L2s do
						lx := l[x];
						if not lx in orbit then
							out_new_orbit := {};
							for new_orbit in remaining do
								if lx in new_orbit then
									orbit join:= new_orbit;
									out_new_orbit := new_orbit;
									break;
								end if;
							end for;

							// print "main";
							// out_new_orbit;
							Exclude(~remaining, out_new_orbit);
						end if;
					end for;
				end for;
			end while;
		end while;

		Append(~orbits, orbit);
		remaining := next_remaining;

		// for target_orbit in remaining do
		// 	if target_orbit in to_remove then
		// 		continue;
		// 	end if;

		// 	target := Rep(target_orbit);

		// 	doesEmapToTarget, l2 := dupeq_fixed_l2(fTT, finvTT, fTT, finvTT, e, target);
			
		// 	if doesEmapToTarget then
		// 		Append(~L2s,l2);
				
		// 		newElements := target_orbit;
		// 		Include(~to_remove, target_orbit);

		// 		countBefore := 0;
		// 		while #newElements gt countBefore do
		// 			countBefore := #newElements;
				
		// 			for x in newElements do
		// 				for l in L2s do
		// 					lx := l[x];
		// 					if not lx in newElements then
		// 						out_new_orbit := {};
		// 						for new_orbit in remaining do
		// 							if lx in new_orbit then
		// 								newElements join:= new_orbit;
		// 								out_new_orbit := new_orbit;
		// 								break;
		// 							end if;
		// 						end for;

		// 						print "main";
		// 						out_new_orbit;
		// 						Include(~to_remove, out_new_orbit);
		// 					end if;
		// 				end for;
		// 			end for;
		// 		end while;

		// 		orbit join:= newElements;
		// 	end if;
		// end for;

		// Append(~orbits, orbit);
		// remaining diff:= to_remove;
	end while;

	return orbits;
end function;

