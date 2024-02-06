load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/dupeq.m";

/* Partition a list of functions through the specified invariant */
ComputePartitionUsingInvariant := function(FunctionList, InvariantFunction)
    InvPartition := AssociativeArray();

    for f in FunctionList do
        k := InvariantFunction(f);

        if not k in Keys(InvPartition) then
            InvPartition[k] := [];
        end if;

        Append(~InvPartition[k], f);
    end for;

    return InvPartition;
end function;

/* Partition a list using an equivalence relation.
 * Expects a procedure that takes a function and a list of functions,
 * and returns a sublist of functions inequivalent to the first.
 */
ComputePartitionUsingEquivalence := function(FunctionList, InequivalentToFunction)
    Partition := [];

    while #FunctionList ne 0 do
        f := FunctionList[1];
        Append(~Partition, f);

        FunctionList := InequivalentToFunction(f, FunctionList[2..#FunctionList]);
    end while;

    return Partition;
end function;

/* BEGIN of user modifiable section */

// Example clasify one or more of the expansions
// Defines
//
// p; n; F<a> := GF(p^n); R<x> := PolynomialRing(F);
load "./expansions/test.m";

/* First partition using the nuclei invariant */
S, sizes := PrecomputeSubfields(F);

compute_nuclei_invariants := function(f)
    return Nuclei(f, One(F), S, sizes);
end function;

part_nuclei := ComputePartitionUsingInvariant(Functions, compute_nuclei_invariants);

// remove x^2
Remove(~part_nuclei, [p^n,p^n]);
// remove albert since the automorphisms are stupid long to compute. But keep it for the classification because we don't know if they have other classes
albert := part_nuclei[[p^2,p^2]];
Remove(~part_nuclei, [p^2, p^2]);

[<k,v> : k->v in part_nuclei];

part_nuclei := [v : k->v in part_nuclei];


part_nuclei_code := [];

for partition in part_nuclei do
    part_code := ComputePartitionUsingInvariant(partition, AutomoriphismGroupOrderFromFunction);

    part_nuclei_code cat:=[v : k->v in part_code];
end for;

Append(~part_nuclei_code, albert);
part_nuclei_code;
classes := [];

for p in part_nuclei_code do
    new_classes := ComputePartitionUsingEquivalence(p, LinInqeuivalentToF);

    classes cat:= new_classes;
end for;

classes;

/* END of user modifiable section */
