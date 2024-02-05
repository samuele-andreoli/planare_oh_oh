load "lib/ccz_equivalence.m";
load "lib/semifields.m";
load "lib/dupeq.m";

/* Partition a list of functions through the specified invariant */
PartitionUsingInvariant := function(FunctionList, InvariantFunction)
    Partition := AssociativeArray();

    for f in FunctionList do
        k := InvariantFunction(f);

        if not k in Keys(Partition) then
            Partition[k] := [];
        end if;

        Append(~Partition[k], f);
    end for;

    return [v : k->v in Partition];
end function;

/* Partition a list using an equivalence relation. 
 * Expects a procedure that takes a function and a list of functions,
 * and returns a sublist of functions inequivalent to the first.
 */
PartitionUsingEquivalence := function(FunctionList, InequivalentToFunction)
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
load "./expansions/p3_n4_m4_l1_x2";

/* First partition using the nuclei invariant */
S := PrecomputeSubfields(F);

S;

compute_nuclei_invariants := function(f)
    return NucleiInvariants(f, S);
end function;

part_nuclei := PartitionUsingInvariant(Functions, compute_nuclei_invariants);

// part_nuclei := [Functions];

// part_nuclei_code := [];

// for p in part_nuclei do
//     part_code := PartitionUsingInvariant(p, AutomoriphismGroupOrderFromFunction);

//     part_nuclei_code cat:=part_code;
// end for;

classes := [];

// for p in part_nuclei_code do
//     new_classes := PartitionUsingEquivalence(p, CCZInequivalentToF);

//     classes cat:= new_classes;
// end for;

// classes;

// Example lin inequiv 
classes := [];

for p in part_nuclei do
    new_classes := PartitionUsingEquivalence(p, LinInqeuivalentToF);

    classes cat:= new_classes;
end for;

classes;

// Example classify families

/* END of user modifiable section */