# Unbounded formation-root charge and meromorphic-divisor selection law

- **ID:** ULF-DFPM-1-LC
- **Stage:** 3-formalized
- **Type:** LEAN-CERTIFIED SELECTION CORE
- **Status:** [UNCONDITIONAL] [NO RH PREMISE] [NO ADDED AXIOMS] [SOURCE ROOT GENESIS OPEN]

## Certified mechanism

Let `M` be a monoid, `charge : M -> Z`, and suppose

\[
 \operatorname{charge}(x^n)=n\operatorname{charge}(x).
\]

If one carrier `R` has `n`-th roots in `M` for natural numbers `n` of unbounded size, then

\[
 \operatorname{charge}(R)=0.
\]

For complex meromorphic carriers the charge is pointwise meromorphic order.  If that order is
finite and `R` has meromorphic roots at unbounded depths, its order is zero.  One global root
family meromorphic at every point therefore annihilates the complete finite divisor.

## Lean certificate

Module:

`GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection`

Certified declarations:

- `int_eq_zero_of_unbounded_natCast_dvd`;
- `charge_eq_zero_of_unbounded_formationRoots`;
- `meromorphicOrderAt_eq_zero_of_unbounded_roots`;
- `meromorphicDivisor_eq_zero_of_unbounded_roots`;
- `divisibleFormationSelection_capstone`.

Scratch elaboration and direct leaf elaboration pass.  Targeted build of only the leaf module
passes.  The leaf is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`; that umbrella
was not built.  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` where
needed.

## Exact boundary

This certificate proves selection from effective roots; it does not construct those roots.  Roots
created only after ramified base change do not satisfy the theorem's original-base premise.  The
remaining field problem is source-native, coherent root genesis and descent for the renormalized
formation transfer before divisor specialization.
