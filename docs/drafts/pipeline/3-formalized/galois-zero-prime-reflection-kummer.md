# Prime reflection radicals and the global lifting obstruction

- **ID:** galois-zero-prime-reflection-kummer
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Questions:** Infinite arithmetic sign kernel; field lift of functional reflection.

## Target

Inside the prime spectral extension `E/B`, let `H` be the compositum of all
reflection-pair residue fields. For every prime and actual zero put

`U_(p,ρ)=p^ρ+p^(1−ρ)`,
`d_(p,ρ)=p^ρ−p^(1−ρ)`,
`D_(p,ρ)=U_(p,ρ)²−4p`.

Prove `H/B` normal and `E=H(d_(p,ρ))`, with `d²=D∈H`. Index the nonzero
radicals. The complete kernel `Gal(E/H)` identifies with the sign
families respecting every finite square-class relation among the `D`.
This is an infinite classification, not a finite-height approximation.

The uniform negative sign gives a concrete lifting criterion: functional
reflection extends to a `B`-automorphism of `E` exactly when every finite
product of nonzero `D` that is square in `H` has an even number of factors.
Such a lift is unique, central, nonidentity and involutive. Its equality with
ordinary conjugation is exactly the purity question. Restriction gives the
continuous exact sequence `1→Gal(E/H)→Gal(E/B)→Gal(H/B)→1`; the kernel is
abelian of exponent two and its sign classification preserves Krull topology.

Conjugation acts on the sign group by conjugating zero labels. It centralizes
the entire orientation kernel exactly when `D_i D_conjugate(i)` is square in
`H` for every nonzero radical. This locates its action on the kernel without
asserting that it belongs to the kernel or is central in the whole group.

## Paper mechanism

Arithmetic automorphisms transport each pair field to the pair field of the
image zero, so their full compositum is invariant. The identities
`d²=U²−4p` and `p^ρ=(U+d)/2` give the full radical presentation; zero radicals
already give elements of `H`. Infinite Galois/Kummer duality classifies
simultaneous signs by all finite square-class relations.

For two primes at one zero, the product of their reflection differences is
fixed by its pair stabilizer, hence belongs to its pair field. Consequently
their discriminants have the same square class whenever both are nonzero.
This is independent of prime choice; different pairs can remain coupled.

Uniform negation sends every prime value at `ρ` to its value at `1−ρ`.
Conversely a functional-reflection lift has precisely this sign action.
The faithful zero action and commutation of all arithmetic zero maps with
functional reflection give uniqueness and centrality.

Normality of `H/B` makes `τ↦cτc` an action on `Gal(E/H)`. Its sign at `i` is
τ's sign at the conjugate index. Infinite Kummer duality says that two such
sign characters agree exactly when the product of their radicands is square
in `H`; this gives the kernel-centralization criterion.

## Existing ingredients

- `ThePrimeResidueFieldsOfTheZeros`: pair fields, exact fixing subgroups,
  reflection commutation, quadratic equations, full prime generation.
- `TheKummerRelationsOfTheZeroWidths.radicalSignAction_unique_extension`:
  generic infinite Kummer criterion. Its field, generation and nonvanishing
  premises must all be proved for these concrete prime radicals.

## Boundary

The parity condition is not established. No lift, realness of `H`, centrality
of ordinary conjugation, or identification with the earlier contour fields
is assumed. Paper proof and Lean formalization are complete.

## Lean declarations

`ThePrimeReflectionKernelOfTheZeros.lean`:

- `primeReflectionField_normal`, `primeReflectionRestriction_surjective`,
  `primeReflectionRestriction_ker`, `primeReflectionKernelEmbedding_range`:
  the exact arithmetic quotient and its full kernel.
- `primeReflectionRadicals_adjoin_top`, `primeReflectionDifference_sq`:
  the complete radical presentation and explicit discriminants.
- `primeReflectionSignAction_unique_extension`, `primeReflectionSignEquiv`,
  `primeReflectionSignHomeomorph`: all compatible signs are realized uniquely,
  with the complete Krull topology.
- `primeReflectionKernel_comm`, `primeReflectionKernel_square`: the kernel
  is abelian of exponent two.
- `primeReflectionRadicands_same_zero_square`: prime-choice independence.
- `primeFunctionalReflection_unique_lift_iff`,
  `primeFunctionalReflection_central`, `primeFunctionalReflection_ne_one`,
  `primeFunctionalReflection_square`: exact parity obstruction and the lift's properties.
- `primeReflectionSignAction_conjugate`,
  `primeConjugation_centralizes_kernel_iff`: conjugation's exact kernel action
  and its square-class obstruction.
- `primeReflectionRestriction_conjugation_iff`,
  `primeFunctionalReflection_eq_conjugation_iff`: the separate purity boundary.

Repository-source compilation passed with `lake --old env lean`. All 33
transitive axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
