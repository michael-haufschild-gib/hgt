# The maximal arithmetic quotient of the zero motive

- **ID:** galois-zero-arithmetic-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Algebraic Frobenius values; arithmetic quotients of the full zero motive.

## Theorem

Let `Δ⊆ℂ` be the full original integer zero group and `R=Δ∩ℚ`.
The character subgroups `H≤Δ` on which the exponential points at
three distinct prime times have algebraic values are exactly the
subgroups `H≤R`. Thus the quotient motive with character group
`R` is the maximal quotient supporting three algebraic prime-time points.
Its character group contains `ℤ` and has rational rank one; the entire
original zero motive cannot have three algebraic prime-time points.

Algebraic values refer to the canonical rational group-algebra form
`ℚ[H]`, or equivalently to values on its character basis. They do not mean
that every value of a complex-coefficient regular function is algebraic.

## Paper argument

For any `z∈ℂ`, if `z∉ℚ`, the numbers `1,z` are rationally independent.
The logarithms of three distinct primes are rationally independent.
The six-exponentials theorem therefore excludes simultaneous algebraicity
of all three prime exponentials `p^z`: the other row consists of the
rational primes themselves. Conversely, for rational `z=a/b`, the
exponential has a nonzero power equal to the rational number `p^a`, so it
is algebraic.

Applying this equivalence to every element of `H` gives exactly `H≤R`.
Restriction of complex characters from `Δ` to `R` is onto by divisibility
of `ℂˣ`, constructing the quotient on complex points. Every other allowed
restriction factors through this one. Functional-equation pairing gives
`1∈R`; any two nonzero elements of `R` are rationally proportional.
Every actual zero is nonreal, so its character lies outside `R`.
Moreover `R` is saturated: if `nz∈R` for a positive integer `n`, then
`z=(nz)/n∈ℚ`. Consequently `Δ/R` is torsion-free.

The quotient has exact character sequence
`1→Hom(Δ/R,ℂˣ)→Hom(Δ,ℂˣ)→Hom(R,ℂˣ)→1`.
Its kernel contains the injective real family
`u↦(z↦exp(u·Im z))`: every rational character exponent has imaginary part
zero, while any actual zero has nonzero imaginary part. Thus the arithmetic
quotient necessarily loses a full real family detecting zero ordinates.

## Boundary

The actual subgroup `Δ∩ℚ`, including its possible denominators, remains
undetermined. Finite type is not established. This classifies
algebraic prime-time values; it does not locate complex conjugation or
prove purity.

## Formalization

`GaloisForLFunctions/GaloisTheoryOfZeros/TheMaximalArithmeticQuotientOfTheZeroMotive.lean`:

- `three_prime_exponentials_algebraic_iff`.
- `threePrimeAlgebraic_iff_rational`, `allPrimeAlgebraic_iff_rational`.
- `rationalZeroOne_ne_zero`, `rationalZero_denominator`.
- `rationalZeroSubgroup_saturated`, `arithmeticRelationQuotient_torsionFree`.
- `arithmeticMotiveProjection_surjective`, `arithmeticMotiveProjection_kernel_iff`.
- `arithmeticMotiveProjection_universal`.
- `rawZeroRoot_not_rational`, `rationalZeroSubgroup_ne_top`.
- `arithmeticMotiveOrdinateKernel_trivial`, `arithmeticMotiveOrdinateKernel_injective`.

Final source check passed without warnings. All 19 transitive dependency
audits use only `propext`, `Classical.choice`, `Quot.sound`.
