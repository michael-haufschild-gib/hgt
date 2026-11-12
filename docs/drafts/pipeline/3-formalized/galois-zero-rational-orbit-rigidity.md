# Rational weights and arithmetic orbit rigidity

- **ID:** galois-zero-rational-orbit-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Questions:** Integral zero relations; arithmetic invariance of the critical line; reflection obstructions.
- **Lean:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheRationalWeightsOfPrimeZeroOrbits.lean`

## Results

Write `B` for the complete mixed-prime trace field, `E` for its spectral
extension, and `Δ` for the integral span of actual zeros.

1. `Gal(E/B)` acts faithfully and additively on `Δ`, transporting every
   prime character. It fixes `Δ∩ℚ`; the rational prime spectral field lies in `B`.
2. Every actual zero with rational real part has exactly the arithmetic
   orbit `{ρ,conjugate(ρ)}`. Its real part is preserved.
3. Critical-line membership is invariant under every arithmetic
   automorphism, in both directions. An orbit meeting the line lies on it.
4. The reflection-pair field satisfies `H_ρ=B ⇔ Re ρ=1/2`. Its global
   compositum equals `B` exactly when all actual zeros are critical.
5. For rational real parts, functional reflection belongs to the arithmetic
   orbit exactly on the line. Off the line `F_ρ=H_ρ`; each nonzero reflection
   discriminant is square in the global pair field, giving a singleton odd
   square relation obstructing the global functional-reflection lift.
6. An off-line zero whose reflection belongs to its arithmetic orbit has
   irrational real part. Its algebraic prime-monomial relations contain no
   independent pair; one relation support contains all others. Two algebraic
   prime values at a reflection-conjugate zero force it onto the line.

## Proof

Automorphisms preserve products of prime values. Two-prime injectivity
therefore transports every integral zero relation. The unit weight is
fixed because its prime values are the primes themselves; clearing
denominators fixes rational weights. Infinite Galois fixed-field duality
places their prime values in `B`.

For rational `β=Re ρ`, the weight `q=ρ+conjugate(ρ)=2β` is fixed. Put
`ζ=σ⁻¹ρ`. Absolute-height preservation gives
`conjugate(ζ)=ζ∓(2ρ−q)`. Thus `σcσ⁻¹ρ` has horizontal displacement
`∓2(Re σρ−β)`. The bounded set of absolute displacements of the complete
arithmetic orbit is closed under doubling; its supremum forces it to be
`{0}`. Absolute-height preservation leaves exactly the conjugate pair.
The pair-field stabilizer and six-exponentials relation theorem give
the stated field and prime-monomial consequences.

## Main declarations

- `primeTraceExponentRepresentation_injective`
- `primeTraceExponentHom_rational`
- `rationalPrimeSpectralField_le_traceField`
- `primeTraceZeroMap_rational_orbit_iff`
- `primeTraceZeroMap_critical_iff`
- `primePairField_eq_bot_iff_critical`
- `primeReflectionField_eq_bot_iff_critical`
- `primeReflectionOrbit_rational_iff`
- `primeReflection_rational_offline_odd_square_relation`
- `primeReflectionOrbit_relations_dependent`
- `primeReflectionOrbit_two_algebraic_values_critical`

## Boundary

The action is internal to the full infinite extension. No extension to
ambient complex automorphisms, finite height truncation, or centrality of
conjugation is assumed. Rationality of all zero real parts, existence of a
global functional-reflection lift, and purity remain unproved.

Validation: direct Lean source check; 28 axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`.
