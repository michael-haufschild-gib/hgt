# Fixed-trace-ideal Gamma cofinal normalizer law — formalized

- **ID:** `fixed-trace-ideal-gamma-cofinal-normalizer-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `fixed-trace-ideal-gamma-cofinal-normalizer-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean
```

The first module supplies the carrier `PrimeTraceSequence`, the fixed summable ideal
`primeFirstTraceSummableIdeal`, the raw Gamma character `primeReflectedCharacterMultiplier`, the
Fisher twist `primeActivationOccupancyFisherTwist`, the fixed physical class
`primeFixedPhysicalFisherClass`, and the actual rational-adelic period-one Stokes landings; it is
certified by the sibling card `graded-variable-ideal-fixed-xi-comparison.md`.  The second module
carries every clause of this card.

## Formal theorem chain

```text
 1  primeReflectedCharacter_preservesFixedIdeal_of_nonneg      damping majorant, C_t(I) ⊆ I for 0 ≤ t
 2  primeReflectedCharacter_preservesFixedIdeal_iff            clause 1: C_t(I) ⊆ I ↔ 0 ≤ t, |t| < 1
 3  reflected_primeReflectedCharacter_preservesFixedIdeal_iff  clause 2: C_(-t)(I) ⊆ I ↔ t ≤ 0
 4  reflected_primeReflectedCharacter_normalizesFixedIdeal_iff clause 3: two-sided ↔ t = 0
 5  primeFiniteReflectedCharacterMultiplier                    finite-prime Gamma multiplier
 6  summable_primeFiniteReflectedCharacterMultiplier_sub       its defect from the identity is ℓ¹
 7  primeFiniteReflectedCharacterMultiplier_quotient_eq        clause 4: identity on S/I, every grade
 8  primeActivationOccupancyFisherFiniteTruncation_class_eq_zero  clause 5a: truncations are zero
 9  primeFixedPhysicalFisherClass_ne_zero_iff                  clause 5b: [F_t] ≠ 0 ↔ 0 ≤ t
10  primeFixedPhysicalFisher_reflected_pair_ne_zero            clause 6a: never the zero pair
11  primeFixedPhysicalFisher_reflected_pair_both_ne_zero_iff   clause 6b: both nonzero ↔ t = 0
12  primeFixedPhysicalFisher_reflected_pair_exactly_one_erased clause 6c: off centre, exactly one
13  primeGammaCofinalBockstein                                 beta_t = [F_(-t)] - [F_t]
14  primeGammaCofinalBockstein_ne_zero_iff                     clause 8a: beta_t ≠ 0 ↔ t ≠ 0
15  primeGammaCofinalBockstein_eq_zero_iff                     the contrapositive form
16  primeFiniteGammaBockstein_eq_zero                          clause 8b: every finite stage is zero
17  xi_reflected_primeReflectedCharacter_normalizesFixedIdeal_iff  two-sided at rho ↔ Re rho = 1/2
18  ccmRationalAdelicPrimeFixedXiStokesComparisons_class_one_orientation_ne_zero
                                                               clause 7a: unconditional survival
19  ccmRationalAdelicPrimeFixedXiStokesComparisons_class_exactly_one_erased
                                                               clause 7b: off line, one is erased
20  ccmRationalAdelicPrimeFixedXiGammaBockstein                 source-derived orientation defect
21  ccmRationalAdelicPrimeFixedXiGammaBockstein_eq             clause 9a: defect = j_rho • beta_(t_rho)
22  ccmRationalAdelicPrimeFixedXiGammaBockstein_ne_zero_iff     clause 9b: nonzero ↔ Re rho ≠ 1/2
23  ccmRationalAdelicPrimeFixedXiGammaBocksteinAnnihilates_iff_riemannHypothesis
                                                               clause 10: annihilation ↔ RH
24  xiPrimeReflectedCharacterNormalizesFixedIdeal_iff_riemannHypothesis
                                                               clause 7c: global two-sided ↔ RH
```

`RiemannHypothesis` is mathlib's `RiemannHypothesis`; the passage to the `xi` divisor is the
corpus theorem `rh_iff_xi_ne_zero_right`.  The leading-jet nonvanishing used in step 22 is
`iteratedDeriv_XiC_ne_zero_at_supportMultiplicity`, so no jet hypothesis is assumed.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean  -- clean
lake build GaloisForLFunctions.RHTower                                                        -- success
```

`#print axioms` on all 18 named declarations of the module reports exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration occurs.  The module is imported by `GaloisForLFunctions.RHTower`.
