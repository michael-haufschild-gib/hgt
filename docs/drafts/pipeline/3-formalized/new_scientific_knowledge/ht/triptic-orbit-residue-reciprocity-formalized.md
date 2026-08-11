# Triptic orbit-residue reciprocity — formalized

- **ID:** `triptic-orbit-residue-reciprocity-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `triptic-orbit-residue-reciprocity.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/TripticGermConstraint.lean
formal/GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorLinearity.lean
formal/GaloisForLFunctions/HTGeometry/TripticBoundaryPoleClasses.lean
formal/GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorClassFunction.lean
formal/GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorFinsetSum.lean
formal/GaloisForLFunctions/HTGeometry/TripticOrbitResidueReciprocity.lean
formal/GaloisForLFunctions/HTGeometry/TripticSeparatedPrincipalPart.lean
formal/GaloisForLFunctions/HTGeometry/TripticGlobalCoefficient.lean
formal/GaloisForLFunctions/HTGeometry/TripticKernelNormalForm.lean
formal/GaloisForLFunctions/HTGeometry/TripticKernelIdentification.lean
formal/GaloisForLFunctions/HTGeometry/TripticKernelDifferentialAlgebraicity.lean
formal/GaloisForLFunctions/HTGeometry/TripticMultiplicativeKernel.lean
formal/GaloisForLFunctions/HTGeometry/EllipticGammaJetSourceDivisor.lean
formal/GaloisForLFunctions/HTGeometry/EllipticGammaSourceGermConstraint.lean
formal/GaloisForLFunctions/HTGeometry/EllipticGammaConePresentationBridge.lean
formal/GaloisForLFunctions/HTGeometry/TripticGammaCorrectionBasis.lean
formal/GaloisForLFunctions/HTGeometry/TripticGammaCorrection.lean
formal/GaloisForLFunctions/HTGeometry/TripticNormalForm.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicRealizationDerivative.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicRealizationAlgebra.lean
formal/GaloisForLFunctions/HTGeometry/EllipticGammaJetRealization.lean
formal/GaloisForLFunctions/HTGeometry/TripticJetRowFreeness.lean
formal/GaloisForLFunctions/HTGeometry/TripticJetCombinationHypertranscendence.lean
formal/GaloisForLFunctions/HTGeometry/TripticCompleteness.lean
```

## The class `Q`, as the card defines it

`Q = {F ∈ Mer(ℂ) : Δ₁F = 0 and Δ_τΔ_σF ∈ ℂ}` is an identity in `Mer(ℂ)`, not a pointwise identity:
a representative of a function with poles cannot satisfy it at a pole, where one side has a finite
artefact value and the identity demands the cancellation of an infinity.  The Lean class is therefore

```text
PeriodicOneGerm F        ∀ z, ∀ᶠ w in 𝓝[≠] z, F (w+1) = F w
MixedConstGerm F τ σ C   ∀ z, ∀ᶠ w in 𝓝[≠] z, F(w+τ+σ) - F(w+τ) - F(w+σ) + F w = C
```

and the elliptic gamma source is a member of it (`mixedConstGerm_ellipticGammaSource`), which is what
the completeness theorem needs.

## Formal theorem chain

```text
 1  additiveOrbitalDivisorAt                     the labelled orbital principal-part divisor
 2  triptic_orbit_residue_reciprocity            R_τ(F) = R_σ(F)                        [reciprocity]
 3  triptic_multiplicative_divisor_reciprocity   its multiplicative form
 4  exists_finset_boundaryPoleClasses            finitely many boundary pole classes
 5  exists_orderBound_boundary                   orders bounded below
 6  additiveOrbitalDivisorAt_classFunction       the divisor is a class function on ℂ/(ℤ+ℤτ+ℤσ)
 7  differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor
                                                 vanishing divisor ⟹ differentially algebraic
 8  mixedConstGerm_ellipticGammaSource           Δ_τΔ_σΨ = -2πi as germs, so Ψ ∈ Q
 9  mixedConstGerm_gammaJetSource_succ           every higher jet has vanishing mixed constant
10  jetCombination, gammaCorrection              the correcting combination of gamma jets
11  additiveOrbitalDivisorAt_gammaCorrection     it carries the source's divisor on every class
12  exists_gammaCorrection_vanishing_divisor     F - A has vanishing divisor everywhere
13  exists_gammaCorrection_differentiallyAlgebraic
                                                 Cst = gammaCorrectionConst and
                                                 F - R_trip(F)Ψ ∈ Mer_DA        [normal form + (A2)]
14  exists_mem_class_with_prescribed_divisor     every divisor datum is realized   [surjectivity]
15  ellipticGammaCone_shift_eq                   the two elliptic gamma presentations agree
16  realizesMero_iteratedDeriv, realizesMero_logDeriv, realizesMero_translate
                                                 realization commutes with jets, quotients, shifts
17  realizesMero_gammaJetSource                  gamma jets realize the packet germs
18  differentialIndependent_ellipticGammaTranslateFamily_option
                                                 the translation packet, base source included, is
                                                 differentially independent over ℂ
19  not_differentiallyAlgebraic_jetCombination_option
                                                 a nonzero jet combination is hypertranscendental
20  exists_classTransversal                      class transversal of a finite set of base points
21  additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic
                                                 DA member of Q ⟹ vanishing divisor    [kernel ⊆]
22  differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
                                                 ker R_trip = Q ∩ Mer_DA               [completeness]
```

## Card statements and their Lean names

| Card statement | Lean |
|---|---|
| `R_τ(F) = R_σ(F)` | `triptic_orbit_residue_reciprocity` |
| `aug₀(R_trip(F)) = -C/(2πi)` (A2) | first conjunct of `exists_gammaCorrection_differentiallyAlgebraic` |
| `F - R_trip(F)Ψ ∈ Mer_DA` | second conjunct of `exists_gammaCorrection_differentiallyAlgebraic` |
| `R_trip` surjective | `exists_mem_class_with_prescribed_divisor` |
| `ker R_trip = Q ∩ Mer_DA` | `differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero` |

## Audit

Every declaration above depends only on `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
`admit`, `axiom`, `opaque` or `unsafe` declaration is involved, and no hypothesis beyond the card's
own standing assumptions (`τ, σ` in the upper half plane, `1, τ, σ` independent) is used.

The card's scientific-status line hedged completeness on "independent audit of the elliptic-gamma
atomic theorem".  That theorem is itself formalized in this corpus
(`ellipticGammaTranslatePacket_diffIndepOn_of_separated`, unconditional), so the hedge is discharged
in Lean rather than assumed.
