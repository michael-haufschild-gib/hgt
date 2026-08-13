# Finite-jet aperture and complete-germ closure threshold — formalized

- **ID:** `finite-jet-aperture-complete-germ-closure-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `finite-jet-aperture-complete-germ-closure-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/CauchyJetControllability.lean` | real-linear surjectivity of the finite Cauchy-jet map on the positive tangent and arbitrarily small finitely supported perturbations |
| `HTGeometry/PositiveHilbertCubeEmbedding.lean`, `HTGeometry/FiniteConstraintBlockKernel.lean`, `HTGeometry/CountableConstraintBlockAperture.lean` | the closed embedded signed Hilbert cube inside every finite affine constraint fiber |
| `HTGeometry/InfiniteSupportPositiveAperture.lean`, `HTGeometry/AtomlessProjectivePositiveAperture.lean` | the countable positive block partition from infinite support (resp. atomlessness) and the resulting positive aperture |
| `HTGeometry/AtomlessProjectiveFrameFiber.lean` | the Hilbert cube inside the *exact* Cayley frame fiber: same level-`N` Gram section and same regular Cauchy jet through order `N-1` |
| `HTGeometry/AnalyticNevanlinnaCarrierBridge.lean`, `HTGeometry/NevanlinnaPositiveCarrierCapstone.lean`, `HTGeometry/AnalyticNevanlinnaCarrierRelationFree.lean` | identification of the abstract frozen tangent with actual weighted Nevanlinna-carrier jets and the dense residual all-finite-pattern hypertranscendental phase |
| `HTGeometry/AnalyticNevRelationFreeUnconditional.lean` | the same two capstones with every analytic hypothesis discharged for the constructed family |
| `HTGeometry/CompleteCauchyGermClosure.lean` | complete-germ closure: one complete nonreal Cauchy jet determines the carrier probability law, at every nonreal node |
| `HTGeometry/NevExtremalFamily.lean`, `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/NevanlinnaTransferMinimalType.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean` | the constructed Nevanlinna family, M. Riesz minimal exponential type, and the complete input term |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `HTGeometry.analyticNevCarrier_positiveActualCarrier_hypertranscendental_dense_residual` —
  **the finite-jet residual law, unconditional**: freeze any finite packet of upper-half-plane
  Cauchy jets against an infinite-support parameter law; the positive mass-one chart of the frozen
  level contains a dense residual family whose actual weighted-carrier Cauchy transforms are
  hypertranscendental, and every chart point is a strictly positive normalised density;
- `HTGeometry.analyticNevCarrier_positiveSingularContinuousCarrier_hypertranscendental_dense_residual`
  — the same at fixed singular-continuous spectral type: every chart point is an atomless
  Lebesgue-singular probability solution of the *same* Hamburger moment problem;
- `GaloisForLFunctions.HTGeometry.exists_closedEmbeddedHilbertCube_in_exactCayleyFrameFiber_of_infiniteSupport`
  — infinite-dimensional positive aperture inside the exact finite Cayley/Cauchy-jet level;
- `GaloisForLFunctions.HTGeometry.exists_positive_closedEmbeddedHilbertCube_in_infiniteSupportConstraintFiber`
  — the Banach-space core of that aperture;
- `GaloisForLFunctions.HTGeometry.surjective_finsupp_full_tangent_at_positive` — disjoint-pole
  controllability on the constrained tangent;
- `GaloisForLFunctions.HTGeometry.measure_eq_of_completeCauchyJet_eq` — **the threshold**: the
  complete Cauchy germ at any nonreal point determines the carrier, so the boundary modulus closes
  to a point exactly at completion.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AnalyticNevRelationFreeUnconditional.lean
lake build GaloisForLFunctions.HTGeometry.AnalyticNevRelationFreeUnconditional
```

## What closed last

The card's Lean status said: "Until the Nevanlinna family is constructed in Lean, the residual-HT
half of the card is not unconditional."  The family is now constructed
(`nevExtremalFamily`, `exists_classicalAnalyticNevanlinnaCarrierFamily`) and carries a complete
`MaximalTranslationInputs` term, whose five fields are exactly the analytic hypotheses of the
relation-free capstones — minimal exponential type, no common lower-row zero, a zero and a regular
point of the denominator entry, and the Weyl half-plane map.  The label null-preimage hypothesis of
the singular-continuous version is discharged by real analyticity of the lower row.  Only the
frozen-jet data and the parameter law remain as arguments, as they must.

## Boundary

The remaining gates are an independent specialist proof audit and a full primary-source priority
audit — external literature obligations.  The RH content is stated as a carrier requirement: any
route using finitely many local values, derivatives, Hankel minors or resolvent samples leaves the
positive aperture; only a complete coherent germ or a global orientation law closes it.  This is
not a proof of RH.
