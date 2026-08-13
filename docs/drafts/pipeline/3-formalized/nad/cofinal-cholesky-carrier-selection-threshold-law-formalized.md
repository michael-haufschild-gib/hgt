# Finite Cholesky frames retain maximal HT; the complete divergent tower selects the carrier — formalized

- **ID:** `cofinal-cholesky-carrier-selection-threshold-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `cofinal-cholesky-carrier-selection-threshold-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/CofinalCholeskyFiniteFrame.lean`, `HTGeometry/CayleyMomentFrame.lean`, `HTGeometry/CauchyJetFrame.lean` | the Cayley triangular transform, prefix equivalence of Cayley moments and regular Cauchy jets, the inverse Gram identity `G⁻¹ = CᴴC`, the canonical inverse-Cholesky frame, its uniqueness, determinant identities, and leading-principal compatibility of the tower |
| `HTGeometry/CompleteGramTowerTopology.lean`, `HTGeometry/CanonicalFrameClosedGraph.lean`, `HTGeometry/CanonicalFrameContinuity.lean`, `HTGeometry/CompleteFrameTowerTopology.lean` | continuity and injectivity of the complete tower and its closed-embedding property on compact carrier families |
| `HTGeometry/CholeskyDeterminantDivergence.lean` | vanishing normalized Gram determinants force frame-determinant, least-eigenvalue, and operator-norm escape, with the exact identity `‖C_N‖₂ = λ_min(G_N)^(-1/2)` |
| `HTGeometry/PositiveHilbertCubeEmbedding.lean`, `HTGeometry/FiniteConstraintBlockKernel.lean`, `HTGeometry/CountableConstraintBlockAperture.lean`, `HTGeometry/LinftyFiniteConstraintAperture.lean`, `HTGeometry/LinftyPositiveAperture.lean` | the Banach-space core of the finite-prefix aperture and its `L∞` realization |
| `HTGeometry/AtomlessProjectivePositiveAperture.lean`, `HTGeometry/InfiniteSupportPositiveAperture.lean`, `HTGeometry/ProjectiveFiniteConstraintCarrierAperture.lean`, `HTGeometry/AtomlessProjectiveFrameFiber.lean` | the projective block partition and the Hilbert-cube frame fiber with identical level-`N` Gram section and Cauchy jet |
| `HTGeometry/GraphSaturationCore.lean`, `HTGeometry/ToeplitzPolynomialGraph.lean`, `HTGeometry/RieszBrothersReduction.lean`, `HTGeometry/FAndMRieszVanishing.lean`, `HTGeometry/RieszSingularSzegoCollapse.lean` | the polynomial graph as a submodule, its exact orthogonal complement, the reduction to one-sided Fourier rigidity, and the F. and M. Riesz theorem together with the singular Szegő collapse |
| `HTGeometry/NevanlinnaBoundaryAlgebra.lean`, `HTGeometry/NevanlinnaBoundaryKernel.lean`, `HTGeometry/LabeledBoundarySimplex.lean`, `HTGeometry/HamburgerBoundaryKernel.lean`, `HTGeometry/NevanlinnaClassicalInterface.lean` | the boundary label, the labeled simplex, unbounded moment preservation, and the exact source-convention adapter |
| `HTGeometry/NevExtremalFamily.lean`, `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/NevanlinnaTransferMinimalType.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean` | the construction of the classical `N`-extremal Nevanlinna family and of the complete `MaximalTranslationInputs` term |
| `HTGeometry/CofinalCholeskyResidualPhase.lean` | the global weak-topology gluing of the carrier-range residual phase |
| `HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean` | the same capstone with no structure input: stated for the constructed family |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `HTGeometry.nevExtremalFamily`, `HTGeometry.exists_classicalAnalyticNevanlinnaCarrierFamily` —
  the classical `N`-extremal Nevanlinna family is constructed from `PositiveMomentForm s`,
  `BoundedKernel s 0`, `s 0 = 1` alone;
- `HTGeometry.analyticNevCarrierFamilyMaximalTranslationInputs` — the complete input term
  (minimal exponential type by M. Riesz through Simon's transfer route, no common zero, zero and
  regular points, lower-to-upper Weyl map);
- `HTGeometry.analyticNevCarrierFamily_cofinalCholeskyResidualPhase_dense_gdelta_residual` —
  **the card's capstone, unconditional**: on the complete Nevanlinna carrier range of an
  indeterminate normalised moment sequence the singular-continuous maximal-translation phase is
  dense, `Gδ`, and residual;
- `HTGeometry.analyticNevCarrierFamily_cofinalPhase_isSingularContinuous_maximalTranslation` —
  every point of that phase is an atomless carrier, mutually singular with Lebesgue measure, and
  maximally translation-differentially free;
- `HTGeometry.analyticNevCarrierFamily_carrierRange_maximalTranslationPhase_dense` — the
  maximal-translation locus alone is dense in the carrier range.

The finite-frame, aperture, graph-saturation, and Riesz layers listed above were audited
axiom-clean when they were built and are unchanged.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean
lake build GaloisForLFunctions.HTGeometry.AnalyticNevCofinalCholeskyUnconditional
```

## What closed last

The card's single open formalization gate was "unconditional construction of the classical
`N`-extremal Nevanlinna family".  With `nevExtremalFamily` and
`analyticNevCarrierFamilyMaximalTranslationInputs` in place, the residual-phase capstone no longer
takes any structure or analytic argument: it is a theorem about every indeterminate normalised
Hamburger moment sequence.

## Boundary

The two remaining gates on the paper card — an independent specialist proof audit and a full
primary-source priority audit, together with the exact primary-source match for each literature
interface — are external literature obligations, not formalization obligations.  This is not a
proof of RH; the card's RH content is a carrier requirement only.
