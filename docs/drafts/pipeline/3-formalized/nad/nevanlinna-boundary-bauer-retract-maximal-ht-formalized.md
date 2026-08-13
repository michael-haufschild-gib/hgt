# The Nevanlinna boundary is a canonical Bauer retract carrying maximal translation HT — formalized

- **ID:** `nevanlinna-boundary-bauer-retract-maximal-ht-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `nevanlinna-boundary-bauer-retract-maximal-ht.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/NevanlinnaBoundaryAlgebra.lean` | determinant-one matrix data, the projective support label `[-D:C]` (4), its continuity, and the fiber calculus |
| `HTGeometry/NevanlinnaBoundaryKernel.lean` | the boundary family, exact label pushforward (5), the boundary barycenter (7), complete moment preservation, and the closed embedding (10) |
| `HTGeometry/NevanlinnaConstraintProjector.lean` | the left inverse (9), the canonical retraction (12)–(13), the constraint Markov kernel and operator (17)–(21), and the leaf/label covariance transport |
| `HTGeometry/NevanlinnaAffineGeometry.lean`, `HTGeometry/NevanlinnaBauerRetract.lean` | affinity of the retraction on probability mixtures |
| `HTGeometry/NevanlinnaBoundaryFaceLattice.lean` | the closed-face lattice (23)–(24) |
| `HTGeometry/NevanlinnaStationaryBauer.lean` | the stationary simplex (22) and its extremal boundary |
| `HTGeometry/NevanlinnaKernelErgodicity.lean` | ergodic stationary laws are exactly the `N`-extremal leaves |
| `HTGeometry/NevExtremalFamily.lean` | the classical `N`-extremal family, constructed from the moment data alone |
| `HTGeometry/NevBauerUnconditional.lean`, `HTGeometry/NevBauerMarkovFacesUnconditional.lean` | the whole list above instantiated at the constructed family |
| `HTGeometry/NevanlinnaNormalizationTwist.lean` | the Möbius action of `SL(2,ℝ)` on the projective line, the matrix twist `W · g`, label and fiber covariance, and the twisted boundary family |
| `HTGeometry/NevTwistUnconditional.lean` | normalization independence (14)–(16) for the constructed family |
| `HTGeometry/NevanlinnaBoundaryFaceMaximalTranslation.lean`, `HTGeometry/NevanlinnaFullRankPhaseGdelta.lean` | the residual maximal-translation phase on every infinite closed face (25)–(27) and its unconditional `Gδ` detector |
| `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/NevanlinnaTransferMinimalType.lean`, `HTGeometry/NevanlinnaEntryConjugation.lean`, `HTGeometry/NevanlinnaCarrierDenominatorRow.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean` | the analytic carrier family, M. Riesz minimal exponential type, the Weyl half-plane map, and the complete `MaximalTranslationInputs` term |

Every module is reachable from `GaloisForLFunctions.HTGeometry`.

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.
All statements below assume only `PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1` — the
card's own setup (1) — and no analytic input.

- (4)–(6) support fibration: `NevanlinnaBoundaryFamily.map_projectiveLabel_leaf` — the exact
  projective label of every leaf is its parameter;
- (7)–(9) barycentring and its left inverse:
  `NevanlinnaBoundaryFamily.barycenter_hasHamburgerMoments`, `nevProjectiveLaw_barycenter`;
- (10)–(11) Bauer simplex and extreme boundary: `nevBauer_isClosedEmbedding`,
  `nevBauer_extreme_iff`;
- (12)–(13) canonical retraction: `nevCarrierProjector_idempotent`, `nevCarrierProjector_range`,
  `nevCarrierProjector_fixed_iff`;
- (14)–(16) normalization independence: `nevCarrierProjector_twist`, `nevBarycenter_range_twist`,
  with the underlying covariance
  `NevanlinnaMatrixData.twist_projectiveLabel : (W · g).label = g⁻¹ • W.label` and
  `NevanlinnaBoundaryFamily.twist_carrierProjector`;
- (17)–(20) constraint randomizer: `nevConstraintKernel_isWeakFeller`,
  `nevConstraintKernel_idempotent`, `nevConstraintMarkovOperator_idempotent`,
  `nevConstraintKernel_integral_pow` (every monomial is flattened to its prescribed moment in one
  step);
- (21)–(22) one-step landing and stationarity: `nevCarrierProjector_hasHamburgerMoments`,
  `nevStationaryProbabilityLaws_eq_carrierRange`, `nevErgodicConstraintStationaryBoundary`;
- (23)–(24) closed-face lattice: `nevBoundaryCarrierFace_isProbabilityLawFace`,
  `nevBoundaryCarrierFace_mono`, `nevBoundaryCarrierFace_inter`,
  `nevBoundaryCarrierFace_subset_iff`;
- (25)–(27) the HT phase law:
  `analyticNevCarrierFamily_maximalTranslationPhase_dense_residual` — for every infinite closed
  `K ⊆ RP¹(ℝ)`, the maximal-translation phase is dense in the boundary carrier face and residual
  in it.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/NevanlinnaNormalizationTwist.lean
lake env lean GaloisForLFunctions/HTGeometry/NevTwistUnconditional.lean
lake build GaloisForLFunctions.HTGeometry.NevTwistUnconditional
```

Twenty-two-declaration axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## What closed last

The final formalization gate was the card's §"Independence of the Nevanlinna normalization"
(14)–(16).  It is now a theorem rather than a transport under hypotheses: right translation of the
determinant-one matrix data by `g ∈ SL(2,ℝ)` is a boundary family of the *same* moment sequence,
because `c'(x)σ + d'(x) = c(x)(g₀₀σ + g₀₁) + d(x)(g₁₀σ + g₁₁)` identifies its denominator fibers
with the original fibers relabelled along the Möbius action; the projective label therefore
transforms by `g⁻¹`, and the leaf/label covariance transport gives equality of the two carrier
projectors and of the two boundary simplices.

## Boundary

The formalized surface is the card's numbered list.  The card's two remaining gates — an
independent specialist proof audit and a full primary-source priority audit — are external
literature obligations, not formalization obligations.  This is not a proof of RH.
