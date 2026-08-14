# nad folder stage-3 sweep — 8 cards promoted (2026-08-13/14)

Goal: formalize every `2-fully-proven/nad` card unconditionally and move it to `3-formalized/nad`.
Ledger: `docs/drafts/pipeline/2-fully-proven/nad/_FORMALIZATION-LEDGER.md`; task list = one task/card.

## Promoted (companion + card moved + ledger row + card log)
1. `nevanlinna-boundary-bauer-retract-maximal-ht` — `NevanlinnaNormalizationTwist.lean` +
   `NevTwistUnconditional.lean` (SL(2,ℝ) twist, label covariance, projector invariance).
2. `cofinal-cholesky-carrier-selection-threshold-law` — `AnalyticNevCofinalCholeskyUnconditional`.
3. `singular-maximal-ht-schur-defect-collapse-law` — same module (real-line half).
4. `singular-maximal-ht-toeplitz-weld-graph-saturation` — same.
5. `spectral-type-stratified-moment-fiber-maximal-ht` — `BoundaryBarycenterSpectralTransport`
   (Luzin (N), pure-point / a.c. / singular transports, mixture mass vector).
6. `finite-jet-aperture-complete-germ-closure-law` — `AnalyticNevRelationFreeUnconditional`.
7. `hausdorff-positive-higher-spin-cdd-cone` — `PositiveMeasureExtremeRays` +
   `HausdorffCddExtremeRays` (extreme rays of the positive cone = point masses).
8. `moment-polynomial-blind-resolvent-complete-boundary-splitting` — six new modules, see below.

## New reusable infrastructure (all axiom-clean, wired into `GaloisForLFunctions.HTGeometry`)
- `CauchyTransformOpenUniqueness.lean` — **finite measures are determined by their Cauchy transform
  on any nonempty open subset of a half-plane** (identity theorem + mass `lim y·Im S(iy)` +
  normalisation into `measure_eq_of_completeCauchyJet_eq`).
- `CauchyKernelDensityVanishing.lean` — **an integrable complex density whose Cauchy transform
  vanishes on an open subset of BOTH half-planes is zero a.e.**  One half-plane is NOT enough
  (counterexample `(τ−i)⁻²`).  Also `analyticOnNhd_densityCauchyTransform`, `…_conj`.
- `NevanlinnaQuotientOpenImage.lean` — the Weyl pole `q = −d/c` is nonconstant (else the real lower
  row vanishes, contradicting det = 1) and has open images.
- `BoundaryConditionalExpectation.lean` — leaf kernel/average, `markovAverage_ae_eq_condExp`,
  vertical-kernel characterisation, polynomial blindness.
- `NevanlinnaResolventCompleteness.lean` — `chartMeasure`, `integral_onePoint_split`, `leafCauchy`,
  Möbius partial fraction, resolvent completeness (+ constructed-family version),
  `leafCauchy_injective_on_chart`.
- `NevanlinnaPickGramSplitting.lean` — `integral_bind_bounded` (complex Fubini over a probability
  kernel), the three Gram kernels, the law of total covariance, self-Gram = variance, and
  `boundaryGram_eq_zero_iff_exists_dirac`.
- `NevanlinnaBoundaryL2Completeness.lean` — `L²` density of constants + leaf transforms; closed span
  of the centered features = orthogonal complement of the constants; rank-one mean layer;
  `polynomial_eq_zero_of_ae_eq_zero_of_support_infinite`.
- `PositiveMeasureExtremeRays.lean` — extreme rays are point masses;
  `exists_eq_dirac_of_measure_eq_zero_or_one` (two-valued probability ⇒ Dirac).

## Lean gotchas collected
- `V₊`/`z₊` are not valid identifiers; use `Vup`/`Vlow`.
- `ring` cannot cancel `(2*I)⁻¹ * I` — state constants as `-(2:ℂ)⁻¹ * I` and feed `Complex.I_sq`.
- `Integrable.conj` does not exist; use `Integrable.mono' hint.norm …`.
- `Integrable.mono'` goals have no outer norm on the bound side.
- mathlib's `L2.inner_def` unfolds pointwise as `g t * conj (f t)` — write `show` in that order.
- `Submodule.topologicalClosure_eq_top_iff` takes no explicit submodule argument.
- `set X := …` inside a proof breaks later `rw` pattern matching — prefer plain `have`s.
- `SecondCountableTopology (OnePoint ℝ)` is NOT an instance: derive from
  `onePointRealUnitAddCircleHomeomorph.isEmbedding.secondCountableTopology`.
- `#print axioms` needs a fresh olean: `lake build <module>` before the scratch import.

## Remaining 28 cards — blockers
- `indeterminate-moment-fiber-maximal-translation-ht`: density of `Ext M(s)` (Naimark) — needs the
  Nevanlinna parametrisation by general Pick functions (Herglotz representation).
- `pick-defect-finite-selector-maximal-ht-phase-law`: confluent Nevanlinna–Pick + `J`-inner.
- `xi-schur-inverse-limit-atomic-condensation-law`: construct the canonical Xi circle measure and
  bridge its singularity to `continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis`.
- `affine-jet-packet-collision-completeness`: **next target**.  Needs O(ℂ^d) as a Baire space
  (mathlib has `compactConvergenceUniformSpace`, `instCompleteSpaceOfCompactlyCoherentSpace`, and
  countably-generated uniformity ⇒ metrizable ⇒ Baire; entire functions are a closed subspace),
  finite Hermite interpolation, the affine chain rule, and determinant → differential independence.
- Bottleneck 2 (Ritt / Becker–Bergweiler): asymmetric-binary-tree, bethe-padic, diamond-ising ×2,
  postselected-qubit, one-species, kolchin-exchange (13)/(15).
- Bottleneck 3 (Ritt–Kolchin / Bohr / Pontryagin): nonautonomous-kolchin, singular-autonomous-ade,
  signed-archimedean (37).
- QFT-substrate cards: compact-local form factor, collision-phase complexity, open-family CDD,
  q-ladder Jost, sectoral Kolchin, wedge PFG, identity-zero Pauli, two-state fermionic.
- `constrained-prolate-…`: prolate spheroidal theory.  `gauss-paired-…`: weak Schatten + Dixmier.
- `projective-constraint-…`, `projective-hurwitz-…`: triangle/modular curves, Kummer minimality.

## Repo hygiene
`lake build GaloisForLFunctions.HTGeometry` (umbrella) currently fails on a duplicate
`cauchyTransform` between another agent's uncommitted `ContinuousMapCauchyTransform.lean` and
`RegularizedHerglotzTransform.lean`.  I fixed the committed `abs_exp_sub_exp_le` collision
(renamed in `HerglotzJetMapContinuity.lean` + `NodeJetUniformLipschitz.lean`).  Never edit another
agent's modified file; one `lake build` at a time.
