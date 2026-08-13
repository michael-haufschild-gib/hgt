# nad folder stage-3 sweep — 7 cards promoted (2026-08-13)

Goal: formalize every `2-fully-proven/nad` card unconditionally and move it to `3-formalized/nad`.
Ledger: `docs/drafts/pipeline/2-fully-proven/nad/_FORMALIZATION-LEDGER.md` (rows updated as I go).
Task list (one task per card) is in the session task tool.

## Promoted this session (companion + card moved + ledger row + card log)
1. `nevanlinna-boundary-bauer-retract-maximal-ht` — normalization independence (14)-(16):
   `NevanlinnaNormalizationTwist.lean` (matrix twist `W·g` for `g ∈ SL(2,ℝ)`, label covariance
   `(W·g).projectiveLabel = g⁻¹ • W.projectiveLabel`, fiber covariance, twisted family,
   `twist_carrierProjector`, `twist_range_barycenter`) + `NevTwistUnconditional.lean`.
2. `cofinal-cholesky-carrier-selection-threshold-law` — `AnalyticNevCofinalCholeskyUnconditional.lean`.
3. `singular-maximal-ht-schur-defect-collapse-law` — same module closes the real-line half.
4. `singular-maximal-ht-toeplitz-weld-graph-saturation` — same.
5. `spectral-type-stratified-moment-fiber-maximal-ht` — `BoundaryBarycenterSpectralTransport.lean`
   (Luzin (N) via `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, pure-point,
   absolutely-continuous (8), mutual-singularity transports, mixture mass vector (16)-(18)).
6. `finite-jet-aperture-complete-germ-closure-law` — `AnalyticNevRelationFreeUnconditional.lean`.
7. `hausdorff-positive-higher-spin-cdd-cone` — `PositiveMeasureExtremeRays.lean` (extreme rays of
   the cone of finite positive measures = point masses) + `HausdorffCddExtremeRays.lean` ((18),
   (18a), (18b), finite atomic sums).

## In progress: card `moment-polynomial-blind-resolvent-complete-boundary-splitting`
`HTGeometry/BoundaryConditionalExpectation.lean` (wired, axiom-clean) already proves:
`leafKernel`, `leafAverage`, `markovAverage`, `ae_projectiveLabel_eq`,
`integral_measureBarycenter`, **`integral_comp_projectiveLabel_mul_barycenter`** = (4),
**`markovAverage_ae_eq_condExp`** = (5) (σ-algebra `labelSigmaAlgebra = comap π`),
**`leafAverage_eval`** = (10), **`leafAverage_eval_sub_const`** = (11),
**`integral_eval_mul_comp_projectiveLabel`** = (12)-(13).
Remaining for that card:
- (6)-(8) `L²` splitting: `H_hor = lpMeas ℝ ℝ labelSigmaAlgebra 2 ν`, projection = `condExpL2`,
  `H_ver` = kernel = {f | leafAverage f = 0 η-a.e.}.
- (14)-(21) resolvent completeness.  **Analytic core**: span({1} ∪ {Φ_z}) dense in `L²(T,η)`.
  Route that avoids Riesz representation: take `g ∈ L²(η)` orthogonal to all of them, form the
  complex measure `g·η`, use the Möbius identity (18) to get a vanishing Cauchy transform on an
  open subset of BOTH half-planes (`q` maps lower→upper by `analyticNevCarrierFamily_lowerMap`,
  and `q(z̄) = conj q(z)`), then the identity theorem + complex-measure Stieltjes uniqueness.
  NOTE: vanishing on ONE half-plane is NOT enough (counterexample: density `1/(τ-i)²`).
- (21a)-(21i) three-layer Pick-Gram splitting and exact ranks.

## Key reusable facts
- Bottleneck 1 is CLOSED: `analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0` is complete;
  instantiate any capstone at `analyticNevCarrierFamily h h0b h0` / `nevBoundaryFamily h h0b h0`.
- `nevBoundaryFamily h h0b h0 = (nevExtremalFamily h h0b h0).toBoundaryFamily =
  (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily` — all rfl.
- Namespaces: `nevBoundaryFamily`, `analyticNevCarrierFamily`, `PositiveMomentForm`,
  `BoundedKernel`, `momentFunctional` live in **`HTGeometry`**; `NevanlinnaBoundaryFamily`,
  `NevanlinnaMatrixData` in `GaloisForLFunctions.HTGeometry`; `Hypertranscendental` in
  `GaloisForLFunctions`.  Header that works inside `namespace HTGeometry`:
  `open GaloisForLFunctions GaloisForLFunctions.HTGeometry`.
- `integral_bind_real` (HamburgerBoundaryKernel) is the real-valued Fubini for barycenters.
- `StronglyMeasurable.integral_kernel` needs a `Kernel`; wrap `F.leafMeasure` + `F.measurable_leaf`.

## Umbrella build is currently broken by ANOTHER agent's in-flight edit
`lake build GaloisForLFunctions.HTGeometry` fails on a duplicate `cauchyTransform` between
`ContinuousMapCauchyTransform.lean` (uncommitted, another agent) and
`RegularizedHerglotzTransform.lean`.  I fixed one earlier collision myself (renamed
`abs_exp_sub_exp_le` → `abs_exp_sub_exp_le_of_abs_sub_le_one` in `HerglotzJetMapContinuity.lean`
plus its use in `NodeJetUniformLipschitz.lean`).  Do NOT edit the other agent's modified file;
re-run the umbrella audit later.  All my own modules build individually through their full
dependency chains and are axiom-clean.

## Remaining cards and their real blockers
- `indeterminate-moment-fiber-maximal-translation-ht`: density of `Ext M(s)` (Naimark) — needs the
  full Nevanlinna parametrization by Pick functions (Herglotz representation), not just constants.
- `pick-defect-finite-selector-maximal-ht-phase-law`: confluent Nevanlinna–Pick + `J`-inner.
- `xi-schur-inverse-limit-atomic-condensation-law`: source-faithful Xi circle measure + bridge to
  `continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` (capstone currently takes
  `RH ↔ mu ⟂ₘ circleLebesgue` as an argument).
- `affine-jet-packet-collision-completeness`: Fréchet space of multivariate entire functions,
  Hermite interpolation, affine chain rule, determinant→differential independence.
- Bottleneck 2 (Ritt / Becker–Bergweiler): cards asymmetric-binary-tree, bethe-padic,
  diamond-ising ×2, postselected-qubit, one-species, kolchin-exchange (13)/(15).
- Bottleneck 3 (Ritt–Kolchin / Bohr / Pontryagin): nonautonomous-kolchin, singular-autonomous-ade,
  and `signed-archimedean-gamma-orbit-charge-phase-law` (its (37) rests on the implicit-ADE
  frequency theorem; the elementary `rank_Q Λ_N = π(N)` is already proved).
- QFT-substrate cards (compact-local form factor, collision-phase complexity, open-family CDD,
  q-ladder Jost, sectoral Kolchin, wedge PFG, identity-zero Pauli, two-state fermionic): need
  LSZ/Haag–Ruelle transfer, locality/positivity inequalities, or the exp(O(n)) intertwiner.
- `constrained-prolate-continuous-polar-charge-law`: prolate spheroidal theory (absent in mathlib).
- `gauss-paired-quasi-inner-channel-schatten-depth-law`: weak Schatten ideals + Dixmier traces.
- `projective-constraint-...` / `projective-hurwitz-...`: triangle/modular curves, Kummer minimality.
