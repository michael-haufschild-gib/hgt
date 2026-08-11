# Constraint-relativity stage-2 → stage-3 progress

Working note for the promotion sweep.  Not a card.

## Promoted this sweep (paper card + `-formalized.md` companion now in `3-formalized/constraint-relativity/`)

| Card | Lean module |
|---|---|
| `route-r-raw-resolved-relative-cone-character-law` | `HTGeometry/ConstraintRelativity/RouteRRawCurvature.lean`, `RouteRConeCharacter.lean` |
| `ultrametric-horizon-energy-smith-correspondence` | `HTGeometry/ConstraintRelativity/UltrametricHorizonEnergySmith.lean` + `SmithNormalFormDVR`, `DeterminantalIdeal`, `DVRFiniteSpan`, `AlternantVandermondeDivisibility` |
| `phase-subdiscriminant-kahler-smith-stratification-law` | `HTGeometry/ConstraintRelativity/PhaseSubdiscriminantKaehlerSmith.lean` |
| `prime-radial-excess-intersection-discriminant-law` | `HTGeometry/ConstraintRelativity/PrimeRadialExcessDiscriminant.lean` |
| `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law` | `RHTower/CCMRationalAdelicPrimeIsotropyObserverFreedom.lean` |
| `prime-isotropy-vertical-shear-gauge-torsor-and-nonerasure-dichotomy` | `RHTower/CCMRationalAdelicPrimeIsotropyVerticalGauge.lean` |
| `two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law` | `RHTower/CCMRationalAdelicTwoEndpointStokesModuli.lean` |

All modules are wired into their area umbrella, build green, and every listed declaration returns
only `[propext, Classical.choice, Quot.sound]`.

## Remaining in stage 2

- `banach-two-boundary-observer-radical-and-horizon-layer-duality`
- `factor-framed-tensor-jacobian-defect-law`
- `passive-relation-triangle-energy-and-interaction-cross-fibre-law`
- `polarized-incidence-stokes-and-e-mass-capacity-phase-law`
- `provenance-admission-connecting-law-and-flat-completion-cube`
- `residue-preserving-law-promotion-anomaly-trilemma`
- `resource-filtered-relation-typicality-and-recurrence-no-go`

## Scouting notes

### `banach-two-boundary-observer-radical-and-horizon-layer-duality` — deferred, needs new analysis

`(BHR.2)`/`(BHR.4)` (cone kernel `= Y_L ⊓ Y_R`) and `(BHR.7)` (the continuous observer exact
sequence) are straightforward: Hahn–Banach extension is `StrongDual.exists_extension`.

The two hard equations need machinery mathlib does **not** have:

- `(BHR.8)`, `K^⊥ = w*-closure(Y_L^⊥ + Y_R^⊥)`, is the bipolar theorem for subspaces.  mathlib has
  `LinearMap.polar`, `StrongDual.polar`, `LinearMap.subset_bipolar`, and — crucially —
  `WeakBilin.dualEmbedding_surjective` / `WeakBilin.dualEquiv` in
  `Mathlib/Analysis/LocallyConvex/WeakDual.lean` (the dual of a weak topology is the pairing
  partner).  There is **no** subspace bipolar theorem.  Route: separate `f ∉ w*-closure S` from the
  closed subspace by `geometric_hahn_banach_*`, identify the separating functional as an evaluation
  via `WeakBilin.dualEquiv`, then use that the pre-annihilator of `Y_L^⊥ + Y_R^⊥` is `Y_L ⊓ Y_R`
  (Hahn–Banach through the quotient norm, `exists_dual_vector` on `E ⧸ Y`).
- `(BHR.14)`, `M(b)^⊥/M(a)^⊥ ≅ (M(a)/M(b))_*`, is the predual quotient theorem for weak-* closed
  subspaces.  mathlib has no von Neumann predual theory; the Banach-space core to build is: for a
  normed space `X` and weak-* closed subspaces `N ≤ P` of `StrongDual 𝕜 X`, the pairing
  `(P_⊥ ⧸ N_⊥) × (P ⧸ N) → 𝕜` identifies the left side with the weak-*-continuous functionals on
  `P ⧸ N`, isometrically.

`(BHR.12)` (layer = kernel of the cut projection) and `(BHR.18)` (modular pairing covariance) are
elementary once the pairing is set up.  `(BHR.21)`–`(BHR.24)` (the finite thermofield
countermodel) are finite-dimensional and independent of the above.
