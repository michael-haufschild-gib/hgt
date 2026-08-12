# nad Bottleneck 1 — the Weyl-disc closed form is PROVED; `upperMap` is a sign bug

## What was closed (2026-08-12), all axiom-clean, all wired into `GaloisForLFunctions.HTGeometry`

The ledger's "highest-leverage unproved statement in the folder" is done.

`HTGeometry/NevLeafCauchyMoebius.lean`
- `nevTrunc_cauchy_identity` — finite stage, cleared of denominators:
  `(Bₙ(z)τ − Dₙ(z))·∫(x−z)⁻¹dμₙ = −s₀·(Aₙ(z)τ − Cₙ(z))`, where
  `μₙ = quasiMeasure s n (nevBeta s n τ / nevAlpha s n τ)`.
  Proof: multiply `quasiMeasure_cauchy_identity_of_im_ne_zero` by the common factor
  `(h₀/hₙ)·nevAlpha`, using `nevTruncNumeratorC_eq_quasi` / `nevTruncDenominatorC_eq_quasi`.
- `nevInf_cauchy_identity` — the limit `(B(z)τ − D(z))·∫(x−z)⁻¹dν_τ = −(A(z)τ − C(z))`.
  Proof: `exists_tendsto_quasiProbMeasure_nevLeaf` (weak convergence of the quadrature levels)
  + `tendsto_cauchyTransform_of_tendsto` + `tendsto_nev{A,B,C,D}truncC` composed with
  `Tendsto (goodLevel h tau ∘ φ) atTop atTop`; `tendsto_nhds_unique`.
- `nevInf_denominator_ne_zero` — `Bτ − D ≠ 0` off the real axis (else numerator vanishes too and
  `AD − BC = 0 ≠ 1`; the determinant needs `boundedKernel_global h h0b z`).
- `cauchyTransform_nevLeaf_eq_moebius` — **the Weyl-disc closed form**
  `∫(x−z)⁻¹dν_τ = −(A(z)τ − C(z))/(B(z)τ − D(z))`.

`HTGeometry/NevLeafInfinityCauchyMoebius.lean` — the same at the parameter `∞`:
`nevLeaf_infinity_eq_fiberMeasure`, `exists_tendsto_quasiProbMeasure_nevLeafInf`,
`ofReal_nevAlphaInf/BetaInf`, `nevAtruncC_closedInf`, `nevBtruncC_closedInf`,
`nevAtruncC_eq_quasiInf`, `nevBtruncC_eq_quasiInf`, `nevTruncInf_cauchy_identity`,
`nevInf_cauchy_identity_infty`, `nevBinf_ne_zero`, `cauchyTransform_nevLeafInf_eq_ratio`
(`∫(x−z)⁻¹dν_∞ = −A(z)/B(z)`).

`HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`
- **`analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s`** — item 1 of
  Bottleneck 1 is CLOSED.  Carrier convention `(a,b,c,d) = (−A, C, B, −D)`.
- `exists_classicalAnalyticNevanlinnaCarrierFamily`.

Hypotheses throughout: only `PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1`.

## The ledger was stale in two places

- `nevTrunc_moebius_eq_convergent` is **present and proved** in `NevTruncConvergent.lean`
  (the ledger says it was backed out).
- `NevTruncCauchyTransform.quasiSum_cauchy_eq_nevTruncC` already had the finite-stage Weyl-disc
  form before this session.

## HARD FINDING — `MaximalTranslationInputs.upperMap` is FALSE (uninhabitable structure)

`NevanlinnaBoundaryFaceMaximalTranslation.MaximalTranslationInputs` requires
`upperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im`, with `F.quotient z = −F.d z / F.c z = D(z)/B(z)`
— the pole of the Möbius map `τ ↦ (aτ+b)/(cτ+d)`.

The map sends `ℝ ∪ {∞}` into the open upper half-plane (each image is `∫(x−z)⁻¹dν_τ`, a Cauchy
transform of a probability measure at `Im z > 0`).  A Möbius map of the sphere carries one open
half-plane onto the disc bounded by that circle and the other onto its exterior; the pole maps to
`∞`, which is exterior.  Since the closed upper half-plane maps into the disc (Pick-class constants
are admissible parameters), **the pole lies in the open lower half-plane**: `(F.quotient z).im < 0`.

Two independent confirmations:
1. Algebraic: writing `Im f(τ) = Q(τ)/|Bτ−D|²` with
   `Q(τ) = −Im(A B̄)|τ|² + Im((A D̄ − C̄ B)τ) − Im(C D̄)`, one computes `Q(D/B) = 0` identically
   (pure algebra), while `Q > 0` on `ℝ`; writing `q = q₁ + iq₂` and subtracting `Q(q₁)` gives
   `q₂(α q₂ + Re β) = −Q(q₁) < 0` with `α = −Im(A B̄) > 0`, `β = A D̄ − C̄ B`.  `Re β ≠ 0` follows
   at once, `Re β → 1` as `z → ℝ` (because `β = G(z, z̄)` with `G(z,z) = AD − BC = 1`), and `Re β`
   is continuous and nonvanishing on the connected upper half-plane, hence `Re β > 0`, hence
   `q₂ < 0`.
2. Explicit model: `f(τ) = i + ε(τ−i)/(τ+i)` maps `ℝ` to a small circle about `i` inside the upper
   half-plane and has its pole at `−i`.

Consequence: `MaximalTranslationInputs` cannot be inhabited for the canonical family, so
`boundaryCarrierFace_maximalTranslationPhase_dense_residual` is currently vacuous, and item 2 of
Bottleneck 1 is blocked on an interface repair, not on new analysis.

**Repair plan.**  Replace `0 < (F.quotient z).im` by `(F.quotient z).im ≠ 0` throughout the chain,
and `hupperf : ∀ i, 0 < (F.quotient (zf i)).im` likewise.  The deepest layer already only needs
`≠ 0` (`projectiveNevanlinnaValueLinftyControl` takes `hq : (F.quotient z).im ≠ 0`, and
`continuous_projectiveCauchyPower` takes `q.im ≠ 0`), so the change should be mechanical.
19 files mention the positivity form:
`CompactNevanlinnaUniformProbe`, `AnalyticNevanlinnaCarrierRelationFree` (24 hits),
`SingularContinuousFullTranslationFamilyFreenessUniversalityLaw`,
`NevanlinnaNoncriticalProjectiveCompactPatch`, `ConstrainedCauchyJetControllability`,
`NevanlinnaTranslatedExpandedEvaluationCompactPatch`, `NevanlinnaBoundaryFaceMaximalTranslation`,
`ProjectiveCauchyDensityControl`, `ProjectiveNevanlinnaGenericity`,
`AnalyticNevanlinnaCarrierBridge` (10 hits), `BoundaryCarrierTranslationFreeness`,
`NevanlinnaJetTriangular`, `CarrierHerglotzPresentationFree`,
`ProjectiveNevanlinnaPolynomialEscape`, `NormalizedProjectiveCauchyDensityControl`,
`NevanlinnaExpandedEvaluationCompactPatch`,
`SingularContinuousHerglotzMaximalFreenessUniversalityLaw`, and two `RHTower` universality laws.

## Remaining for the ten Bottleneck-1 cards

1. the interface repair above;
2. `HasMinimalExponentialType (nevBinf s)` — **M. Riesz's theorem** that the Nevanlinna matrix has
   minimal exponential type.  The corpus's Gronwall bound (`SecondKindGlobal`) only gives
   `exp(C‖z‖²)`, i.e. order 2, so it is useless here.  The classical route is: the zeros of `B` are
   the support of `ν_∞` and satisfy `∑ 1/|xₖ| < ∞`, then a genus-0 Hadamard product gives minimal
   type (for any `A > 0`, split off the finitely many zeros with `|xₖ| ≤ R` and bound the tail by
   `exp(A‖z‖)`).  Needs Hadamard factorization, which mathlib does not have.
3. `phase_isGδ : IsGδ {ν | MaximalTranslationDifferentialFree ν}`;
4. the two easy fields: `noCommonZero` (from `AD − BC = 1`) and `regularPoint` (`nevBinf s I ≠ 0`
   by `nevBinf_ne_zero`); `zeroPoint` follows because `ν_∞` is a probability measure carried on
   `{x | nevBrealInf s x = 0}`, so that set is nonempty;
5. leaf/label covariance under an arbitrary normalization change, to upgrade
   `carrierProjector_eq_of_leaf_label_covariance`.
