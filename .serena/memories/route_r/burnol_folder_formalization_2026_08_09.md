# Burnol stage-2 folder: first Lean layer (2026-08-09)

Target: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/burnol/` (9 cards).

## Promoted to stage 3 (verified, clean axioms, umbrella-wired, companions written, ledger updated)

- `burnol-divided-shift-evaluation-separation-law` — `RHTower/BurnolDividedShiftEvaluationSeparation`
  (was already formalized; verification only).
- `burnol-holonomy-cauchy-sector-separation` — `RHTower/BurnolHolonomyCauchySectorSeparation`
  (was already formalized; verification only).
- `burnol-all-prime-completion-singular-potential-entrance-wall` — **new**, all of
  `(AW0)`–`(AW17)` including the sharp `ℓ²` wall in both directions and the multiplicity jet.

Six cards remain in stage 2, each now carrying a `## Lean formalization` table mapping equations to
declarations and naming exactly what is still open.

## New Lean modules (all `RHTower/`, all umbrella-wired, axioms clean)

`BurnolPrimeLogSummability`, `BurnolAllPrimeCompletionWall`, `BurnolGammaSteinCollarKernel`,
`BurnolGammaSteinMoments`, `BurnolFirstWallResiduePolarization`,
`BurnolDyadicCoboundaryContraction`, `BurnolDyadicCommutatorStaircase`,
`BurnolPrimeCartierWallTrace`, `BurnolReciprocalStokesSewing`, `BurnolPoissonSubordinateWall`.

## What is still open per card (the real frontier)

- card `first-wall-cartier-residue-cancellation`: tail/endpoint mass `(10)`–`(17)` of `g_ρ`,
  deep-profile limit `(29)`, `(30)`–`(31)`, Cor 5.
- card `gamma-bockstein-first-wall-extraction`: `(13)`, `(15)`, `(16)`, `(22)`.
- card `prime-two-causal-cartier-collar`: operator realization `(3)`/`(4)`, `γ̂ = Γ_ℝ` `(7)`,
  normal convergence `(11)`, `(18e)`–`(18g)`, crossing formula `(19)`, landings `(22)`, `(24)`.
- card `cofinite-cartier-wall-trace-horizon`: cofinite radius law `(CH10)`, maximal-germ
  nonclosed range `(CH13)`–`(CH17)`.
- card `all-prime-window-hilbert-cartier-jet-wall`: window norms `(HJ2)`, direct-sum membership
  `(HJ3)`, packaged `(HJ5)`.
- card `poisson-subordinate-smooth-cartier-entrance-wall`: Poisson subordination identity
  `(PS2)`/`(PS11)` (needs `∫₀^∞ e^{-t²-b²/t²} dt = (√π/2)e^{-2b}`), `(PS12)`–`(PS13)`.

The first three cards all need the same missing object: the actual zero-divided source `g_ρ` on the
ray, its constant head `a_ρ = 1/(1-ρ)`, its `O(t^{-2})` tail, and the aperture-crossing correlation
`W_G`.  Build that once and four card items close at the same time.

## Two traps hit

1. **`lake env lean` can pass against a stale olean set.**  `BurnolPoissonSubordinateWall` was clean
   per-file and then produced six errors under `lake build GaloisForLFunctions.RHTower`.  Treat the
   umbrella build as the only real gate (see `mem:rhtower_umbrella_collisions_2026_08_07b`).
2. **Committed modules rot under a dependency rebuild.**  Two blocked the RHTower umbrella,
   independent of this work.  `HTGeometry/HalfLineCoshPrimitive.lean` is now **fixed** (an AM-GM
   `nlinarith` replaced by the explicit `ε⁻¹(εe−|R|)²` identity, plus a
   `MeasureTheory.integral_const_mul` disambiguation).  `RHTower/DeningerCriticalFloquetVonMangoldtWall.lean`
   is **still broken** (9 errors around lines 976–1169, incl. unknown constant
   `intervalIntegral.integral_eq_zero` and two failed `change`s) — that is the only remaining
   RHTower umbrella failure.

## Technique notes worth reusing

- Every collar moment reduces to one master identity: substitute `z = C e^{-2u}` (Jacobian `2z`,
  `integral_image_eq_integral_abs_deriv_smul` with `s = univ`), then the integrand is
  `e^{-z} z^{s-1}·cubic` and the answer is a Gamma combination.  No integration by parts is needed
  for `(27)`/`(28)`.
- `field_simp` on the *whole* collar expression is very slow; factor the polynomial out as an
  opaque variable (`burnolCollarProfile_mul_mode (P u : ℝ)`) and the file compiles in seconds.
- The cofinite-comparison pattern for prime divergence: `Set.Finite.preimage Subtype.val_injective`
  for the small-prime set, `Summable.subtype`, then `Set.Finite.summable_compl_iff`.
- `∑_p 1/(p log²p) < ∞` is `burnolSummable_prime_one_div_mul_log_sq`, proved by the telescoping
  comparison `1/((n+1)log²(n+1)) ≤ 1/log n − 1/log(n+1)` — condensation does not apply because the
  integer function is not antitone at `n = 1`.
