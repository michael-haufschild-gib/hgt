# Burnol stage-2 folder: five of nine cards promoted (2026-08-09)

Target was `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/burnol/` (9 cards).

## Promoted to stage 3 (paper card moved, companion written, ledger updated)

| Card | Lean |
|---|---|
| `burnol-divided-shift-evaluation-separation-law` | already formalized; verified only |
| `burnol-holonomy-cauchy-sector-separation` | already formalized; verified only |
| `burnol-all-prime-completion-singular-potential-entrance-wall` | **new**, all `(AW0)`–`(AW17)` |
| `burnol-all-prime-window-hilbert-cartier-jet-wall` | **new**, all `(HJ1)`–`(HJ29)` |
| `burnol-poisson-subordinate-smooth-cartier-entrance-wall` | **new**, all `(PS1)`–`(PS16)` |

Four cards remain in stage 2, each with a `## Lean formalization` table mapping equations to
declarations: `first-wall-cartier-residue-cancellation-law`,
`gamma-bockstein-first-wall-extraction-law`, `prime-two-causal-cartier-collar-law`,
`cofinite-cartier-wall-trace-horizon`.

## New Lean modules (all `RHTower/`, all umbrella-wired, axioms clean)

`BurnolPrimeLogSummability`, `BurnolAllPrimeCompletionWall`, `BurnolAllPrimeWindowEnergy`,
`BurnolReciprocalStokesSewing`, `BurnolPoissonSubordinateWall`, `BurnolGlasserIntegral`,
`BurnolGammaSteinCollarKernel`, `BurnolGammaSteinMoments`, `BurnolFirstWallResiduePolarization`,
`BurnolDyadicCoboundaryContraction`, `BurnolDyadicCommutatorStaircase`,
`BurnolPrimeCartierWallTrace`.

## What is still open (the real frontier)

- `first-wall-cartier-residue-cancellation`: tail/endpoint mass `(10)`–`(17)` of `g_ρ`,
  deep-profile limit `(29)`, `(30)`–`(31)`, Cor 5.
- `gamma-bockstein-first-wall-extraction`: `(13)`, `(15)`, `(16)`, `(22)`.
- `prime-two-causal-cartier-collar`: operator realization `(3)`/`(4)`, `γ̂ = Γ_ℝ` `(7)`, normal
  convergence `(11)`, `(18e)`–`(18g)`, crossing formula `(19)`, landings `(22)`, `(24)`.
- `cofinite-cartier-wall-trace-horizon`: cofinite radius law `(CH10)`, maximal-germ nonclosed range
  `(CH13)`–`(CH17)`.

**The first three all need the same missing object**: the actual zero-divided source
`g_ρ(t) = ∫_1^∞ u^{-ρ} f₀(ut) du` on the ray — its constant head `a_ρ = 1/(1-ρ)`, its `O(t^{-2})`
tail via the periodic mean-zero primitive of `p = {t} - {2t}`, and the aperture-crossing
correlation `W_G`.  Build that once and four card items close together.

For `(CH13)`–`(CH17)` the open-mapping theorem is **not** needed: take `u_p = 1/√p`, which is not in
`ℓ²` (Euler) while `∑_p p^{-1-2(σ-R)} < ∞` makes the finite truncations converge in every
compact-open seminorm.  Non-closedness is then a constructive statement about a sequence and its
limit, expressible without building the Fréchet space.

## Two traps hit

1. **`lake env lean` can pass against a stale olean set.**  `BurnolPoissonSubordinateWall` was clean
   per-file and then produced six errors under `lake build GaloisForLFunctions.RHTower`.  The
   umbrella build is the only real gate.
2. **Committed modules rot under a dependency rebuild.**  `HTGeometry/HalfLineCoshPrimitive.lean` is
   now **fixed** (AM-GM `nlinarith` replaced by the explicit `ε⁻¹(εe−|R|)²` identity, plus a
   `MeasureTheory.integral_const_mul` disambiguation).
   `RHTower/DeningerCriticalFloquetVonMangoldtWall.lean` is **still broken** (9 errors, lines
   976–1169, incl. unknown constant `intervalIntegral.integral_eq_zero`) — the only remaining
   RHTower umbrella failure, unrelated to the Burnol work.

## Technique notes worth reusing

- Every collar moment reduces to one master identity: substitute `z = C e^{-2u}` (Jacobian `2z`,
  `integral_image_eq_integral_abs_deriv_smul` with `s = univ`); the integrand becomes
  `e^{-z} z^{s-1}·cubic` and the answer is a Gamma combination.  No integration by parts.
- `field_simp` on a whole collar expression is very slow; factor the polynomial out as an opaque
  variable (`burnolCollarProfile_mul_mode (P u : ℝ)`).
- The Glasser integral: reciprocal involution `t ↦ b/t` equates the two halves; the Glasser map
  `t ↦ t - b/t` (explicit inverse `t = (v+√(v²+4b))/2`, strictly monotone) carries `(0,∞)` onto `ℝ`
  with `(t-b/t)² + 2b = t² + b²/t²`.  `integrableOn_image_iff_integrableOn_abs_deriv_smul` transfers
  integrability for free.
- Cofinite prime comparison: `Set.Finite.preimage Subtype.val_injective` for the small primes,
  `Summable.subtype`, then `Set.Finite.summable_compl_iff`.
- The corpus already owns the even-function reflection `lintegral_Iio_eq_lintegral_Ioi_neg`
  (`RHTower/EvenL2LogUnitary`); do not rebuild it.
