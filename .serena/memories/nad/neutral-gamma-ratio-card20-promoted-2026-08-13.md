# nad card 20 `neutral-gamma-ratio-full-differential-boundary-depth-law` — PROMOTED to stage 3 (2026-08-13)

## Key finding that changed the plan

The ledger's planned finish (`K_θ ⊆ g·ℂ[z]` for one nowhere-zero `g`, then
`hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial`) is **mathematically
impossible for any Γ-bearing class**: mathlib's `Complex.Gamma` encodes poles as zeros, so
`G_θ = Γ(s+iθ)/Γ(s)` vanishes on `-ℕ ∪ (-ℕ - iθ)` — infinitely many zeros — while `g·q` with `g`
nowhere zero has only finitely many.  Any class containing an actual Γ-ratio function is never
inside `g·ℂ[z]`.

## What was done instead (strictly stronger)

New module `HTGeometry/NeutralGammaRatioProjectiveBoundary.lean` (axiom-clean, wired into the
`GaloisForLFunctions.HTGeometry` umbrella at EOF):

- `neutralGammaRatio θ s = Γ(s+iθ)/Γ(s)`; `neutralGammaRatioRationalClass θ = {G_θ·p/q : q ≠ 0}`.
- `neutralGammaRatio_ne_zero` — no zeros in the open upper half-plane (θ ≥ 0).
- `exists_norm_gt_eval_ne_zero` — escape radius of a nonzero polynomial (via
  `Polynomial.finite_setOf_isRoot`, NOT `setOf_isRoot_finite` — that name does not exist).
- `tendstoLocallyUniformly_congr_eventually_local` — TLU transfers along sequences agreeing
  eventually **near each point** (the global-`x` congr in `PolynomialRecessionLocallyUniform` is
  not enough: at fixed k there are always bad z at height `-S k`).
- **`hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass`** (θ ≥ 0):
  normalization `(iT)^{-d}·G_θ(z+iT)⁻¹·∏_l q_l(z+iT)`, limits = cleared numerators
  `p_j·∏_{l≠j}q_l` leading coefficients at the common degree bound; identification holds
  eventually on every compact because the translated points escape both Γ pole lines and the
  finitely many denominator roots.
- **`neutralGammaRatio_twoStageBoundary_rationalClass`** — the unconditional two-stage capstone.

Proof-technique notes: `field_simp` alone closes the clearing identity (don't append `ring` —
"no goals"); avoid `rw` of `IS = (y+IS) - y` (rewrites occurrences inside the norm too — use
`calc` + `congr 1; ring`); `(y + I*(S k)).im = y.im + S k` is closed by plain `simp`.

## Boundary recorded

Realized class = single-`G_θ`-power rational stratum `G_θ·ℂ(s)`.  Mixed `G_θ^k` powers or `Ψ`-jets
would need vertical Tricomi–Erdélyi asymptotics (`G_θ(s) ~ s^{iθ}` on tubes) — NOT in mathlib (no
complex Stirling / no Hadamard).  Card promoted per folder standard; parent-literature audit stays
open as a research (non-Lean) gate.

Card + companion now in `docs/drafts/pipeline/3-formalized/nad/`.  Ledger row 20 updated.
