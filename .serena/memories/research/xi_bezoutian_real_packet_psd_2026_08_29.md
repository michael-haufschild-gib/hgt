# BZ-1: separated real-packet PSD of the Bezoutian RH criterion — LEAN-PROVED (2026-08-29)

Card: `docs/drafts/pipeline/1-in-progress/xi-critical-kernel-separated-real-packet-positivity.md`.
Modules (both umbrella-wired, built via `lake build` 10904 jobs, all public theorems on
propext/Classical.choice/Quot.sound):
- `formal/GaloisForLFunctions/RHTower/XiCriticalKernelSeparatedRealPacketPositivity.lean`
  (real-ray analytic layer, 1136 lines)
- `formal/GaloisForLFunctions/RHTower/XiBezoutianSeparatedRealPacketPosSemidef.lean`
  (correlation + Gershgorin + matrix strata, 764 lines)

## The theorems

With Φ = thetaCuspFullSource, γ = C_u/C_l, R_u = πe⁴+logγ+12,
R_l = (2π)²e^{2e+8}+4log(8γ)+16, R₀ = xiRayPacketBase = R_u+R_l (≥ 256):
- `xiRayLogDeriv_le` / `xiRayLogDeriv_ge`: on the real Euler ray,
  (log b)/8 ≤ ξ'/ξ(1/2+b) ≤ log b + 1 for b ≥ R_l / R_u — proved purely from the theta
  bilateral-Laplace representation (no ζ, no Γ, no Euler product, no zeros).
- `posSemidef_criticalLogDerivKernel_separatedRealPacket` and
  `posSemidef_thetaTailFirstMomentBezoutian_separatedRealPacket` (+ `_packet_nodes` in the
  literal endpoint quantifier shape): for every packet x 0 ≥ R₀, x(m+1) ≥ R₀²·x m, every n,
  the matrices [criticalLogDerivKernel (x j) (x k)] and
  [thetaTailFirstMomentBezoutian (x j) (conj (x k))] are Matrix.PosSemidef.
  First ≥3-node (arbitrary-rank) unconditional stratum of
  `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`.

## Structural frame (reusable)

- At real nodes K₀(x,y) = (r(x)+r(y))/(x+y), K₀(x,x) = r(x)/x, and
  correlation = cosh(Δ log r/2)/cosh(Δ log β/2): 2×2 real minors ⟺ log r 1-Lipschitz in
  log β. Corpus's n≤2 theorems = the two monotonicities; corpus counterexample 1/(w−a) =
  Lipschitz violation. LOG-LIP conjecture (all real 2×2, RH-necessary, saturates at β→1/2
  where r ≈ (2+γ_E−log4π)·2β) recorded on card.
- Two-sided r ≍ log b is what makes rows summable; a constant lower bound is NOT enough
  (row sums grow like √log β_j).
- Correlation: log t/t antitone (a·log c ≤ c·log a via log ≤ x−1), 1+2d ≤ 4^d,
  ρ_d ≤ 32(2/R₀)^d; Gershgorin threshold 64q ≤ 1−q at q = 2/R₀ ≤ 1/128.

## Lean traps hit (new ones beyond the CP-1 list)

- Ambiguous names: TWO `integrable_exp_mul_thetaCuspFullSource` (RHTower strip version with
  |c|<1 vs HedenmalmThetaSource all-shift version) — with `open HedenmalmThetaSource` the
  wrong one can resolve; qualify explicitly.
- Many nested `set` bindings (let-vars) blow up whnf/linarith in a big theorem —
  `clear_value` after each `set` fixes it, but then typed `have h : X ≤ …  := lemma` breaks
  (no defeq); switch to `by rw [hXdef]; exact lemma`.
- `set_option maxHeartbeats … in` must come BEFORE the docstring, not between it and theorem.
- `integrableOn_const` now has two autoParam goals (μ s ≠ ⊤ and ‖C‖ₑ ≠ ⊤ named hC) — the
  second is discharged by `enorm_ne_top`.
- Beta-blocked rewrites in `setIntegral_congr_fun`/`IntegrableOn.congr_fun` pointwise goals:
  use `simp only [neg_mul]`-style, never bare `rw`.
- Unit-rate tail majorant `(X+u)e^{−ru} ≤ (X+1)e^{−u}` (r ≥ 2) turns every shifted half-line
  integral into stock `integral_exp_neg_Ioi` — no set-shift API needed.
- Matrix.PosSemidef is now Finsupp-based; build via
  `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` (Hermitian + ∀ c : n → ℂ vector form);
  extract via `.dotProduct_mulVec_nonneg`. Real symmetric entries: re = two real forms
  (dite-restricted ℕ-vectors + Fin.sum_univ_eq_sum_range), im = 0 by Finset.sum_comm +
  antisymmetry.
- `Real.log_le_log (hx : 0 < x) : x ≤ y → …` still exists; `le_div_iff₀`, `div_le_iff₀`,
  `div_le_div_iff₀`, `div_le_div_of_nonneg_left/right` are the current division-order names.

## Open next

Shrink R₀; LOG-LIP (would close all real 2×2 minors); n = 3 all-gap via the corpus's
`ThetaCuspTiltFluxThreeRealDeterminant` reduction; complex displaced packets (needs |L| off
the ray from the same theta representation); off-line quartet mass domination (zero-density,
heavy). Sibling memory: `research/theta_kernel_cp1_separated_packets_2026_08_29`.
