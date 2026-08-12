# Step 43: window optimality — the detection-delay dichotomy [LEAN-PROVED]

Module `formal/GaloisForLFunctions/HTGeometry/TuranMinorDetectionDelay.lean` (imports
TuranMinorNodeRefinementNonmonotone), wired via HTGeometry.lean EOF append. Both theorems audit
to [propext, Classical.choice, Quot.sound].

## Theorems

- `pair_minor_re_neg_at_index {w W} (hw)(him)(hW) (n)`: single off-line conjugate pair has
  `(n, n+2, n+1)` minor with negative real part at EVERY index — substitute `W ↦ wⁿW` in
  `pair_minor_re_neg`; shape bridge `rw [map_mul, map_pow]; ring`.
- `exists_offline_config_minors_nonneg_below_seven`: explicit unit-circle config — real atom 1
  (weight 14), pair (12±5i)/13 (weights 1±2i), conj-symmetric in atoms AND weights, all norms
  = 1, re > 0, off-line copy with nonzero weight — minors nonnegative for all n < 7
  (minor₀ = 3588/28561 etc.), n = 7 negative. Constant truncation windows cannot detect.

## The dichotomy (paper + numeric)

Pure-pair levels: bracket = Σaᵢ²sin²θᵢ + cross-cos terms; AM–GM (a²s₁² + b²s₂² ≥ 2ab·sin²(σ/2)
up to η-corrections) forces bracket > 0 at every index — no masking from pair-pair oscillation.
Level REAL atom: no diagonal penalty; bracket = b²sin²θ + 2cb·sin²(θ/2)cos(θ(n+2)+φ); tuned φ
gives delay N ≈ arc/θ ~ c₀/g. NUMERIC: N·g ≈ 5.7 constant for θ = π/8..π/256 (three orders) —
the 1/g factor of the step-39 window is attained at fixed masses. Exact instance found by
Fraction-arithmetic search; closed form: 2·minor_n = (2c/169)·2Re((−4−58i)·w^{n+1}) − 1000/169,
integer chain z_k = (−4−58i)(12+5i)^k, condition 7·Re(z_{n+1}) ≥ 125·13^{n+1} holds exactly for
n ≤ 6, fails n = 7.

## Lean tech

Gaussian-rational moment chain: hy_k : Wp·vv^k = ↑x_k + ↑y_k·I by recursion
(`rw [show Wp*vv^(k+1) = Wp*vv^k*vv by ring, hy_k, hvv]; push_cast; linear_combination
(5·y_k/13 : ℂ) * Complex.I_sq`). Uniform assembler `hMof : ∀ k x y M, Wp·vv^k = ↑x+↑y·I →
14+2x = M → (moment sum) = ↑M`. Case split `n = 0 ∨ … ∨ n = 6 := by omega` then
`rcases … <;> norm_num only [] <;> [rw…; …] <;> rw [← ofReal_pow, ← ofReal_mul, ← ofReal_sub,
ofReal_re] <;> norm_num`. Norm=1 from normSq: factor (‖v‖−1)(‖v‖+1) = 0 by nlinarith, rcases.

## Open stretch

Asymptotic 1/g family as exact Lean theorem needs trig-arc bounds (Real.cos interval lemmas) —
recorded, not the frontier. Frontier now: unconditional arithmetic supply — the supply mass
inequality for the actual ξ spectrum at concrete (X, δ) from corpus zero-counting/mass bounds.
Card: xic-order-one-growth-organ.md steps 39-43.
