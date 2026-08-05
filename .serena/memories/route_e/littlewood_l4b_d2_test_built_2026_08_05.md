# L4b closed: the (D2) second-derivative test in Lean (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/SecondDerivativeTest.lean` — wired, built (8694
jobs), axioms clean, zero warnings. Namespace `RHTower.Sieve`.

- `regionIdx δ y = ⌊y−δ⌋ + ⌊y+δ⌋` (noncomputable), `regionIdx_mono`,
  `regionIdx_diff_le : (idx y' − idx y : ℝ) ≤ 2(y'−y)+2`,
  `regionIdx_even_band : idx = m+m → y ∈ [m+δ, m+1−δ]`,
  `regionIdx_odd_gap : idx = 2m+1 → y ∈ [m+1−δ, m+1+δ)` (needs 0 ≤ δ, 2δ ≤ 1).
- `second_derivative_test` : λ ≤ g'' ≤ h·λ on `Icc x₀ (x₀+(N−1:ℕ))`, 0 < λ ≤ 1, 1 ≤ N ⟹
  ‖∑_{n<N} e(g(x₀+n))‖ ≤ (2Nhλ+3)(3/√λ+1). Hypotheses: HasDerivAt g/g' pointwise on span.
- `second_derivative_test'` : expanded ‖S‖ ≤ 8Nh√λ + 12/√λ. `1 ≤ h` derived, not assumed.

Proof shape: δ = √λ/2; K n := regionIdx δ (g'(x₀+n)) monotone (MVT slope ⟹ MonotoneOn g');
fibre split by `MonotoneFibers`; even fibre → `kuzminLandau_interval` (band transferred to
whole run by monotonicity from the two fibre-endpoint samples); odd fibre → card ≤ 2δ/λ+1
from MVT slope across the width-2δ gap; count via `card_image_le_of_monotone`.

## Lean traps
- `Real.sqrt_le_one` is an iff now: `.mpr hlam1`.
- Floor-based `def` needs `noncomputable` (linarith… linearOrder noncomputable).
- NEVER `rw [← hsqsq]` (hsqsq : √λ*√λ = λ) when goal contains `Real.sqrt lam` — it rewrites
  the `lam` inside the sqrt. Use `linear_combination c * hsqsq`.
- Avoid deprecated `lt_div_iff/le_div_iff`: go inv-form — `rw [div_eq_mul_inv]`,
  `mul_inv_cancel₀ h.ne'`, then `nlinarith [product facts]`.
- `Int.lt_floor_add_one` + `rw [hfloor_eq] at` needs no push_cast after (cast is already ↑m).
- omega closes ℤ-goals with opaque atoms (regionIdx applications) fine.

## Next: L5 — (Dk) induction
Consumes `weyl_vdc` (WeylDifferencing) + `second_derivative_test'`. Statement per
`docs/drafts/pipeline/1-in-progress/littlewood-l2-weyl-chain.md`: A_k ≤ 256,
e_k = 1/(2^k−2), bound A_k·(N·(h²λ)^{e_k} + N^{1−2^{2−k}}·λ^{−2^{1−k}}), induction step via
weyl_vdc with window H := ⌈(h²λ)^{−e'/(1+e')}⌉ ⊓ N, trivial branch when h²λ > 1
(‖S‖ ≤ N always), difference phase Δ_r g has second derivative in [rλ_3-ish…] — see the
card for exact bookkeeping. Then (Z) dyadic assembly, then L6 Ford-detector region transfer.
