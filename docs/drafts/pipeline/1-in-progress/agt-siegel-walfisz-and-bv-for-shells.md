# Siegel–Walfisz and Bombieri–Vinogradov for the shells

- **ID:** agt-sw-bv-shells
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, classical) → THEOREM (Lean)
- **Source:** AGT README §9 topic 2; card agt-arithmetic-gauge-theory-programme
- **Statement:** For the prime pair form with weights `a = Λ` on `Q`-rough integers and a finite Fourier
  kernel, `Σ_{q ≤ Q} φ(q)^{-1} |Σ_{χ mod q, χ ≠ χ₀} P(aχ, xχ)| ≪_{A,g} K N ‖x‖² (log K)^{-A}` for
  `Q ≤ √N`, `N ≤ K^{O(1)}`.

## Goal
Bombieri–Vinogradov for the shells: level of distribution `1/2` with arbitrary log saving. The large-
sieve half is formalized (`largeSieve_shellPart`); the missing half is Siegel–Walfisz for the twisted
prime sums `A_j(χ) = Σ_{k ≤ K} Λ(k) χ(k) k^{-it_j}` at conductors `≤ (log K)^B`.

## Plan (dependencies in corpus)
1. Uniform zero-free region for complex zeros: `L(β+iγ, χ) = 0`, `γ ≠ 0` or `χ` complex ⟹
   `β ≤ 1 − c/log(q(|γ|+3))`. Inputs: Mathlib `norm_LFunction_product_ge_one` (3-4-1),
   `Zeta23.ThmE.L_logDeriv_partial_fraction` (|t| ≥ 6, uniform), Landau lemma
   `RHTower.Sieve.neg_re_logDeriv_le`, growth `Zeta23.ThmE.LFunction_growth_right_uniform`.
   Small heights `|t| < 6`: Landau lemma at centre `2 + it` (same uniform growth bound).
2. Real zeros of real χ: `RHTower.siegel_zero_free` (Siegel, ineffective).
3. Log-derivative bound `|L'/L(s,χ)| ≪ log²(q(|t|+3))` on `σ ≥ 1 − c'/log(q(|t|+3))` away from the
   exceptional zero (partial fraction + zero count `RHTower.exists_uniform_localCount`).
4. Smoothed Siegel–Walfisz by contour shift (character Perron: `RHTower.smoothed_character_vonMangoldt_eq_perron_integral`,
   `RHTower.norm_integral_characterPerron_tails`), then unsmoothing.
5. Assembly: orthogonality `Σ_{χ mod q} |X(χ)|² ≤ φ(q)(N/q + 1)‖x‖²`, imprimitive reduction, dyadic large
   sieve (`largeSieve_primePairForm`), small conductors by step 4.

## Log
- 2026-10-30 — created; prerequisites surveyed (Siegel, Landau lemma, uniform growth/partial fraction,
  uniform local zero count, character Perron all present). Starting step 1.
