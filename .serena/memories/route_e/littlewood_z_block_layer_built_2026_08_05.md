# (Z) block layer built: Z1 log-phase + Z2 Abel (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/LogPhaseBlock.lean` and
`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockAbel.lean` — wired, built, axioms
clean, zero warnings. Namespace `RHTower.Sieve`.

Key theorems:
- `dirichlet_block_bound` : k ≥ 2, λ = (t/2π)(k−1)!/(2N)^k ≤ 1, N+L ≤ 2N+1 ⟹
  ‖∑_{j<L} ((N+j:ℕ):ℂ)^(−(I·t))‖ ≤ 256(L·(4^kλ)^{1/(2^k−2)} + L^{1−4/2^k}·λ^{−2/2^k}).
- `abel_block_bound` : decreasing nonneg weight w, all prefixes ‖∑_{Ico N m} a‖ ≤ P ⟹
  ‖∑_{Ico N M} (↑(w n))·a n‖ ≤ P·w N.
- `dirichlet_block_one_full` : N ≤ M ≤ 2N+1 ⟹ ‖∑_{Ico N M} n^(−1−It)‖ ≤ (same RHS with
  L := M−N)·(N:ℝ)⁻¹.
- `natCast_cpow_neg_I_mul` : (n:ℂ)^(−(I·t)) = exp(↑(2π·logPhase t n)·I), logPhase t =
  −(t/2π)·log. `norm_phase_sum_neg` handles odd k by conjugation.

## Lean notes
- logPhaseChain: chain via (x^{i+1})⁻¹ (npow-inv, NOT zpow) — HasDerivAt.inv on
  hasDerivAt_pow; factorial recursion by `Nat.factorial_succ` + field_simp + ring.
- (−1)^k parity: Even.neg_one_pow/Odd.neg_one_pow; sign-squared collapse via
  `linear_combination c * hsq` with hsq : (−1)^{j+1}·(−1)^{j+1} = 1 (pow_add + Even).
- `Finset.sum_range_sub'` instantiated at an explicit lambda arrives ALREADY beta-reduced
  (simp only [] then errors "no progress").
- Lean auto-closed the cast goal (↑n)⁻¹ = ↑((↑n)⁻¹) only via push_cast (norm_cast/congr
  left an e_a goal behind — congr 1 on `a*b = c*b` can produce hidden second goals).
- inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹ (inv_le_inv_of_le is GONE).
- Complex.cpow_add (y z) (hx : x ≠ 0); Complex.cpow_neg_one; Complex.ofReal_log needs
  0 ≤ x and the ℕ→ℂ vs ℕ→ℝ→ℂ cast must be aligned first (norm_cast).

## Next: Z3 schedule (the analytic assembly)
Head: ∑_{n≤X₀} 1/n ≤ log X₀ + 1 (check corpus Mertens/harmonic assets first!).
Tail: dyadic blocks N ≥ X₀ = t^{1/m}, m ≈ loglog t; per block k(N) with N^{k−1} ≤ t-ish;
CARE: the k-schedule must keep BOTH (i) λ ≤ 1 — the factorial gate (k−1)! ≤ 2π2^k·(spare
power of N), and (ii) term2 small — needs t²N^{4−2k} ≥ N-ish, i.e. do NOT overshoot k by
a full unit: use branch t ≶ N^{k₀−1/2} choosing k₀ or k₀+1 (k₀ = ⌊log t/log N⌋+1).
Per-tail-block target: ≤ C·exp(−c·log N/2^k) ≤ 1/log t; total tail O(1).
Z4: truncation via PNTPlus Zeta0EqZeta/riemannZeta0_apply at s = 1+it (read-only imports).
Z5: rectangle σ-version reuses abel_block_bound with w n = n^{−σ}.
