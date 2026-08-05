# L5 (Dk) closed: k-th derivative test in Lean (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/PhaseCorrelation.lean` +
`formal/GaloisForLFunctions/RHTower/Sieve/KthDerivativeTest.lean` — wired, built (8697
jobs), axioms clean, zero warnings. Namespace `RHTower.Sieve`.

- `weylCorr_phase` : weylCorr of `n ↦ e(g(x₀+n))` = ∑_{n<N−h} e(g(x₀+n+h)−g(x₀+n)).
- `kth_derivative_test (k) (hk : 2 ≤ k) (G : ℕ → ℝ → ℝ) ...` : derivative chain
  `∀ i < k, HasDerivAt (G i) (G (i+1) x) x` on `Icc x₀ (x₀+(N−1:ℕ))`, `λ ≤ G k ≤ h·λ`,
  `0 < λ ≤ 1 ≤ h` (h IS a hypothesis here, unlike D2) ⟹
  ‖∑_{n<N} e(G 0(x₀+n))‖ ≤ 256(N·(h²λ)^{1/(2^k−2)} + N^{1−4/2^k}·λ^{−2/2^k})
  (rpow exponents literally `1 / ((2:ℝ)^k - 2)`, `1 - 4/(2:ℝ)^k`, `-(2/(2:ℝ)^k)`).

Proof: Nat.le_induction, generalizing G x₀ N lam hgrow. Base = second_derivative_test'.
Step: trivial branch h²λ ≥ 1 first; window H = min ⌈(h²λ)^{−e'/(1+e')}⌉₊ N in weyl_vdc;
difference phase Gd i x := G i (x+h') − G i x consumes IH at (h'λ, h) via MVT slope;
h'λ > 1 branch absorbed by (h²h'λ)^{e'} ≥ 1. Exponent identities: e'/(1+e') = 2e_{k+1},
2β' = 1+β, 2γ' = γ. Constants: √2052 ≤ 256 both cases; sqrt step via
‖S‖ = √(‖S‖²) ≤ √(Y²) = Y (Real.sqrt_sq), no sqrt-subadditivity needed.

## Lean traps (big-context arithmetic)
- `rw [pow_succ]` grabbed `hgrow^2` (rw uses FIRST match's instantiation for all rewrites).
  Pin: `rw [show ((2:ℝ)^(k+1)) = (2:ℝ)^k*2 from pow_succ 2 k]`.
- `set`-bound locals: linarith/nlinarith zeta-unfold the let-values (rpow towers) → simplex
  blew 1.6M heartbeats. Fix: `clear_value U V a H H₀ s B E β' γ' β γ e'` once all
  value-dependent proofs are done (hanorm needs a's value; min-lemmas need H's; prove
  H = ⌈H₀⌉₊ later via `rw [hHdef]; exact min_eq_left`), plus `linarith only [...]`
  everywhere. nlinarith → deterministic mul_le_mul/linarith-only where possible.
- Renames: `le_or_lt` → `le_or_gt`, `div_le_div_iff` → `div_le_div_iff₀`,
  `pow_le_pow_right₀`, `Real.sqrt_le_one` is an iff.
- After `rw [weylCorr_phase]`, goals equal up to let-bound difference-phase unfolding close
  by rw's rfl check — extra Finset.sum_congr steps then error "no goals".
- `set_option ... in` goes BEFORE the docstring.
- IH gets set-abstracted by `set e' := 1/((2:ℝ)^k−2)` etc. — set rewrites hypotheses too;
  exploit it so hIH arrives in e'/β/γ form.

## Next: (Z) dyadic assembly
g(x) = −(t/2π)log x on (N, 2N]: G i x := derivative chain of −(t/2π)log x (i-th:
±(t/2π)(i−1)!x^{−i}); λ = (t/2π)(k−1)!(2N)^{−k}, h = 2^k, (h²)^{e_k} ≤ 4. Abel 1/n
weights, per-block k-min vs trivial log 2, PNTPlus truncation → ζ(1+it) ≤ C·log t/loglog t
+ rectangle version. Then L6: Ford detector transfer (read-only PNTPlus imports).
