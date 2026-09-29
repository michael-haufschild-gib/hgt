# Mertens mean-square and EDQ first-tail exponent laws

- **ID:** MC-RECEIVER-MSQ-EDQ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycles 120 and 126
- **Statement:** For `c ≥ 1` with `c ≠ 2Θ+1`, `Σ_{k≤X} M(k)² = O(X^c)` iff `2Θ+1 < c`. For `a ≥ 0` with `1+a ≠ 2Θ`, the fixed-start EDQ first-tail energy `I(N) = Σ_{N<n≤2N}(M(n)−M(N))²/(n(n+1))` is `O(N^a)` iff `2Θ < 1+a`.

## Lean
- `RHTower.exists_sum_sq_shiftedMertens_le_rpow_iff`, `zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le`, `finiteMobiusGammaHankelEnergy_le_mertens` (module `RHTower/MobiusMertensMeanSquareExponentLaw.lean`).
- `RHTower.DeletionFirstTail.exists_incrementEnergy_le_rpow_iff`, `exists_sum_sq_mertens_le_of_incrementEnergy_le`, `zetaZeroAbscissa_le_of_incrementEnergy_le` (module `RHTower/EulerDeletionFirstTailExponentLaw.lean`).
- Axioms: propext, Classical.choice, Quot.sound. Both are wired into `RHTower.lean`, and `lake build --old` passes (about 70 s each).

## Proof mechanism
1. **Energy bound.** The Abel form of the Laplace pencil and weighted Cauchy–Schwarz give `E_N(r) ≤ 2Γ(r)M(N)²(2N)^{−r} + 2Γ(r+1)Σ_{k<N}M(k+1)²(k+1)^{−r−1}`.
2. **Summation.** Abel summation together with `u^{−p} − (u+1)^{−p} ≤ p u^{−p−1}` (Bernoulli) bounds the weighted sum for `r > c−1`.
3. **Cutoff choice.** Every dyadic block contains a cutoff with small `M(N)`, so `E_N(r)` is bounded for infinitely many `N`. Fatou and the closed-half-plane criterion then exclude zeros with `Re ρ ≥ r/2`.
4. **EDQ tail.** Anchor chain `N_{k+1} ∈ (3N_k/2, 2N_k]` with averaged increments. This gives `|M(N_k)| ≪ N_k^{(a+1)/2}`, block mean squares `≪ N_k^{a+2}`, and a geometric cover of the line.

## Consequence
The first EDQ block, listed as an open carrier in the frontier map, is a receiver. A cutoff-uniform subpower bound on it is exactly RH, and a bound `O(N^a)` is exactly the zero-free half-plane `Re s > (1+a)/2` (STATUS MUST-525).

## Log
- 2026-09-29: formalized and wired.
