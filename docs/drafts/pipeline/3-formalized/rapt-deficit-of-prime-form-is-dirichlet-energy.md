# The deficit of the prime form is a Dirichlet energy

- **ID:** rapt-deficit-of-prime-form-is-dirichlet-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continues `rapt-valuation-tower-exactly-solvable` (class-span gap) and RAPT `ThePoleIsTheTopOfThePrimeForm` (sharp counterterm); ground-state transform of ACT/ALG's Metzler identity.
- **Statement:**
  1. For all `N`, `x`: `P_N(x) + D_N(x) = Σ_{n ≤ N} (A(⌊N/n⌋) + log n) x_n²`, where
     `D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` and `A(y) = Σ_{t ≤ y} Λ(t)/t`.
  2. For all `N`, `x`: `Σ_n (n/N) log n · x_n² ≤ 2 D_N(x) + 2(log 4 + 4)|x|²`.
  3. For every `ε > 0`, eventually: `P_N(x) + (1 − ε) D_N(x) ≤ (log N − γ + ε)|x|²`.
  4. For every prime `p` and `ε > 0`, eventually: if `x` is orthogonal on every `p`-ladder `{u p^j}`
     to `(p^{−j/2})_j`, then `P_N(x) ≤ (log N − γ − (1 + 1/p) log p + ε)|x|²`.

## Proof

1. Pole-gauge (ground-state) identity: expand `Λ(t)(x_{mt} − x_m/√t)²`; `Σ_{t∣n} Λ(t) = log n` collects
   the `x_{mt}²` terms, `Σ_{t ≤ N/m} Λ(t)/t = A(⌊N/m⌋)` the `x_m²` terms, and the cross terms are
   `P_N(x) = 2 Σ Λ(t) t^{−1/2} x_m x_{mt}`.
2. `log n · x_n² = Σ_{t∣n} Λ(t) x_n²`, `x_{mt}² ≤ 2(x_{mt} − x_m/√t)² + 2x_m²/t`, `mt/N ≤ 1`; the
   remainder is `Σ_m (m/N) ψ(⌊N/m⌋) x_m² ≤ (log 4 + 4)|x|²`.
3. Rows with `⌊N/n⌋ ≥ Q`: Mertens. Rows with `⌊N/n⌋ < Q` exceed `log N − γ + ε/2` by at most
   `A(Q) + γ ≤ θ (n/N) log n` once `log(N/Q) ≥ Q(A(Q) + γ)/θ`; by 2 these atoms cost `θ(2D + 2C|x|²)`.
   `θ = ε/(4(log 4 + 4) + 2)`.
4. The `p`-power edges of `D_N` are `log p · E_p(x)`, `E_p = Σ_{m p^k ≤ N}(x_{mp^k} − p^{−k/2}x_m)²`. Split
   `[1, N]` into `p`-ladders (`n = u p^j`, `p ∤ u`). On a ladder `(x_{l} − p^{−(l−j)/2}x_j)² ≥
   (p^{−j/2}x_l − p^{−l/2}x_j)²`, and Lagrange's identity sums these minors to `|b|²|x|² − ⟨b, x⟩²`,
   `|b|² = Σ_{j ≤ J} p^{−j} ≥ 1 + 1/p` when the ladder has two rungs (a one-rung ladder is killed by
   orthogonality). Then 3.

## Significance

- The sharp counterterm no longer needs the tilted Collatz–Wielandt vector: the deficit
  `(log N − γ)|x|² − P_N(x)` is, up to `ε`, the Dirichlet energy of the multiplicative random walk in
  the pole gauge, and that energy itself pays the top rows.
- First all-vector spectral gap below the pole: for each prime, on `V_p^⊥` (complement of the
  ladder poles, codimension = number of `p`-free `u ≤ N`) the top drops by `(1 + 1/p) log p`
  (`1.5 log 2` at `p = 2`; numerically the true value is `2 log 2`, attained by the 2-adic valuation
  step). The class-span Hodge index (`rapt-matched-prime-place-hodge-index-on-classes`) is now global.
- Reduction of the full gap (C4): `P_N ≤ log N − γ + ε − c(1 − Π_pole)` follows from a Poincaré
  inequality `D_N(x) ≥ c·dist²(x, ℝ·pole)` for the multiplicative walk (measure `1/n`, edges
  `(m, mt)` weighted `Λ(t)/(mt)`). Numerics: its gap is 1.241, 1.255, 1.266, 1.276 at
  N = 500, 1000, 2000, 4000 (→ `2 log 2`); with prime edges only (no prime powers) the gap decays
  (0.14 → 0.11), so the prime-power edges `Λ(p^k) = log p` are essential.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheDeficitOfThePrimeFormIsADirichletEnergy.lean`
(`poleDefect`, `atomicWeilForm_eq_edges`, `sum_edges_eq_sum_divisors`, `atomicWeilForm_add_poleDefect`,
`sum_top_le_poleDefect`, `eventually_atomicWeilForm_add_poleDefect_le`, `sum_Icc_eq_sum_ladders`,
`ladderDefect`, `log_mul_ladderDefect_le`, `sum_sum_minor_sq`, `sum_Icc_shift`,
`sum_ladder_sq_le_of_orthogonal`, `ladderDefect_ge`, `eventually_atomicWeilForm_le_of_ladderOrthogonal`).
Clean exact-file check; axioms `propext, Classical.choice, Quot.sound`; wired in the RAPT umbrella.

Open: the Poincaré inequality for the multiplicative walk (C4); the sharp per-prime gap
`p log p/(p − 1)` on `V_p^⊥` (long ladders give it; short top ladders limit the proof to `1 + 1/p`).
