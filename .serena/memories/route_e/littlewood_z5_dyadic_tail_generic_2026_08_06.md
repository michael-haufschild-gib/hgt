# Littlewood Z5: dyadic tail off the line + generic assembly (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaTail.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `norm_sum_Ico_dyadic_of_blockBound {E} [NormedAddCommGroup E] (A R) (f) (b)` :
  `(∀ r < R, ‖∑_{Ico (A2^r) (A2^{r+1})} f‖ ≤ b r) ⟹ ‖∑_{Ico A (A2^R)} f‖ ≤ ∑_{r<R} b r`.
  **Generic in the summand** — the dyadic assembly never inspects it.
  `dirichlet_tail_dyadic_of_blockBound` is now visibly the `n^{−1−It}` instance.
- `dirichlet_tail_sigma_dyadic_le` :
  `‖∑_{Ico A (A2^R)} n^{−σ−It}‖ ≤ ∑_{r<R} 2560·(A2^r)^{1−σ}·(A2^r)^{−1/(3·2^{k r})}`.

## Running pattern for the σ version

Three theorems + three corollaries so far, reusing the schedule and the dyadic assembly unchanged.
**Everything in the chain concerning the phase is σ-free; only weight-carrying statements need
analogues.** Expect head/tail split, two-regime, uniform tail, threshold to be similarly cheap —
the only genuinely new work is the harmonic head `∑ n^{−σ}` in place of `∑ 1/n`.

## Remaining for Z5

Head/tail split (needs `∑_{n<A} n^{−σ}` bound — check `Sieve/ZetaTruncated.sum_rpow_neg_le_harmonic`,
which gives `∑ k^{−σ} ≤ 1 + log N` for `σ ≥ 1`; for `σ < 1` a different bound is needed),
two-regime, uniform tail, threshold. Then the Landau/3-4-1 pipeline.
