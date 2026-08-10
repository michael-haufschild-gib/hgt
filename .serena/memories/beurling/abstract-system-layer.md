# Abstract Beurling generalized prime system — new corpus layer

Started 2026-08-10 for the card
`docs/drafts/pipeline/2-fully-proven/route-e-beurling-local-axiom-firewall.md` (still stage 2 —
items 4, 5, 7 of that card remain; the card's "Lean progress" section is the authoritative state).

## What now exists

`RHTower/BeurlingSystemGibbsGauge.lean`
- `structure BeurlingSystem` — `Label : Type`, `labelNorm : Label → ℝ`, `1 < labelNorm p`.
  Generalized integers are `Multiset Label` (the free commutative monoid), `intNorm` is the
  multiplicative norm, `moebius` the generalized Möbius function (needs `open scoped Classical in`
  on the definition **and** on every lemma that mentions the `if`).
- `gibbsWeight_mul_le` / `gibbsWeight_mul_lt` — log-submodularity of `exp(-x ∏|p|)`, strict in
  transverse directions.  No such inequality existed anywhere in the corpus before.
- `log_labelNorm_div_log_intNorm_replicate`, `gammaGauge`, `gammaGauge_mem_Icc_of_truncate`.

`RHTower/BeurlingSystemCounting.lean`
- `IsDiscrete`, `countBall`, `HasLinearCounting`, and `summable_expNegNorm`: linear counting ⟹
  absolute convergence of `∑_g exp(-x |g|)`, by unit-norm layers vs a geometric series.

## Audit findings worth keeping

- The corpus's only prior generalized-prime layer is
  `HTGeometry/ConstraintRelativity/GeneralizedPrimeCountermodel.lean`, which models grades as a
  **free abelian group** `ι →₀ ℤ` with `gradeNorm` — a different object for a different card; it
  has no monoid of generalized integers, no counting function, no Möbius.
- No generalized Möbius on a free commutative monoid, and no log-submodularity, existed anywhere.
- For the future `(BF16)` Mellin step, `RHTower/SalemFermiModeIntegral.lean` already has the
  **generic real-frequency** bridge `mellin … s = Γ(s) * Σ a n / (p n)^s`; do not rebuild it from
  the ℕ-indexed `HTGeometry/BoundedCoefficientLaplaceMellin.lean`.

## Lean traps hit

- `Finset.one_le_prod'` / `Finset.single_le_prod'` need `MulLeftMono`, which ℝ does **not** have.
  For real products use `Finset.prod_le_prod` with `f = fun _ => 1`, and `Finset.prod_erase_mul`
  for the strict version.
- `Set.ncard_coe_Finset` does not exist in this mathlib; convert with
  `Set.ncard_eq_toFinset_card _ hfinite` and then `Finset.card_le_card`.
- `summable_of_sum_le` cannot infer its bound `c` from a later `calc`; pass `(c := …)` explicitly.
