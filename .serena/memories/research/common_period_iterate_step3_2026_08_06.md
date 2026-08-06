# Step 3's passage to an iterate (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Modules **32 and 33**.
Continues [[research/eigenvolume_pointwise_law_toric_derivation_2026_08_06]].

## `CommonPeriodIterate.lean` (32) — abstract, no AG deps

- `iterate_mul_eq_self` — a period is a period for every multiple (`Function.iterate_add_apply`).
  Depends on **`propext` only** — no choice.
- **`exists_common_period`** — a finite set of periodic points has one common period: the product
  of the individual periods, indexed over `Finset.attach` so the choice of period can depend on the
  membership proof.
- **`exists_iterate_fixing_support`** — combines it with
  `exists_pos_iterate_eq_self_of_backwardStable` and finiteness of the support.

## `SchemeHorizonIterate.lean` (33)

`exists_iterate_fixing_horizon` — on a quasi-compact integral Noetherian scheme there is a single
positive iterate fixing every component of the horizon.

## Why this mattered

The card's Step 3 ends "After a common iterate, every component is fixed."  The abstract
ramification system only produced periodicity **one component at a time**
(`exists_pos_iterate_eq_self_of_backwardStable`), so that sentence was the one part of Step 3 with
no formal counterpart.  It now has one.

## Lean note

`∀ x ∈ s, ∃ n, …` cannot be `choose`n into a plain function (the value depends on the membership
proof).  Indexing the product over `s.attach` and using `(hper x.1 x.2).choose` avoids the issue
entirely; `Finset.dvd_prod_of_mem _ (Finset.mem_attach s ⟨x, hx⟩)` then gives divisibility.

## Remaining for Theorem A

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
