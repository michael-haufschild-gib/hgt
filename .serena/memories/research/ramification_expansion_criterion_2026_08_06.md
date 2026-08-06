# The expansion step in local form (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **51**.
Continues [[research/different_generator_valuation_2026_08_06]].

## `RamificationExpansionCriterion.lean`

- **`one_lt_ramificationIndex`** — for a totally ramified extension, `e = finrank`, so `1 < e` iff
  the extension is nontrivial.  Uses `finrank_eq_ramificationIndex` (module 48).
- **`ramified_cycle_of_forall_one_lt`** — pointwise expansion ⇒ the cycle hypothesis `hram`
  (take `k = 0`; a fixed point of an iterate already carries ramification there).
  **Depends on no axioms at all.**
- **`eigenvolumeOrder_eq_neg_one_of_forall_one_lt`** — the horizon theorem with `hram` replaced by
  pointwise expansion.

## What this clarifies about Step 4

The card derives `e_E > 1` from int-amplification via eigenvalues on `N¹`.  Locally, `e > 1` is
equivalent to the extension being nontrivial — so what Step 4 must supply globally is **that the
map is not an isomorphism along the horizon**, not expansion of eigenvalues as such.  The `N¹`
machinery is a route to that fact, not the fact itself.

## Repo hazard

`lake build` of the umbrella can block for minutes when a concurrent agent holds the lake lock; a
10-minute tool timeout can fire on a build that normally takes ~10 s.  Re-run rather than assuming
breakage.

## Remaining for Theorem A

1. Sheaf of differentials on a scheme (presentation of `K_X = f^*K_X + R_f`; the coefficient
   identity itself is already proved, modules 22–23).
2. Step 4 globally: that the map is not an isomorphism along the horizon (`N¹` route).
3. Corollary B: MMP.
