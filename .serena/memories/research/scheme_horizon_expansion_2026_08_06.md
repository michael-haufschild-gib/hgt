# Scheme horizon under pointwise expansion (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **52**.
Continues [[research/ramification_expansion_criterion_2026_08_06]].

## `SchemeHorizonExpansion.lean`

- **`schemeEigenvolume_ordAt_eq_neg_one_of_expansion`** — the horizon is a reduced divisor.
- **`schemeEigenvolume_ordAt_ne_zero_iff_of_expansion`** — total invariance.

Both with `hram` (the cycle hypothesis) replaced by **pointwise expansion**
`∀ z, ordAt g z ≠ 0 → 1 < e z`, via `ramified_cycle_of_forall_one_lt` (module 51).

## Where Step 4 now stands

Theorem A's conclusions hold on a scheme given: the local order law (derived from the pullback law,
the different, and the eigenvolume condition — all proved), finiteness (proved), surjectivity of the
divisor map, and **ramification along every component of the horizon**.

That last item is the *entire* remaining content of Step 4, in its weakest sufficient form.  By the
local criterion (module 51) it is equivalent to the morphism not being an isomorphism there.  The
card reaches it via `N¹` and int-amplification; that machinery is a route, not the requirement.

## Remaining for Theorem A

1. Ramification along the horizon (Step 4, global) — the `N¹`/int-amplification route.
2. Sheaf of differentials on a scheme (presentation of `K_X = f^*K_X + R_f`; the coefficient
   identity is proved, modules 22–23).
3. Corollary B: MMP.
