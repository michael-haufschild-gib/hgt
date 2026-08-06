# Jacobian hypothesis wired to the local different (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **54**.
Continues [[research/scheme_theorem_a_assembled_2026_08_06]].

## `SchemeJacobianOrder.lean`

- **`ord_eq_sub_one_of_addVal_eq`** — `Scheme.ord` of the image of a local element equals `e − 1`
  when its `addVal` does.  Direct from `ord_algebraMap_stalk_eq_addVal` (module 16).
- **`jacobian_order_of_addVal`** — pointwise version producing exactly the horizon theorem's `hjac`
  (`Scheme.ord J z = (e z : ℤ) − 1`).

## Why it was worth doing

Previous reports claimed "the Jacobian order is proved, not assumed".  That was true of the local
different computation (module 50) but the *link* to the divisor-level hypothesis was prose.  It is
now a Lean lemma, so the dependency claim is checkable.

## Honest status of Step 4 (recorded after a full re-examination)

Step 4's remaining content **cannot** be reduced further without positivity:

- The abstract shadow ("all eigenvalues of modulus > 1, λ a positive integer ⇒ λ > 1") is
  content-free.
- Locally `e > 1` ⟺ the extension is nontrivial (module 51), but nothing forces that globally.
- Module 35's counterexample shows the conclusion genuinely fails without it.
- The Riemann–Hurwitz route gives ramification *somewhere*, not on *every* horizon component.

So the requirement is intersection theory / `N¹`, which mathlib lacks entirely.  This is a
multi-iteration build, not a gap that can be argued away.

## Remaining for Theorem A

1. Step 4 globally: positivity (`N¹`, ample, intersection numbers) — the real blocker.
2. Sheaf of differentials on a scheme (presentation of `K_X = f^*K_X + R_f`).
3. Corollary B: MMP.
