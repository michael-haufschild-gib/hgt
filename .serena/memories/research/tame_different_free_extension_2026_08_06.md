# The monic relation from Cayley–Hamilton (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **42**.
Continues [[research/tame_different_monogenic_final_2026_08_06]].

## `TameDifferentFreeExtension.lean`

- **`exists_monic_relation_of_free`** — in a finite free `A`-algebra `B` of rank `e`, every `x : B`
  satisfies a monic degree-`e` relation over `A`: the characteristic polynomial of
  `Algebra.lmul A B x`.  Key mathlib lemma: **`Algebra.aeval_self_charpoly_lmul`**
  (`Mathlib/LinearAlgebra/Charpoly/Basic.lean`) — the algebra-level Cayley–Hamilton, saves going
  through endomorphisms by hand.  Degree from `LinearMap.charpoly_natDegree`.
- **`exists_eisenstein_relation_of_free`** — that relation is Eisenstein at a uniformizer.
- **`exists_monic_relation_addVal_eval_derivative`** — its derivative has valuation `e − 1`.

## Why this matters

The whole different arc previously assumed a **monogenic presentation**.  It is now *produced*:
freeness of a finite torsion-free module over a DVR is automatic, so the only real hypotheses are
"finite extension of DVRs, rank = ramification index (totally ramified), tame".

**Honest caveat, kept in the docstring**: the quantity computed is the valuation of the derivative
of the *characteristic* polynomial.  That is the different exactly when the uniformizer generates
the extension (`B = A[x]`); otherwise it is the different times the conductor.  For a totally
ramified extension `B = A[x]` does hold, but proving it needs Nakayama plus the residue-field
computation — not yet done.

## Remaining for Theorem A

1. `B = A[x]` for totally ramified extensions (Nakayama + residue computation) — would upgrade
   "derivative of the charpoly" to "the different".
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
