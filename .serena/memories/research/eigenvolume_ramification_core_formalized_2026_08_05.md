# Stable-coframe log-CY card: combinatorial-arithmetic core closed in Lean (2026-08-05)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
Still stage 2 — gate 2 → 3 needs algebraic geometry that does not exist yet (see "next layer").

## New module

`GaloisForLFunctions/HTGeometry/EigenvolumeRamificationSystem.lean` (imports the pre-existing
`RamificationPoleFixedPoint.lean`).  Abstract system: a type `α` of primes, image map `F : α → α`,
ramification index `e : α → ℕ`, eigenvolume order `c : α → ℤ`, local law
`c x + 1 = e x * (c (F x) + 1)`.

Closed (all axiom-clean; only `propext`, `Classical.choice`, `Quot.sound`):

| Theorem A step | declaration |
|---|---|
| (10) preimage stability | `order_ne_zero_of_image_ne_zero`, `order_ne_zero_of_iterate_ne_zero` |
| iterated law | `shift_eq_prod_iterate`, `one_lt_prod_iterate_of_expanding` |
| step 3 backward orbits return | `exists_pos_iterate_eq_self_of_backwardStable` |
| step 4 on a cycle | `eigenvolumeOrder_eq_neg_one_of_periodic` |
| (2)+(5) reduced horizon | `eigenvolumeOrder_eq_neg_one` |
| (3) total invariance | `order_ne_zero_iff_image_ne_zero` |
| (4) étale off horizon | `ramificationIndex_eq_one_of_order_eq_zero` |
| (6) `R_f = f*D − D` | `ramificationCoefficient_eq_pullback_sub` |
| expansion necessary | `exists_nonexpanding_order_ne_neg_one` |
| finiteness necessary | `exists_infiniteSupport_order_ne_neg_one` |

## Two results that improve on the paper

1. **No iterate is needed.**  The card's step 3 says "after a common iterate every component is
   fixed".  Unnecessary: on a cycle of length `n`,
   `c + 1 = (∏_{k<n} e(F^[k] x)) · (c + 1)` with the product `> 1`, so `c = -1` directly for `f`
   itself.  `eigenvolumeOrder_eq_neg_one_of_periodic`.
2. **Both hypotheses are sharp.**  Drop expansion: `α = Unit`, `c ≡ 5`, `e ≡ 1` satisfies the law
   with finite support.  Drop finiteness: `α = ℕ`, `F n = n − 1`, `c n = 2^n − 1`,
   `e n = if n = 0 then 1 else 2` satisfies the law with expansion on the whole (infinite) support
   and `c 1 = 1 ≠ −1`.  The backward orbit never returns, so no cycle equation exists.

`ramificationIndex_eq_one_of_order_eq_zero` needs **only** the law — not surjectivity, finiteness
or expansion — because `c x = 0 ⟹ c (F x) = 0` is the contrapositive of preimage stability.
`order_ne_zero_of_image_ne_zero` likewise needs no lower bound on `e` (`e x * m = 1` in ℤ with
`e x : ℕ` already forces `e x = 1`).

## Next layer (what actually blocks stage 3)

Only the algebraic-geometric *inputs* to the abstract system remain:
- (7) `f^*Ω = det(A) Ω` from `f^*|W` being an automorphism of the coframe space;
- (8) the ramification-divisor pullback formula `c_E = e_E c_F + (e_E − 1)`;
- `e_E > 1` on recurrent components, from int-amplification acting on `N^1(X)`.

These need Weil divisors on a smooth projective variety, ramification divisors of finite
morphisms, and the Néron–Severi group with amplified pullback eigenvalues.  mathlib has
`AlgebraicGeometry/AlgebraicCycle` and `OrderOfVanishing.lean` but no ramification formula and no
`N^1`.  Corollary B (log canonicity, Moraga–Yanez–Yeong) is further out and needs MMP.

Do **not** re-derive the combinatorial layer; it is done and sharp.
