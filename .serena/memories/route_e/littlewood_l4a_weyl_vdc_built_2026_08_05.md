# Littlewood L4a built: windowed Weyl–van der Corput (2026-08-05)

Card: `littlewood-zero-free-region.md` (L1 ✓ L2 ✓ L3 ✓ L4a ✓). Indexes regenerated (covers
KuzminLandau + WeylDifferencing).

`RHTower/Sieve/WeylDifferencing.lean` — wired, build 3274 jobs, axioms only
propext/Classical.choice/Quot.sound, zero warnings. Headline `weyl_vdc`:
for ‖a n‖ ≤ 1, 1 ≤ H ≤ N: `H·‖∑_{n<N} a n‖² ≤ 4N·(N + ∑_{h∈Icc 1 (H−1)} ‖weylCorr a N h‖)`
with `weylCorr a N h = ∑_{n<N−h} a(n+h)·conj(a n)` over FULL truncated ranges (what the Dk
induction consumes on smooth phases).

Design that worked: if-supported shifted windows (`weylShift r m = if r ≤ m < N+r then
a(m−r) else 0`) — NO fibre-pair combinatorics; window correlations collapse to Ico-filters +
`Finset.sum_Ico_eq_sum_range`; conjugation symmetry for r < r'; row bound by two explicit
`Finset.sum_bij'` reindexings (≤ 2·distance-indexed sum).

Lean traps: (1) `sq_sum_le_card_mul_sum_sq` lives in `Mathlib.Algebra.Order.Chebyshev` —
import explicitly; (2) omega cannot see through `max/min` if-normal-forms in bij'-value goals
— rewrite with `max_eq_left/right`, `min_eq_left/right` first; (3) `(mul_le_mul_left h).mp`
ambiguous — use `le_of_mul_le_mul_left`; (4) conj-of-conj: `RingHomInvPair.comp_apply_eq₂`
collapses starRingEnd² inside sums. Compiler caught a REAL math slip (row-lemma bijection
evaluated g at d+r instead of d) — the pre-verified paper doc + typechecker discipline works.

Next: L4b = (D2) second-derivative test (KuzminLandau + integer-crossing splitting over
Finset decompositions — the analytic wrapper: g' monotone/MVT per consecutive pair), then
L5 = (Dk) induction consuming weyl_vdc + D2 per `littlewood-l2-weyl-chain.md`.
