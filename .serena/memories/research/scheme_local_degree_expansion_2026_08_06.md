# Expansion from the local degree (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **55**.
Continues [[research/scheme_jacobian_order_wiring_2026_08_06]].

## `SchemeLocalDegreeExpansion.lean`

**`one_lt_ramification_of_one_lt_finrank`** — at a codimension-one point of a scheme, with the
stalk extension a DVR extension of trivial residue extension, `1 < e` follows from
`1 < Module.finrank (stalk (f z)) (stalk z)`.  It is `one_lt_ramificationIndex` (module 51)
instantiated at the stalks, with the `Algebra` structure taken as an instance argument (supplied by
the caller from `f.stalkMap z`).

## Dimension split for Step 4 (the useful conclusion)

- **Dimension one: Step 4 is complete.**  A finite morphism of degree `d > 1` has local degree `d`
  at a totally invariant point, so `e = d > 1` by `finrank_eq_ramificationIndex` (module 48).
- **Dimension ≥ 2:** the local degree has to be produced from positivity — `[E] ≠ 0` in `N¹`
  requires intersection numbers against an ample class.  mathlib has none of this.

So the card's residual dependency is precisely: intersection theory / `N¹` in dimension ≥ 2.

## Repo hazards seen this round

- A background `lake build` killed mid-write left a **missing `.olean`** for an unrelated module
  (`LocalExtensionChartProbeSupportOpenness`), which surfaced as
  `failed to open file … .olean: No such file or directory` on a *different* file's import.
  Fix: rebuild that module explicitly, then the umbrella.  Do not assume source breakage.
- Umbrella builds contend with a concurrent agent's `lake` lock; a 10-minute timeout can fire on a
  build that normally takes ~7 s.

## Remaining for Theorem A

1. Step 4 in dimension ≥ 2: positivity (`N¹`, ample, intersection numbers).
2. Sheaf of differentials on a scheme (presentation of `K_X = f^*K_X + R_f`).
3. Corollary B: MMP.
