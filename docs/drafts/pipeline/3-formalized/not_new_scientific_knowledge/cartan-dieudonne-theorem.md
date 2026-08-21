# The Cartan–Dieudonné theorem

- **ID:** `cartan-dieudonne-theorem`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[CLASSICAL; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Cartan (1938), Dieudonné (1948), Scherk (1950); classical, absent from mathlib
- **Statement:** Let `K` be a field with `2 != 0`, let `V` be a finite-dimensional `K`-vector
  space of dimension `n`, and let `B` be a nondegenerate symmetric bilinear form on `V`.  Then
  every isometry of `(V, B)` is a composite of at most `n` reflections.

## The theorem

For `v` anisotropic (`B v v != 0`) the reflection in the hyperplane `v^perp` is

```text
tau_v(x) = x - (2 * B(x,v) / B(v,v)) * v.
```

`tau_v` is an involutive isometry.  The theorem: for every `f` with `B(f x, f y) = B(x,y)` there
are anisotropic `v_1, ..., v_k` with `k <= n` and `f = tau_{v_1} o ... o tau_{v_k}`.

Conversely every such composite is an isometry, so the statement is a characterization of the
orthogonal group `O(V,B)` as the set of words of length at most `n` in reflections.

## Proof architecture

Write `D = f - 1`, `gamma(x) = B(D x, x)`, `sigma(x,y) = -B(D x, D y)`.  For an isometry `f`,

```text
B(D x, y) + B(D y, x) = sigma(x,y),                                   (polar)
2 * gamma(x) = -B(D x, D x),                                          (square)
```

so `sigma` is the polar form of the quadratic form `gamma`, and "`range D` is totally isotropic"
is exactly "`gamma == 0`".  The whole proof stays inside `V`: no step passes to a subspace, so no
nondegeneracy of a restricted form is ever needed.

**Descent.**  If `gamma(v) != 0`, put `g = tau_{D v} o f`.  Then

```text
(g - 1)(y) = D(y - (B(D y, v)/gamma(v)) * v),
```

so `range(g-1) = D(H_v)` with `H_v = {x : B(D x, v) = 0}`, and `D v` lies in `range D` but not in
`D(H_v)`; hence `rank(g-1) < rank(f-1)`.  So one reflection buys exactly one unit of rank, provided
the non-isotropy hypothesis survives.

**Scherk's lemma (the crux).**  Suppose that for *every* `v` with `gamma(v) != 0` the form `gamma`
vanishes on the whole hyperplane `H_v`.  Then `range D = K * D v_0` is a single line.  Proof:

1. Fix `v_0` with `gamma(v_0) != 0`.  Then `gamma|H_{v_0} = 0`, hence `sigma|H_{v_0} x H_{v_0} = 0`.
2. If `sigma(z, -) == 0` then `D z = 0`.  Indeed for any `v` with `gamma(v) != 0`: if
   `B(D z, v) != 0` then `V = H_v (+) K z` and `gamma(h + t z) = gamma(h) + t sigma(h,z) +
   t^2 gamma(z) = 0` for all `h, t`, so `gamma == 0`, contradiction.  Hence `B(D z, v) = 0` for
   every anisotropic `v`; since one of `x`, `x + v_0`, `x - v_0` is anisotropic for every `x`
   (their `gamma`-values satisfy `gamma(x+v_0) + gamma(x-v_0) = 2 gamma(x) + 2 gamma(v_0)`), this
   gives `B(D z, x) = 0` for all `x`, so `D z = 0` by nondegeneracy.
3. If `a in H_{v_0}` and `sigma(a, v_0) = 0` then `sigma(a, -) == 0` (split `y = h + c v_0` with
   `h in H_{v_0}` and use 1), hence `D a = 0` by 2.
4. If some `a_0 in H_{v_0}` had `sigma(a_0, v_0) != 0`, then splitting an arbitrary `y` as
   `y = a' + d a_0 + c v_0` with `a' in H_{v_0}`, `sigma(a', v_0) = 0` shows
   `B(D a_0, y) = 0` for all `y` — using `B(D a_0, a') = sigma(a_0, a') - B(D a', a_0) = 0`,
   `B(D a_0, a_0) = gamma(a_0) = 0` and `B(D a_0, v_0) = 0` — so `D a_0 = 0` and therefore
   `sigma(a_0, v_0) = -B(D a_0, D v_0) = 0`, a contradiction.
5. Hence `D h = 0` for every `h in H_{v_0}` by 3, and `D x = c * D v_0` for all `x` by splitting.

**Scherk's theorem.**  If `range(f-1)` is not totally isotropic, `f` is a composite of at most
`r = rank(f-1)` reflections.  Induction on `r`: either the descent step can be taken with the
non-isotropy hypothesis preserved (case 1, rank drops by one), or the crux applies and
`range(f-1)` is a line, whence `tau_{D v_0} o f = 1` and `f` is a single reflection.

**Totally isotropic case.**  If `gamma == 0` and `f != 1`, then `sigma == 0`, so `D^2 = 0` and
`range D <= ker D`; rank-nullity gives `2r <= n`.  Also `r != 1`: a rank-one totally isotropic
displacement forces `D = 0`.  Pick `w` anisotropic (it exists, since a nondegenerate symmetric form
in characteristic `!= 2` is not alternating) and set `g = tau_w o f`.  Then
`(g-1)(w) = D w - 2 w`, so `gamma_g(w) = -2 B(w,w) != 0`, and `range(g-1) <= range D + K w` has
rank at most `r + 1`.  Scherk gives `g` as at most `r + 1` reflections, so `f` is at most `r + 2`,
and `r >= 2` with `2r <= n` gives `r + 2 <= n`.

## Gates

- [x] 0 -> 1 in-progress
- [x] 1 -> 2 fully-proven (paper proof above, dependency-closed)
- [x] 2 -> 3 formalized: `formal/GaloisForLFunctions/HTGeometry/CartanDieudonne.lean`

## 2026-08-21 Lean closure

`GaloisForLFunctions/HTGeometry/CartanDieudonne.lean` proves the theorem unconditionally.

- `reflect B v`, `reflect_apply`, `reflect_isom`, `reflect_reflect` — the reflection as a linear
  map, its formula, the isometry property (needs `B` symmetric and `B v v != 0`), and involutivity.
- `reflProd B l`, `IsReflProd B n f`, `IsReflProd.mono`, `IsReflProd.exists_list`,
  `reflProd_isom` — composites of reflections, the "at most `n` reflections" predicate, and the
  converse direction.
- `disp f = f - 1`, `cdGam B f x = B (disp f x) x`, `cdSig B f x y = -B (disp f x) (disp f y)`,
  with `cd_polar`, `cdSig_self`, `cd_disp_sq`, `cdGam_add`, `cdGam_sub` — the displacement calculus
  (`polar`) and (`square`) above.
- `cd_orth_of_rad`, `cd_disp_zero_of_rad`, `cd_sig_of_ker`, `cd_disp_zero_of_ker`, `cd_crux` —
  steps 1–5 of Scherk's lemma.
- `cd_disp_reflect` — the displacement of `tau_{D v} o f`.
- `cd_scherk` — Scherk's theorem, by induction on `finrank K (range (f - 1))`.
- `cartan_dieudonne` — the theorem: `IsReflProd B (finrank K V) f`.
- `cartan_dieudonne_list`, `isometry_iff_exists_reflProd`, `cartan_dieudonne_equiv`,
  `cartan_dieudonne_of_bilinForm` — restatements (list form, characterization form, linear
  equivalence form, and the form using mathlib's `BilinForm.IsSymm` / `BilinForm.Nondegenerate`).

Hypotheses are exactly those of the classical statement: `B` symmetric, `B` nondegenerate,
`(2 : K) != 0`, `FiniteDimensional K V`.  Axioms of every main theorem: `propext`,
`Classical.choice`, `Quot.sound`.

## Log
- 2026-08-21 — created directly at stage 3 (paper proof + Lean closure in one pass)
