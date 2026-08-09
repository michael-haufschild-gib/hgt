# Van Kampen area / Heisenberg / reduced-word Lean layer (ULF-FILL-1)

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling`
(wired into `HTGeometry.UniversalLawField`). Card promoted to Stage 3.

## New corpus-owned infrastructure (mathlib has NONE of it)

- `Heis` — integer Heisenberg group `ℤ³`, `(x,y,z)(x',y',z') = (x+x',y+y',z+z'+x y')`, with
  `Group` instance, `Heis.center m = ⟨0,0,m⟩`, `center_mul`, `center_comm`, `conj_center`,
  `center_injective`, `center_inv`.
- Van Kampen fillings over `FreeGroup (Fin 2)`: `cellWord`, `IsFilling`, `Fillable`, `area`
  (= `sInf {k | Fillable k w}`), with `isFilling_append/conj/inv`, `Fillable.mono/conj/inv`,
  `area_le`, `fillable_area`, `area_inv`.
- `comm x y = x y x⁻¹ y⁻¹` plus `comm_mul_left`, `comm_mul_right` (both by the `group` tactic).
- Reduced-word criterion: `NoCancel`, `reduce_eq_self_of_isChain`, `isChain_replicate_append`,
  `head?_replicate_append`, `mk_replicate`.
- Headline: `area_nullWord : area (aⁿbⁿa⁻ⁿb⁻ⁿ) = n²`, `length_nullWord = 4n`.

## Method notes

- **Dehn lower bound via a central representation**, not lattice area: map `F₂ → Heis` with the
  relator hitting a *central* generator. Conjugation is then invisible, so a `k`-cell filling has
  central exponent ≤ k in absolute value. This kills the whole "signed area changes by ±1"
  bookkeeping.
- Products in a *noncommutative* group must be `List.prod` of `List.ofFn`/`List.map`, never
  `Finset.prod` (which needs `CommMonoid`). Filling cells are therefore a `List`.
- `List.Chain'` is **deprecated → `List.IsChain`**; the useful lemmas are `List.isChain_append`,
  `List.isChain_cons`, `List.isChain_nil`, `List.isChain_singleton`. There is no
  `isChain_replicate` or `isChain_cons'` — build them.
- To prove a concrete block word is reduced, right-nest the appends and use a
  `replicate x ++ L` induction; that handles `n = 0` uniformly and avoids `getLast?` entirely.
- `abs_add` is now `abs_add_le`. `FreeGroup.reduce.cons` is stated with `List.casesOn`, so
  `rw [reduce.cons, ih]` then `cases tl` then `if_neg` closes the reducedness induction.
- `open FreeGroup` shadows `map_mul` with `FreeGroup.map_mul`; use `_root_.map_mul` or don't open.
- Commutator notation `⁅x,y⁆` did not resolve a `Bracket` instance for `FreeGroup`; define `comm`
  explicitly instead.
