# Mapping-cone exactness built (removes the last hypothesis from ROD.10/ROD.11)

Module: `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RelativeConeExactness.lean`
(wired into `GaloisForLFunctions.HTGeometry`; umbrella build green).

Card: `docs/drafts/pipeline/3-formalized/constraint-relativity/relative-law-observer-descent-duality.md`
Its companion previously admitted that `relativeLawEquiv` took the mapping-cone long exact sequence
as INPUT exactness (`range g = ker π`, `range π = ker f`).  That is now PROVED.

## What was built (all from scratch — no category-theory machinery)
- `ZCochain k M` — a `ℤ`-graded cochain complex of `k`-vector spaces (`M : ℤ → Type*`,
  `d : ∀ n, M n →ₗ M (n+1)`, `d_squared`).
  KEY TRICK: index cohomology by the LOWER degree, `H n := ker (d (n+1)) ⧸ range (d n)`.
  This removes EVERY dependent-index cast (`n-1+1 = n` is never needed) and, unlike the corpus's
  ℕ-indexed `DeningerCochainComplex` (`HTGeometry/CochainComplexCohomology.lean`, which sets
  `coboundaries 0 = ⊥`), it is valid in every degree — the ℕ version's shift `H^j(C[1]) = H^{j+1}(C)`
  FAILS at `j = 0`, so the cone LES cannot be stated there.
- `ZCochainMap`, `cocyclesMap`, `cohomologyMap`.
- `coneComplex Φ` — `Cone(Φ)ⁿ = Xⁿ ⊕ Cⁿ⁺¹`, `d(x,c) = (d_X x − Φ c, −d_C c)`; `d² = 0` is exactly
  the chain-map identity.  `coneInc` (`X → Cone`), `conePr` (`Hⁿ(Cone) → Hⁿ⁺¹(C)`).
- `cone_exact_left`, `cone_exact_right` — exactness of
  `Hⁿ(X) → Hⁿ(Cone Φ) → Hⁿ⁺¹(C) → Hⁿ⁺¹(X)` at both middle terms.
  Witnesses: for the left one, a class killed by `conePr` has `c = d_C b`, and subtracting
  `d_Cone (0, b)` puts the cocycle in the image of `coneInc`; for the right one, `Φ c = d_X x`
  makes `(x, c)` a cone cocycle projecting to `[c]`.
- `coneRelativeLawEquiv` (ROD.10) and `coneRelativeObserverDuality` (ROD.11) — unconditional.

## Traps
- Do NOT name a cohomology-class constructor `mk` inside a `structure` namespace: it collides with
  the auto-generated constructor. Used `cls`.
- `x ∈ ker f` is defeq to `f x = 0` but not syntactically; bridge with `have hx' : f x = 0 := hx`.
- Subtype coercions of `conePrCocycles`/`cocyclesMap` need the same `have … := hy` bridge before
  `rw` will fire.
