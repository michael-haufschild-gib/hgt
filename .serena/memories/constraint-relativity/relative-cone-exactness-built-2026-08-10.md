# Mapping-cone layer built (ROD.10/ROD.11 unconditional, plus the character layer)

Module: `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RelativeConeExactness.lean`
(wired into `GaloisForLFunctions.HTGeometry`; `lake build` of the module itself is green).

Card: `docs/drafts/pipeline/3-formalized/constraint-relativity/relative-law-observer-descent-duality.md`
Its companion previously admitted `relativeLawEquiv` took the mapping-cone long exact sequence as
INPUT exactness.  That is now PROVED, and the character/pairing layer is built too.

## Contents
- `ZCochain k M` — `ℤ`-graded cochain complexes of `k`-vector spaces.
  KEY TRICK: index cohomology by the LOWER degree, `H n := ker (d (n+1)) ⧸ range (d n)`.
  Removes EVERY dependent-index cast. The corpus's ℕ-indexed `DeningerCochainComplex`
  (`HTGeometry/CochainComplexCohomology.lean`) sets `coboundaries 0 = ⊥`, under which the shift
  `H^j(C[1]) = H^{j+1}(C)` FAILS at `j = 0` — so the cone segment cannot be stated there.
- `ZCochainMap`, `cocyclesMap`, `cohomologyMap`.
- `coneComplex Φ` (`Cone(Φ)ⁿ = Xⁿ ⊕ Cⁿ⁺¹`, `d(x,c) = (d_X x − Φ c, −d_C c)`), `coneInc`, `conePr`.
- `cone_exact_left`, `cone_exact_right` — exactness of `Hⁿ(X) → Hⁿ(Cone) → Hⁿ⁺¹(C) → Hⁿ⁺¹(X)`.
  Witnesses: subtract `d_Cone (0, b)`; form the cone cocycle `(x, c)`.
- `coneRelativeLawEquiv` (ROD.10), `coneRelativeObserverDuality` (ROD.11) — no hypotheses.
- `sourceCharacter`, `coneCharacter`, `coneCharacter_coneInc`, `coneCharacterRel`,
  `coneCharacterRel_eq` — the character layer: a functional killing coboundaries (the Route-R card's
  `I_p D_0 = 0`) gives a cone character; it annihilates the image of `Hⁿ(X)` (so it reads the
  shifted source coordinate, never the primitive `L_p`); and pairing it with a relative-law class
  computes the source character on the corresponding element of `ker f`.  This is
  `(ROD.12)`/`(ROD.17)`–`(ROD.18)` and `(RRC.26)`–`(RRC.31)` in abstract form.

## What is still open on that card
`(ROD.13)`–`(ROD.18)` literally: instantiating `P := c_ρ I_p(·)[F_{∓t}]` needs the objects
`A, α_p, ε_0, I_p, X_t, Φ_p, L_p, η_p, V = ℂ^𝒫/ℓ¹, F_t, c_ρ` from the STAGE-2 card
`docs/drafts/pipeline/2-fully-proven/constraint-relativity/route-r-raw-resolved-relative-cone-character-law.md`
(461 lines; its boxed result `(RRC.31)` IS `(ROD.17)/(ROD.18)`).  Formalizing that card is the
remaining work, and the abstract half is now already in place.

## Traps
- Do NOT name a cohomology-class constructor `mk` in a `structure` namespace (collides with the
  auto-generated constructor). Used `cls`.
- `x ∈ ker f` is defeq to `f x = 0` but not syntactically; bridge with `have hx' : f x = 0 := hx`.
  Same for `↑y ∈ coboundaries` before `rw` will fire.

## Environment note (2026-08-10)
The HTGeometry umbrella build is currently BROKEN BY THE CONCURRENT SESSION: their new
`HTGeometry/MatrixOrderedSpace.lean` (created 12:52) declares `amplify_apply`, which already exists
in `HTGeometry/KroneckerAmplification.lean` (3 Aug).  Not ours — do not rename their declarations;
verify own work with `lake build <own module>` until they fix it.
