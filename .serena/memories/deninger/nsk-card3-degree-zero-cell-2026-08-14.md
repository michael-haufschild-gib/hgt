# Card 3: degree-zero cell and rank quotient (2026-08-14)

`formal/GaloisForLFunctions/RHTower/DeningerDegreeZeroCell.lean` — compiles clean, axioms
`propext, Classical.choice, Quot.sound`, wired into `RHTower.lean`.

- **`deningerDegreeZeroCell_proj_mem`** — for `S ⊆ 𝒜 0`, `Ideal.span S` is stable under
  `GradedRing.projZeroRingHom 𝒜` (proof: `Submodule.span_induction`, using that the projection is a
  ring hom fixing degree zero).  Counterpart of the corpus's
  `deningerPositiveCell_span_le_ker`.
- `deningerDegreeZeroCell_mem_iff`.
- **`deningerRankQuotient_equiv`** (`A ⧸ ker r ≃+* B` for surjective `r`) and
  `deningerRankQuotient_span_ker` — the card's `(6)`.

Card 3 status: the whole ABSTRACT half is now formalized in the graded shadow —
`(2)` positive-cell π₀ invariance (pre-existing), the equivariant universal property
(pre-existing), `(5)`/`(6)` the degree-zero cell and rank quotient (new), plus the whole
commutative-algebra half of the monic lift: `deningerMonicQuotient_powerBasis`,
`deningerMonic_isRegular`, `deningerMonicConormalEquiv`, `deningerKaehlerBaseChangeEquiv*`, and
**`deningerMonicCotangentComplex_mk`** (the cotangent complex is multiplication by `P'`).

REMAINING on card 3: only the Milnor–Witt geometric layer — the oriented fundamental class, its
determinant twist, and the Gysin forgetful map to `[Z_P]`.  These need Milnor–Witt sheaf theory
(unramified sheaves, Rost–Schmid complex, Chow–Witt groups), absent from mathlib.  The corpus DOES
have graded Milnor–Witt K-theory (`MilnorWittKDeg F n` with words `η^k[a_1]…[a_m]`, the three
relations, `mwKDeg_hom_ext` in `HTGeometry/MilnorWittGraded.lean`), so the natural next build is
**Morel's residue map `∂_π : K^MW_n(K) → K^MW_{n-1}(k)`** — the local model of the Gysin map, and
the Milnor–Witt analogue of the tame symbol already built in `MilnorKTameSymbol.lean`.
