# Deninger NSK cards — state after 2026-08-14

## Card 3 `deninger-selective-positive-cell-h0-preservation` — DONE, moved to `3-formalized`

The `∞`-categorical blocker on `(2)` (`π₀(A//K) ≅ π₀A`) is closed **unconditionally** in
simplicial commutative rings:

- `HTGeometry/SimplicialPiZero.lean` — `simplicialPiZero := colim` over `Δᵒᵖ`, `simplicialPiZeroAdj`
  (`π₀ ⊣ const`), preserves pushouts, `isIso_of_isPushout_of_isIso`.
- `HTGeometry/SimplicialPiZeroSymmetricAlgebra.lean` — **the missing free functor**:
  `symFree : AddCommGrpCat ⥤ CommRingCat` (symmetric algebra over `ℤ`), `symFreeAdj`,
  levelwise `simplicialSymFree`/`simplicialSymFreeAdj` (via `Adjunction.whiskerRight`),
  `addPiZero := colim`, and `piZeroSymFreeIso : π₀ ∘ Sym ≅ Sym ∘ π₀` from
  `Adjunction.leftAdjointUniq` (both are left adjoint to `R ↦ const(R,+)`, using
  `Adjunction.ofNatIsoRight` + `Functor.constComp`).  Then `piZeroSymFree_isInitial`
  (`π₀K = 0 ⟹ π₀Free⁺(K)` initial), `isIso_of_isInitial`,
  `simplicialPiZero_isIso_of_positiveCell`, and the concrete
  `symAug` / `simplicialPiZero_isIso_pushout_inl` on the honest pushout.
- `HTGeometry/SimplicialPiZeroTower.lean` — `(4)` and the limit stages:
  `isIso_colimit_ι_zero` (sequential diagram of isos has its first term for colimit),
  `isIso_map_of_isIso_succ`, `simplicialPiZero_isIso_colimit_ι_zero(_of_succ)`.

### Lean traps hit here
- `AddCommGrp` does not exist in this toolchain — it is **`AddCommGrpCat`**.
- `SymmetricAlgebra ℤ M`'s `CommRing` instance is a `RingCon.Quotient`; `show`/`rw` through
  `CommRingCat.Hom.hom (CommRingCat.ofHom …)` **times out at `whnf`/`isDefEq`**.  Prove those
  lemmas with a *direct term* (`SymmetricAlgebra.lift_ι_apply _ x`) and use `exact`, never `show`.
  `simp` will not fire `CommRingCat.hom_ofHom` there either.
- `rw` fails on `(towerCocone …).pt` unless the cocone is an **`abbrev`** (reducible), because
  `rw`'s motive check runs at `instances` transparency.
- Section variables used only in the proof body need `include hD in`.

## Card 2 `deninger-algebraic-cyclotomic-milnor-amplitude` — still stage 2, one input missing

New infrastructure (all `propext, Classical.choice, Quot.sound`):

- `HTGeometry/MilnorKResidueMap.lean` — **Milnor's residue in every degree**.  Key design point:
  `resPairAt (n) (l) (h : l.length = n)` recurses on `n`, so the value's type never mentions the
  list and both relations (`resPairAt_mul`, `resPairAt_steinberg`) are statable without transport.
  `resPre`/`resPre_ker`/`milnorResPair` descend it; `milnorResidue`, `milnorSpecialization`;
  `milnorResidue_one` = valuation, `milnorResidue_two` = tame symbol.
- `HTGeometry/MilnorKResidueValuation.lean` — `residueDataOfValuation`, `placeUniformizer`,
  `residueDataAtPlace` (uniformizer from `HeightOneSpectrum.valuation_exists_uniformizer`).
  `oneSub_res` is automatic: the residue map is induced by a ring hom.
- `HTGeometry/MilnorKFiniteField.lean` — **`K_n^M(finite field) = 0` for `n ≥ 2`**.
  `milnorSymTwo` bilinear ⟹ `{g^i,g^j} = ij{g,g}`; `two_smul_milnorSymTwo_self`;
  `exists_nonsquare_oneSub_nonsquare` by counting with `quadraticChar_sum_zero`;
  `milnorSymTwo_gen_eq_zero`; `milnorKDegTwo_eq_zero_of_finite`, `milnorKDeg_eq_zero_of_finite`.

### The one remaining input
**The tame kernel of a number field is torsion** (`K₂(𝒪_K) ⊗ ℚ = 0`) — Garland 1971, equivalently
Quillen finite generation + Borel ranks, equivalently Soulé vanishing + Quillen–Lichtenbaum.
A literature sweep (Aug 2026) found **no elementary proof**.  Dead ends confirmed: Bass–Milnor–Serre
(congruence kernel gives no finiteness), Moore (reduces to the same statement about the wild
kernel), transfer/Galois descent (only reformulates it as `K₂^M(ℚ̄) ⊗ ℚ = 0`, or as
`K₃^M(ℚ(t)) ⊗ ℚ = 0` via Milnor's exact sequence), `S`-unit symbol generation (false).

Programme card: `docs/drafts/pipeline/1-in-progress/new_scientific_knowledge/deninger/garland-tame-kernel-torsion.md`.
Next bricks recorded there: Milnor's exact sequence for `F(t)`, Bass–Tate–Kato norms with the
projection formula, Tate's `K₂^M(ℚ)`.
