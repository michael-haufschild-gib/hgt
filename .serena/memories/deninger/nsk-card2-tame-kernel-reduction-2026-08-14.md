# Card 2 (deninger-algebraic-cyclotomic-milnor-amplitude): reduced to Garland alone

Date: 2026-08-14. All declarations build and audit to `[propext, Classical.choice, Quot.sound]`.

## What the card actually claims

Card `(1)` — `K_q^M(F) ⊗ ℝ = 0` for algebraic `F/ℚ`, `q ≥ 2` — is **not proved in the card**: its
proof paragraph cites Gallauer Remark 6.8, which cites **Borel's** computation of rational algebraic
`K`-theory of number rings, plus continuity over finite subextensions.

## Modules

`HTGeometry/MilnorKTameKernel.lean`
- `tameKernel (D : ∀ i, TameData K (κ i)) := ⨅ i, (D i).tameHom.ker`, `mem_tameKernel_iff`
- `tameFiniteSupport`, **`tame_finiteSupport_of_symbols`** (a.e.-vanishing passes from symbols to
  all classes via `milnorKDeg_mem_of_gen`)
- **`exists_zsmul_mem_tameKernel`** `[∀ i, Finite (κ i)ˣ]`
- **`milnorKDegTwo_torsion_of_tameKernel_torsion`**

`HTGeometry/MilnorKTameDedekind.lean` (additions)
- `finite_tameHomAtPlace_ne_zero_all`, `milnorKDegTwo_torsion_of_tameKernelAtPlaces_torsion`

`HTGeometry/MilnorKTameResidueFinite.lean`
- `algebraMap_surjective_of_isFractionRing_of_isUnit`
- **`finite_residueField_valuationSubring`** — residue field at a finite place is finite when
  `R ⧸ v.asIdeal` is. Chain: `valuationSubringAtPrime_eq_valuationSubring` +
  `IsLocalization v.asIdeal.primeCompl (valuationSubringAtPrime K v)` +
  `IsLocalization.algEquiv` + `RingEquiv.subringCongr` + `IsLocalRing.ResidueField.mapEquiv`, and
  `IsFractionRing (R ⧸ I) I.ResidueField` with `R ⧸ I` a field.
- `finite_quotient_asIdeal` (number ring), **`milnorKDegTwo_torsion_of_tameKernel_numberField`**

`RHTower/DeningerMilnorRealShape.lean` (addition)
- **`deningerMilnorRealVanishing_of_tameKernelTorsion`** — the card's `(1)` assuming only that the
  tame kernel of each finite subextension is torsion.

## Residual input, now the only one

**The tame kernel `K_2(𝒪_K)` of a number field is torsion** = Garland (1971) / Quillen + Borel.
Ruled out as shortcuts: `ℚ̄` (torsion for all number fields ⟺ `K_2^M(ℚ̄) = 0`, via
`N ∘ res = [L:K]`); Suslin unique divisibility; "Steinberg relations among S-units span
`Λ²(𝒪_S^×) ⊗ ℚ`" (**false**); Tate's elementary `K_2(ℚ)` (no transfer reduction of a number field
to `ℚ`).

## Toolchain traps hit here
- `Ideal.Quotient.field` is a `def`, not an instance — needs `attribute [local instance]`, and
  introducing it as a `haveI` creates a `Zero`/`CommSemiring` diamond against
  `Ideal.Quotient.commRing`. Use `Ideal.Quotient.maximal_ideal_iff_isField_quotient` +
  `IsField.mul_inv_cancel` and build the unit by hand instead.
- `isUnit_of_mul_eq_one` now needs `[IsDedekindFiniteMonoid M]`; build `⟨⟨a, b, hb, _⟩, rfl⟩`.
- `NumberField ↥K` for `K : IntermediateField ℚ F` is **not** obtainable from
  `hfd : FiniteDimensional ℚ ↥K` by `⟨⟩` or `NumberField.of_module_finite`: the class field uses the
  `algebraRat` module structure, `hfd` uses `IntermediateField`'s. Working construction:
  `{ to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective,
     to_finiteDimensional := by convert hfd using 2; exact Subsingleton.elim _ _ }`.
