# Card 2 (`deninger-algebraic-cyclotomic-milnor-amplitude`) — reduction landed 2026-08-13

## What is now Lean-proved (all compile clean, axioms `propext, Classical.choice, Quot.sound`)
Built ON TOP of the corpus's pre-existing graded Milnor K-theory — do NOT rebuild it:
`HTGeometry/MilnorWittWittComparison.lean` has `MilnorSymbolDeg`, `MilnorKDeg`, `milnorClassDeg`,
`milnorRelSubgroupDeg`, `milnorKDeg_hom_ext`, **`milnorDegZeroEquiv : K_0^M ≅ ℤ`**,
**`milnorDegOneEquiv : K_1^M ≅ Additive Fˣ`**; `HTGeometry/MilnorKGradedRing.lean` has
`milnorSymbolAppend`, **`milnorMul`**, `milnorMul_class`, `milnorPairClass_*`.

New:
- `HTGeometry/MilnorKGrading.lean` — `torsionAddSubgroup`, `milnorClassDeg_split`,
  **`milnorKDeg_mem_torsion_of_two`** (`K_{2+k}^M` torsion once `K_2^M` is).
- `HTGeometry/MilnorKFunctoriality.lean` — `milnorUnitMap`, `milnorSymbolHom`, `milnorKPreMap`,
  **`milnorKMap`** (field hom ⇒ Milnor ring hom), `milnorKMap_symbol`,
  `milnorSymbol_mul_torsion_of_map`, `milnorSymbol_mul_torsion_of_ringHom`,
  `milnorSymbol_mul_torsion_of_subfield`.
- `HTGeometry/MilnorKAlgebraicReduction.lean` —
  **`milnorSymbol_mul_torsion_of_finiteSubextension`** (algebraic over ℚ ⇒ reduce to number fields).
- `RHTower/DeningerMilnorRealShape.lean` — `deningerTorsionModule_tensorReal_eq_zero`,
  **`deningerMilnorDegTensorReal_eq_zero`** (`K_q^M ⊗ ℝ = 0`, `q ≥ 2`, given degree-two torsion),
  `deningerMilnorDegZeroRealEquiv` (`≅ ℝ`), `deningerMilnorDegOneRealEquiv` (`≅ Fˣ ⊗ ℝ`).
All wired into `HTGeometry.lean` / `RHTower.lean`.  Card file updated with a `[NEW]` section.

## THE ONE REMAINING INPUT for `(1)`
*Every length-two Milnor symbol of a number field is torsion.*
Equivalent, via tame symbols into the finite residue fields, to: the tame kernel of a number field
is torsion (Tate/Garland finiteness; equivalently Borel's rank computation).  No elementary route
exists: `K_2` of an algebraically closed field is generally a nonzero uniquely divisible group, so
passing to `ℚ̄` does not help.

## Suggested next build steps toward it
1. Discrete valuation on a field + residue field; the **tame symbol**
   `∂_v{a,b} = (-1)^{v(a)v(b)} a^{v(b)} b^{-v(a)} mod m` on `MilnorKDeg K 2`
   (well-definedness = a case analysis on `v a`, `v b` for the Steinberg relation).
2. For a number field: only finitely many `p` have `∂_p{a,b} ≠ 1`, and each `k(p)^×` is finite, so
   some `n ≠ 0` puts `n{a,b}` in the tame kernel.  This makes the remaining core exactly
   "tame kernel torsion".
3. Then the deep input (Quillen finite generation + Borel rank, or Garland).

## Build-tree note
`lake build GaloisForLFunctions.HTGeometry` currently FAILS with a name collision owned by other
agents: `differentialIndependent_jet_zero` is declared in BOTH
`HTGeometry/EllipticVelocityTail.lean` and `HTGeometry/FreeDifferentialProtocolTimeLaw.lean`
(also mentioned in `ScalarDifferentialInversiveCoreProjectiveLaw.lean`).  Not caused by this work.
