# Order-unit seminorm layer (start of operator systems)

`GaloisForLFunctions.HTGeometry.OrderUnitSeminorm`, namespace
`GaloisForLFunctions.HTGeometry.OrderUnit`.  **mathlib has NO order-unit theory** — checked, the only
`OrderUnit` hit is `Algebra/Order/Monoid/Units.lean`, which is about units of monoids.

`IsOrderUnit e` (positive + absorbing), `unitBounds e v = {t > 0 | -(t•e) ≤ v ≤ t•e}`,
`orderUnitNorm e v = sInf (unitBounds e v)`.  Proved: `unitBounds_nonempty`, `bddBelow_unitBounds`,
`unitBounds_mono`, `orderUnitNorm_nonneg`, `_le`, `le_orderUnitNorm`, `_zero`, `_neg`, `_add_le`.
So the order-unit seminorm IS a seminorm.

Typeclasses: `[AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V] [Module ℝ V]
[PosSMulMono ℝ V] [SMulPosMono ℝ V]`.  Many lemmas need only some — the file uses `omit ... in`
per theorem; keep that or the lint gate fails on unused-section-variable warnings.
Traps: `Real.sInf_nonneg` (not `le_csInf_iff'`, which wants `WellFoundedLT ℝ`);
`exists_lt_of_csInf_lt hne h : ∃ a ∈ S, a < b` destructures directly.

DONE also: `smul_mem_unitBounds`, `orderUnitNorm_smul_le`, `orderUnitNorm_smul` (positive
homogeneity — get the reverse inequality by applying the `≤` half at `c⁻¹`), `IsArchimedean`,
`le_smul_of_orderUnitNorm_eq_zero`, `eq_zero_of_orderUnitNorm_eq_zero`.  So Archimedean ⇒ the
seminorm is a NORM — the reason Archimedean is in the definition of an operator system, now a
theorem.
Trap: `mul_le_mul_left` on ℝ is a `≤` fact, not an iff — use `mul_le_mul_of_nonneg_left` then
`mul_inv_cancel₀`.
NEXT: the matrix levels (matrix-ordered structure, matrix order unit), then complete positivity.
