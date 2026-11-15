import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index

/-!
# The finite-field norm kernel as a power subgroup

The norm on units is surjective. Its kernel therefore has the same
cardinality as the subgroup of powers of the base-field unit order.
Inclusion follows from the exponent of the base unit group, giving an
exact description of the norm-one subgroup in arbitrary universes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Norm-one units are exactly the powers of the base-field multiplicative order. -/
theorem finiteField_norm_kernel_eq_power_range {K L : Type*} [Field K] [Field L]
    [Fintype K] [Finite L] [Algebra K L] :
    (Units.map (Algebra.norm K (S := L))).ker =
      (powMonoidHom (Fintype.card K - 1) : Lˣ →* Lˣ).range := by
  let ν := Units.map (Algebra.norm K (S := L))
  let q := Fintype.card K - 1
  have hqcard : Nat.card Kˣ = q := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  have hq : 0 < q := hqcard ▸ Nat.card_pos
  have hi : ν.ker.index = q := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (FiniteField.unitsMap_norm_surjective K L),
      Nat.card_congr Subgroup.topEquiv.toEquiv, hqcard]
  have hc : Nat.card ν.ker * q = Nat.card Lˣ := by
    simpa only [hi] using ν.ker.card_mul_index
  have hd : q ∣ Nat.card Lˣ := ⟨Nat.card ν.ker, hc.symm.trans (Nat.mul_comm _ _)⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro u ⟨v, rfl⟩
    change ν (v ^ q) = 1
    rw [map_pow, ← hqcard]
    exact pow_card_eq_one'
  · rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hd, ← hc,
      Nat.mul_comm (Nat.card ν.ker) q, Nat.mul_div_right _ hq]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
