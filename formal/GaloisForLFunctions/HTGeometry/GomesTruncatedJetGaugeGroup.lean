import GaloisForLFunctions.HTGeometry.GomesTruncatedJetOrderAlgebra
import Mathlib.Algebra.Group.Commute.Units

/-!
# Actual invertible symmetries of the two finite clocks

The joint commutant supplies a subgroup of ambient matrix units. Inversion
preserves both clock equations, and every pair of these symmetries commutes.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- All invertible matrices preserving the shift and the geometric jet clock. -/
def gomesTruncatedJetGaugeGroup (n : ℕ) (z : ℂ) :
    Subgroup (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ where
  carrier := {u | u.val ∈ gomesTruncatedJetJointAlgebra n z}
  one_mem' := (gomesTruncatedJetJointAlgebra n z).one_mem
  mul_mem' := fun ha hb => (gomesTruncatedJetJointAlgebra n z).mul_mem ha hb
  inv_mem' := by
    intro u hu
    obtain ⟨hD, hC⟩ := (gomesTruncatedJetJointAlgebra_mem_iff n z u.val).mp hu
    exact (gomesTruncatedJetJointAlgebra_mem_iff n z (u⁻¹).val).mpr
      ⟨hD.units_inv_left, hC.units_inv_left⟩

/-- Group membership is precisely membership of the underlying matrix in the joint algebra. -/
theorem gomesTruncatedJetGaugeGroup_mem_iff (n : ℕ) (z : ℂ)
    (u : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    u ∈ gomesTruncatedJetGaugeGroup n z ↔ u.val ∈ gomesTruncatedJetJointAlgebra n z := Iff.rfl

/-- The two literal clock equations characterize the entire gauge group. -/
theorem gomesTruncatedJetGaugeGroup_mem_iff_commute (n : ℕ) (z : ℂ)
    (u : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    u ∈ gomesTruncatedJetGaugeGroup n z ↔
      Commute u.val (fockShiftMatrix (n + 1)) ∧
      Commute u.val (RHTower.truncatedJetClock n z) :=
  gomesTruncatedJetJointAlgebra_mem_iff n z u.val

/-- Every two invertible joint symmetries commute, for every phase and horizon. -/
theorem gomesTruncatedJetGaugeGroup_mul_comm (n : ℕ) (z : ℂ)
    (u v : gomesTruncatedJetGaugeGroup n z) : u * v = v * u := by
  apply Subtype.ext
  apply Units.ext
  exact (gomesTruncatedJetJointAlgebra_commute n z
    ⟨u.val.val, u.property⟩ ⟨v.val.val, v.property⟩).eq

instance gomesTruncatedJetGaugeGroupCommGroup (n : ℕ) (z : ℂ) :
    CommGroup (gomesTruncatedJetGaugeGroup n z) :=
  { (inferInstance : Group (gomesTruncatedJetGaugeGroup n z)) with
    mul_comm := gomesTruncatedJetGaugeGroup_mul_comm n z }

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
