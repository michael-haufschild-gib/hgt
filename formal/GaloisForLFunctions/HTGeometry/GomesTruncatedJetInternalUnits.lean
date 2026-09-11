import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeGroup
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Internal and ambient units are the same clock symmetries

An ambient inverse remains in the joint commutant. Consequently no symmetries
are lost when the gauge group is represented by units of the joint algebra.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Units of the joint algebra are exactly the ambient invertible clock symmetries. -/
def gomesTruncatedJetInternalUnitsEquiv (n : ℕ) (z : ℂ) :
    (gomesTruncatedJetJointAlgebra n z)ˣ ≃* gomesTruncatedJetGaugeGroup n z where
  toFun u := ⟨Units.map (gomesTruncatedJetJointAlgebra n z).val.toMonoidHom u, u.val.property⟩
  invFun u :=
    { val := ⟨u.val.val, u.property⟩
      inv := ⟨(u.val⁻¹).val, (u⁻¹).property⟩
      val_inv := Subtype.ext (Units.mul_inv u.val)
      inv_val := Subtype.ext (Units.inv_mul u.val) }
  left_inv u := by
    apply Units.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- The equivalence leaves the represented matrix unchanged. -/
theorem gomesTruncatedJetInternalUnitsEquiv_val (n : ℕ) (z : ℂ)
    (u : (gomesTruncatedJetJointAlgebra n z)ˣ) :
    (gomesTruncatedJetInternalUnitsEquiv n z u).val.val = u.val.val := rfl

/-- Recovering an internal unit also leaves the represented matrix unchanged. -/
theorem gomesTruncatedJetInternalUnitsEquiv_symm_val (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    ((gomesTruncatedJetInternalUnitsEquiv n z).symm u).val.val = u.val.val := rfl

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
