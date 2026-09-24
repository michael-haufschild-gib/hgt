import Mathlib.Tactic

/-!
# Finite affine source-scale identities

These identities retain the literal first-atom seed factor while changing
between the source normalization and the Gaussian affine-jet normalization.
They are kept separate from the theta import graph so the finite algebra is
checked once and reused in high-order source proofs.
-/

namespace RHTower.ThetaCuspOddFour
noncomputable section

theorem affine_twelve_algebra (q E J : ℝ)
    (hq : q ≠ 0) (hE : E ≠ 0) (hB : 4*q^2-6*q ≠ 0) :
    J/q^8 = (4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^6) *
      ((4-6*q⁻¹)^2/4) := by
  have hL : 4*q-6 ≠ 0 := by
    intro hz
    apply hB
    calc
      4*q^2-6*q = q*(4*q-6) := by ring
      _ = 0 := by rw [hz]; ring
  field_simp [hq, hE, hB, hL]
  have hL' : q*4-6 ≠ 0 := by
    convert hL using 1 <;> ring
  field_simp [hL']

theorem affine_lower_algebra (j : Fin 6) (q E J : ℝ)
    (hq : q ≠ 0) (hE : E ≠ 0) (hB : 4*q^2-6*q ≠ 0) :
    J/q^8 = (4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^j.val) *
      ((4-6*q⁻¹)^2/4) * (q⁻¹)^(6-j.val) := by
  have hL : 4*q-6 ≠ 0 := by
    intro hz
    apply hB
    calc
      4*q^2-6*q = q*(4*q-6) := by ring
      _ = 0 := by rw [hz]; ring
  have hL' : q*4-6 ≠ 0 := by
    convert hL using 1 <;> ring
  fin_cases j <;> norm_num <;>
    field_simp [hq, hE, hB, hL, hL']

theorem affine_lower_signed_algebra (j : Fin 6) (q E J : ℝ)
    (hq : q ≠ 0) (hE : E ≠ 0) (hB : 4*q^2-6*q ≠ 0) :
    J/q^8 =
      ((-1 : ℝ)^j.val * (4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^j.val)) *
      ((-1 : ℝ)^j.val * ((4-6*q⁻¹)^2/4) * (q⁻¹)^(6-j.val)) := by
  rw [affine_lower_algebra j q E J hq hE hB]
  fin_cases j <;> norm_num <;> ring

theorem affine_fourteen_source_algebra (q E J : ℝ)
    (hq : q ≠ 0) (hE : E ≠ 0) (hB : 4*q^2-6*q ≠ 0) :
    (-1 : ℝ)^7*(4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^7) =
      (-J/q^9) * (4/(4-6*q⁻¹)^2) := by
  have hL : 4*q-6 ≠ 0 := by
    intro hz
    apply hB
    calc
      4*q^2-6*q = q*(4*q-6) := by ring
      _ = 0 := by rw [hz]; ring
  have hL' : q*4-6 ≠ 0 := by
    convert hL using 1 <;> ring
  norm_num
  field_simp [hq, hE, hB, hL, hL']

end
end RHTower.ThetaCuspOddFour
