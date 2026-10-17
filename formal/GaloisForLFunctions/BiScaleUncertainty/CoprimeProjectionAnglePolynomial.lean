import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionNeighbors
import Mathlib.Tactic.NoncommRing

/-!
# The exact polynomial of the reduced coprime projection product

Subtracting the common-range projection leaves an operator whose square is
one quarter of itself, or one half when a spacing is two.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

@[simp]
theorem coprimeProjector_mul_self (d : ℕ) :
    coprimeProjector d * coprimeProjector d = coprimeProjector d :=
  ContinuousLinearMap.ext (coprimeProjection_idempotent d)

theorem coprimeLcmProjector_tent (d e j : ℕ) :
    coprimeProjector (coprimeLcm d e) (tentVelocity e j) =
      if d + 2 ∣ coprimeCenter e j then tentVelocity e j else 0 := by
  rw [coprimeProjector_apply, coprimeProjection_tent_of_common_divisor
    (coprimeLcm d e) e j (e + 2) (by omega)
    (by simpa using Nat.dvd_lcm_right (d + 2) (e + 2)) (dvd_refl _)]
  simp only [coprimeLcm_dvd_center_iff]

def reducedCoprimeProduct (d e : ℕ) : Velocity →L[ℝ] Velocity :=
  coprimeProjector d * coprimeProjector e - coprimeProjector (coprimeLcm d e)

@[simp]
theorem reducedCoprimeProduct_star (d e : ℕ) :
    star (reducedCoprimeProduct d e) = reducedCoprimeProduct e d := by
  simp [reducedCoprimeProduct, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def, coprimeLcm_comm d e]

theorem reducedCoprimeProduct_mul_right (d e : ℕ) :
    reducedCoprimeProduct d e * coprimeProjector e = reducedCoprimeProduct d e := by
  have h : coprimeProjector (coprimeLcm d e) * coprimeProjector e =
      coprimeProjector (coprimeLcm d e) :=
    coprimeProjector_comp_of_dvd_reverse e (coprimeLcm d e)
      (by simpa using Nat.dvd_lcm_right (d + 2) (e + 2))
  simp only [reducedCoprimeProduct, sub_mul, mul_assoc, coprimeProjector_mul_self, h]

theorem reducedCoprimeProduct_tent (d e j : ℕ) :
    reducedCoprimeProduct d e (tentVelocity e j) =
      coprimeProjection d (tentVelocity e j) -
        if d + 2 ∣ coprimeCenter e j then tentVelocity e j else 0 := by
  simp only [reducedCoprimeProduct, sub_apply, mul_apply_eq_comp,
    coprimeProjector_apply, coprimeProjection_tent_self]
  rw [← coprimeProjector_apply (coprimeLcm d e) (tentVelocity e j),
    coprimeLcmProjector_tent]

theorem reducedCoprimeProduct_tent_of_adjacent {d e i j : ℕ} (he : 1 ≤ e)
    (h : TentAdjacent d i e j) :
    reducedCoprimeProduct d e (tentVelocity d i) =
      (-1 / 2 : ℝ) • coprimeProjection d (tentVelocity e j) := by
  have hr : coprimeProjector (coprimeLcm d e) (tentVelocity d i) = 0 := by
    rw [coprimeLcm_comm d e, coprimeLcmProjector_tent]
    simp [h.symm.not_dvd]
  simp only [reducedCoprimeProduct, sub_apply, mul_apply_eq_comp,
    hr, sub_zero, coprimeProjector_apply]
  rw [coprimeProjection_tent_one_neighbor he h.symm]
  change coprimeProjector d ((-1 / 2 : ℝ) • tentVelocity e j) = _
  rw [map_smul, coprimeProjector_apply]

private theorem reduced_square_tent {d e : ℕ} (he : 1 ≤ e) (j : ℕ) :
    reducedCoprimeProduct d e (reducedCoprimeProduct d e (tentVelocity e j)) =
      (if d = 0 then (1 / 2 : ℝ) else 1 / 4) •
        reducedCoprimeProduct d e (tentVelocity e j) := by
  by_cases hd : d + 2 ∣ coprimeCenter e j
  · have hz : reducedCoprimeProduct d e (tentVelocity e j) = 0 := by
      rw [reducedCoprimeProduct_tent, if_pos hd,
        coprimeProjection_tent_of_dvd d e j hd, sub_self]
    simp [hz]
  have ht : reducedCoprimeProduct d e (tentVelocity e j) =
      coprimeProjection d (tentVelocity e j) := by
    rw [reducedCoprimeProduct_tent, if_neg hd, sub_zero]
  rw [ht]
  by_cases hd0 : d = 0
  · subst d
    obtain ⟨i, k, hi, hk⟩ := exists_two_even_neighbors he hd
    have hai : TentAdjacent 0 i e j := Or.inl hi
    have hak : TentAdjacent 0 k e j := Or.inr hk
    conv_lhs => rw [coprimeProjection_tent_two_neighbors hi hk]
    rw [map_smul, map_add, reducedCoprimeProduct_tent_of_adjacent he hai,
      reducedCoprimeProduct_tent_of_adjacent he hak, ← add_smul, smul_smul]
    norm_num
  · by_cases ha : ∃ i, TentAdjacent d i e j
    · obtain ⟨i, hi⟩ := ha
      conv_lhs => rw [coprimeProjection_tent_one_neighbor (by omega) hi]
      rw [map_smul, reducedCoprimeProduct_tent_of_adjacent he hi, smul_smul]
      norm_num [hd0]
    · have hz := coprimeProjection_tent_no_neighbor d e j hd (by simpa using ha)
      simp [hz]

theorem reducedCoprimeProduct_square_of_pos_right (d e : ℕ) (he : 1 ≤ e) :
    reducedCoprimeProduct d e * reducedCoprimeProduct d e =
      (if d = 0 then (1 / 2 : ℝ) else 1 / 4) • reducedCoprimeProduct d e := by
  have h := comp_coprimeProjector_eq e
    (reducedCoprimeProduct d e * reducedCoprimeProduct d e)
    ((if d = 0 then (1 / 2 : ℝ) else 1 / 4) • reducedCoprimeProduct d e)
    (by
      intro j
      change reducedCoprimeProduct d e (reducedCoprimeProduct d e (tentVelocity e j)) =
        (if d = 0 then (1 / 2 : ℝ) else 1 / 4) •
          reducedCoprimeProduct d e (tentVelocity e j)
      exact reduced_square_tent (d := d) (e := e) he j)
  change (reducedCoprimeProduct d e * reducedCoprimeProduct d e) * coprimeProjector e =
    ((if d = 0 then (1 / 2 : ℝ) else 1 / 4) • reducedCoprimeProduct d e) *
      coprimeProjector e at h
  simpa only [mul_assoc, smul_mul_assoc, reducedCoprimeProduct_mul_right] using h

/-- Squared cosine of the nontrivial arithmetic angle. -/
def coprimeAngleSquare (d e : ℕ) : ℝ :=
  if 2 ≤ Nat.gcd (d + 2) (e + 2) then 0
  else if d = 0 ∨ e = 0 then 1 / 2 else 1 / 4

theorem coprimeAngleSquare_comm (d e : ℕ) :
    coprimeAngleSquare d e = coprimeAngleSquare e d := by
  simp only [coprimeAngleSquare, Nat.gcd_comm, or_comm]

theorem reducedCoprimeProduct_eq_zero_of_gcd (d e : ℕ)
    (h : 2 ≤ Nat.gcd (d + 2) (e + 2)) : reducedCoprimeProduct d e = 0 := by
  exact sub_eq_zero.mpr (coprimeProjector_comp_eq_lcm d e h)

/-- The reduced product has a single nonzero algebraic angle at every spacing pair. -/
theorem reducedCoprimeProduct_square (d e : ℕ) :
    reducedCoprimeProduct d e * reducedCoprimeProduct d e =
      coprimeAngleSquare d e • reducedCoprimeProduct d e := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · simp [reducedCoprimeProduct_eq_zero_of_gcd d e hg]
  by_cases he : e = 0
  · subst e
    have hd : 1 ≤ d := by
      by_contra hn
      have : d = 0 := by omega
      simp [this] at hg
    have h := congrArg star (reducedCoprimeProduct_square_of_pos_right 0 d hd)
    have hc : coprimeAngleSquare d 0 = 1 / 2 := by
      rw [coprimeAngleSquare, if_neg hg]
      simp
    rw [hc]
    simpa [star_mul, star_smul, reducedCoprimeProduct_star] using h
  · have h := reducedCoprimeProduct_square_of_pos_right d e (by omega)
    simpa [coprimeAngleSquare, hg, he] using h

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
