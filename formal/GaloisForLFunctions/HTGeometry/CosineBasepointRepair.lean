import GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal

/-!
# Cancelling the diagonal basepoint before reciprocal repair

The filled divided difference supplies an entire homogeneous pair whose quotient
has value 1 at the origin, obeys both reflections, and takes the holomorphic value
-1 at every point of the infinite diagonal family. The marked 1-fiber is not
classified here. In particular this is not a C2-P counterexample.
-/

namespace GaloisForLFunctions.HTGeometry.CosineBasepointRepair

open Complex LabeledCosineDescent CosineInfiniteDiagonal
open scoped ComplexConjugate

noncomputable section

def divided : ℂ → ℂ := dslope source 0
def numerator (w : ℂ) : ℂ := divided w + divided (-w) + I * (divided w - divided (-w))
def denominator (w : ℂ) : ℂ := divided w + divided (-w) - I * (divided w - divided (-w))
def repair (w : ℂ) : ℂ := numerator w / denominator w

theorem divided_entire : Differentiable ℂ divided := by
  intro w
  by_cases hw : w = 0
  · subst w
    obtain ⟨p, hp⟩ := source_entire.analyticAt 0
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
  · exact (differentiableAt_dslope_of_ne hw).mpr (source_entire w)

theorem divided_mul (w : ℂ) : w * divided w = source w - source 0 := by
  simpa [divided, smul_eq_mul] using sub_smul_dslope source 0 w

theorem scaled_coordinates (w : ℂ) :
    w * numerator w = source w - source (-w) + I * (source w + source (-w) - 2 * source 0) ∧
    w * denominator w = source w - source (-w) - I * (source w + source (-w) - 2 * source 0) := by
  have h₁ := divided_mul w
  have h₂ := divided_mul (-w)
  constructor
  · dsimp [numerator]
    linear_combination (1 + I) * h₁ + (I - 1) * h₂
  · dsimp [denominator]
    linear_combination (1 - I) * h₁ + (-1 - I) * h₂

theorem source_deriv_zero_ne : deriv source 0 ≠ 0 := by
  simpa [fiberPoint] using source_deriv_ne_zero 0 0

theorem source_deriv_zero_conj : conj (deriv source 0) = deriv source 0 := by
  have hd : deriv source 0 = -(2 * (Real.pi : ℂ) / 3) * Complex.sin (Real.pi / 9) := by
    simpa [fiberPoint] using source_jet_identity 1 0
  simp [hd, ← Complex.sin_conj, map_ofNat]

theorem divided_conj (w : ℂ) : divided (conj w) = conj (divided w) := by
  by_cases hw : w = 0
  · simp [hw, divided, source_deriv_zero_conj]
  · have hcw : conj w ≠ 0 := by simpa using hw
    have hzero : conj (source 0) = source 0 := by simpa using (source_conj 0).symm
    simp [divided, dslope_of_ne _ hw, dslope_of_ne _ hcw, slope, source_conj, hzero]

theorem numerator_entire : Differentiable ℂ numerator := by
  exact (divided_entire.add (divided_entire.comp (by fun_prop))).add
    ((divided_entire.sub (divided_entire.comp (by fun_prop))).const_mul I)

theorem denominator_entire : Differentiable ℂ denominator := by
  exact (divided_entire.add (divided_entire.comp (by fun_prop))).sub
    ((divided_entire.sub (divided_entire.comp (by fun_prop))).const_mul I)

theorem neg_coordinates (w : ℂ) : numerator (-w) = denominator w ∧
    denominator (-w) = numerator w := by
  simp only [numerator, denominator, neg_neg]
  constructor <;> ring

theorem conjugate_coordinates (w : ℂ) : numerator (conj w) = conj (denominator w) ∧
    denominator (conj w) = conj (numerator w) := by
  simp [numerator, denominator, ← map_neg, divided_conj]
  ring

theorem repair_reciprocal (w : ℂ) : repair (-w) = (repair w)⁻¹ := by
  simp [repair, (neg_coordinates w).1, (neg_coordinates w).2]

theorem repair_conjugate (w : ℂ) : repair (conj w) = (conj (repair w))⁻¹ := by
  simp [repair, (conjugate_coordinates w).1, (conjugate_coordinates w).2]

theorem denominator_zero_ne : denominator 0 ≠ 0 := by
  simpa [denominator, divided, two_mul] using
    mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) source_deriv_zero_ne

theorem repair_zero : repair 0 = 1 := by
  apply (div_eq_one_iff_eq denominator_zero_ne).mpr
  simp [numerator, denominator]

theorem repair_analyticAt_zero : AnalyticAt ℂ repair 0 :=
  (numerator_entire.analyticAt 0).div (denominator_entire.analyticAt 0) denominator_zero_ne

theorem source_zero : source 0 = Complex.cos ((Real.pi : ℂ) / 9) := by
  simpa [fiberPoint, fiberValue] using source_fiberPoint 1 0

theorem source_point_ne_zero_value (n : ℕ) : source (point n) ≠ source 0 := by
  intro h
  rw [source_point, source_zero] at h
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.mp h
  all_goals
    have hi := congrArg Complex.im hk
    simp [lift_im, radius_ne_zero, Real.pi_ne_zero] at hi
  have hp : Real.pi * radius n = 0 := by linear_combination -9 * hi
  exact (mul_ne_zero Real.pi_ne_zero (radius_ne_zero n)) hp

theorem divided_point_ne_zero (n : ℕ) : divided (point n) ≠ 0 := by
  intro h
  have hm := divided_mul (point n)
  rw [h, mul_zero] at hm
  exact source_point_ne_zero_value n (sub_eq_zero.mp hm.symm)

theorem divided_neg_point (n : ℕ) : divided (-point n) = -divided (point n) := by
  have hn : point n ≠ 0 := by
    intro h
    exact point_nonreal n (by simp [h])
  apply mul_left_cancel₀ hn
  have h₁ := divided_mul (point n)
  have h₂ := divided_mul (-point n)
  rw [← point_coincidence] at h₂
  linear_combination h₁ - h₂

theorem point_denominator_ne (n : ℕ) : denominator (point n) ≠ 0 := by
  have he : denominator (point n) = -2 * I * divided (point n) := by
    rw [denominator, divided_neg_point]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (divided_point_ne_zero n)

theorem repair_point (n : ℕ) : repair (point n) = -1 := by
  apply (div_eq_iff (point_denominator_ne n)).mpr
  rw [numerator, denominator, divided_neg_point]
  ring

theorem basepoint_escape : repair 0 = 1 ∧ AnalyticAt ℂ repair 0 ∧
    (∀ w, repair (-w) = (repair w)⁻¹) ∧
    (∀ w, repair (conj w) = (conj (repair w))⁻¹) ∧
    Set.Infinite {w : ℂ | w.im ≠ 0 ∧ AnalyticAt ℂ repair w ∧ repair w = -1} := by
  refine ⟨repair_zero, repair_analyticAt_zero, repair_reciprocal, repair_conjugate, ?_⟩
  apply (Set.infinite_range_of_injective point_injective).mono
  rintro w ⟨n, rfl⟩
  exact ⟨point_nonreal n, (numerator_entire.analyticAt _).div
    (denominator_entire.analyticAt _) (point_denominator_ne n), repair_point n⟩

end

end GaloisForLFunctions.HTGeometry.CosineBasepointRepair
