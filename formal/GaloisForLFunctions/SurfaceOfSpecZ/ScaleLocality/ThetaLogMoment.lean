import GaloisForLFunctions.RHTower.ThetaFiniteShellSubquadraticSourceBound
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanSelfEnergyIsLogarithmic

/-! Absolute moments of the actual theta source have logarithmic exponential
growth. First-atom domination supplies a global double-exponential envelope;
an elementary convex estimate leaves an integrable exponential majorant. -/

open MeasureTheory Real
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower

/-- A coarse double-exponential convex bound with logarithmic moment growth. -/
theorem linear_sub_double_exp_le {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    a * t - Real.exp (2 * t) ≤ a * Real.log a := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  by_cases h : t ≤ Real.log a
  · have hm := mul_le_mul_of_nonneg_left h ha0.le
    linarith only [hm, Real.exp_pos (2 * t)]
  · have hae : a ≤ Real.exp t := by
      rw [← Real.exp_log ha0]
      exact Real.exp_le_exp.mpr (lt_of_not_ge h).le
    have hte : t ≤ Real.exp t := (Real.add_one_le_exp t).trans' (by linarith)
    have hp := mul_le_mul hae hte ht (Real.exp_pos t).le
    rw [← Real.exp_add, ← two_mul] at hp
    exact (sub_nonpos.mpr hp).trans (mul_nonneg ha0.le (Real.log_nonneg ha))

/-- A global double-exponential envelope for the actual theta source. -/
theorem exists_theta_double_exp_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, thetaCuspFullSource x ≤
      C * Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) := by
  let B := 1 + thetaCuspHigherAtomDominationWeight
  have hB : 0 < B := by
    have hb := thetaCuspHigherAtomDominationWeight_nonneg
    dsimp [B]
    linarith only [hb]
  refine ⟨B * (4 * Real.pi ^ 2), by positivity, fun x => ?_⟩
  have hb := thetaCuspFullSource_sub_first_le (abs_nonneg x)
  have hfirst := thetaCuspFirstAtom_le_doubleExponentialEnvelope |x|
  have hsource : thetaCuspFullSource |x| ≤ B * thetaCuspSourceTerm |x| 1 := by
    dsimp [B]
    linarith only [hb]
  have hx : thetaCuspFullSource |x| = thetaCuspFullSource x := by
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, thetaCuspFullSource_neg]
  rw [← hx]
  exact hsource.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfirst hB.le)

/-- Absolute theta moments grow at most as the exponential of `s log s`. -/
theorem exists_theta_logarithmic_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      (∫ x, Real.exp (s * |x|) * thetaCuspFullSource x) ≤
        C * Real.exp ((s + 6) * Real.log (s + 6)) := by
  obtain ⟨C, hC, hbound⟩ := exists_theta_double_exp_envelope
  refine ⟨2 * C, mul_pos two_pos hC, fun s hs => ?_⟩
  have hpoint (x : ℝ) : Real.exp (s * |x|) * thetaCuspFullSource x ≤
      (C * Real.exp ((s + 6) * Real.log (s + 6))) * Real.exp (-|x|) := by
    apply (mul_le_mul_of_nonneg_left (hbound x) (Real.exp_pos _).le).trans
    calc
      _ = C * Real.exp (s * |x| + (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|))) := by
        rw [Real.exp_add]
        ring
      _ ≤ C * Real.exp ((s + 6) * Real.log (s + 6) + -|x|) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        have hb := linear_sub_double_exp_le (by linarith : 1 ≤ s + 6) (abs_nonneg x)
        have hpi : 1 ≤ Real.pi := le_trans (by norm_num : (1 : ℝ) ≤ 3) Real.pi_gt_three.le
        have hp := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * |x|)).le
        nlinarith only [hb, hp, abs_nonneg x]
      _ = _ := by rw [Real.exp_add, mul_assoc]
  have hmajor : Integrable (fun x : ℝ =>
      (C * Real.exp ((s + 6) * Real.log (s + 6))) * Real.exp (-|x|)) := by
    have hi := GaloisForLFunctions.SurfaceOfSpecZ.integrable_exp_neg_mul_abs (a := 1) one_pos
    simp only [one_mul] at hi
    exact hi.const_mul _
  have hminor : Integrable (fun x : ℝ => Real.exp (s * |x|) * thetaCuspFullSource x) := by
    have hc : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
    apply hmajor.mono' (show Continuous (fun x : ℝ => Real.exp (s * |x|) * thetaCuspFullSource x) by fun_prop).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos _).le)]
    exact hpoint x
  have hi := integral_mono hminor hmajor hpoint
  rw [integral_const_mul] at hi
  have he : (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
    simpa only [one_mul, div_one] using
      GaloisForLFunctions.SurfaceOfSpecZ.integral_exp_neg_mul_abs (a := 1) one_pos
  rw [he] at hi
  calc
    _ ≤ (C * Real.exp ((s + 6) * Real.log (s + 6))) * 2 := hi
    _ = _ := by ring

#print axioms exists_theta_logarithmic_moment_bound
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
