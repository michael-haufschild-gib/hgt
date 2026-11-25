import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.CountAtoms
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.Subdivision

/-! # Dilation rigidity of the limiting prime counting law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory VacuumCalibration
open scoped NNReal

/-- Rescaling the energy interval multiplies the thermal drift by the same factor. -/
theorem mass_dilate (c d a : ℝ) {r : ℝ} (hr : 0 < r) :
    mass (r*c) (r*d) a = mass c d (r*a) := by
  let f (v : ℝ) := Real.exp (-a*v)/v
  have H := intervalIntegral.integral_comp_mul_left (a := c) (b := d) f hr.ne'
  have he (v : ℝ) : r*f (r*v) = Real.exp (-(r*a)*v)/v := by
    unfold f
    rw [show -a*(r*v) = -(r*a)*v by ring,← mul_div_assoc,mul_div_mul_left _ _ hr.ne']
  change (∫ v in (r*c)..(r*d),f v) = _
  calc _ = r*(∫ v in c..d,f (r*v)) := by rw [H,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
       _ = _ := by rw [← intervalIntegral.integral_const_mul]; exact intervalIntegral.integral_congr (fun v _ => he v)

theorem mass_strictAnti {c d : ℝ} (hc : 0 < c) (hcd : c < d) : StrictAnti (mass c d) := by
  intro a b hab
  have hcont (s : ℝ) : ContinuousOn (fun v : ℝ => Real.exp (-s*v)/v) (Icc c d) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div continuousOn_id
      (fun v hv => (hc.trans_le hv.1).ne')
  have hlt (v : ℝ) (hv : 0 < v) : Real.exp (-b*v)/v < Real.exp (-a*v)/v :=
    div_lt_div_of_pos_right (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (neg_lt_neg hab) hv)) hv
  exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcd (hcont b) (hcont a)
    (fun v hv => (hlt v (hc.trans hv.1)).le) ⟨c,⟨le_rfl,hcd.le⟩,hlt c hc⟩

/-- One nontrivial dilation preserves the limiting count law exactly at zero thermal drift. -/
theorem dilation_invariant_iff {c d r : ℝ} (hc : 0 < c) (hcd : c < d) (hr : 0 < r) (hne : r ≠ 1) (a : ℝ) :
    poissonCount ⟨mass (r*c) (r*d) a,mass_nonneg (mul_pos hr hc) (mul_le_mul_of_nonneg_left hcd.le hr.le) a⟩ =
      poissonCount ⟨mass c d a,mass_nonneg hc hcd.le a⟩ ↔ a = 0 := by
  rw [poissonCount_injective.eq_iff,Subtype.mk.injEq,mass_dilate _ _ _ hr,(mass_strictAnti hc hcd).injective.eq_iff]
  constructor
  · intro H
    by_contra ha
    apply hne
    exact mul_right_cancel₀ ha (H.trans (one_mul a).symm)
  · rintro rfl
    exact mul_zero _

/-- Two adjacent octaves at isometric damping converge to independent copies of the same count. -/
theorem octave_pair_limit {c : ℝ} (hc : 0 < c) :
    let law := poissonCount ⟨Real.log 2,(Real.log_pos one_lt_two).le⟩
    Tendsto (fun h => pairedCount (c := c) (b := 2*c) (d := 2*(2*c)) (by linarith only [hc]) h 1)
      criticalApproach (𝓝 (law.prod law)) := by
  dsimp only
  have hcb : c < 2*c := by linarith only [hc]
  have hbd : 2*c < 2*(2*c) := by linarith only [hc]
  have H := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((doubled_count_limit hc).prodMk_nhds (doubled_count_limit (hc.trans hcb)))
  exact H.congr (fun h => (pairedCount_eq hcb.le hbd.le h 1).symm)

#print axioms mass_dilate
#print axioms mass_strictAnti
#print axioms dilation_invariant_iff
#print axioms octave_pair_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
