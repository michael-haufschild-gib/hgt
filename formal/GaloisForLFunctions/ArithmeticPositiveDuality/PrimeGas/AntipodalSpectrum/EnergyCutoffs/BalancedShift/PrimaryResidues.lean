import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.DigitContinuation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.PoleCalculus

/-!
# Stability of isometric pole residues under translation

At a primary clock return the change in the digit numerator is exactly
the counterterm from the centered recurrence. Every real translation
preserving positive labels has the same leading residues and pole support.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open BalancedContinuation Set

/-- Every admissible translation has exactly the original heat abscissa. The normalized
affine factor and its reciprocal are bounded on the entire interval of inverse labels. -/
theorem shifted_heat_summable_iff (t : ExceptionalTime) (j : ℕ) (a : {v : ℝ // -1 < v}) (s : ℂ) :
    Summable (fun x : Label t j => ‖weight (labelValue x+a.val) s‖) ↔ 1/2 < s.re := by
  let q (u : ℝ) := weight (1+a.val*u) s
  let I := Icc (0:ℝ) 1
  have he : 0 < 1+a.val := by linarith only [a.property]
  have hb : ContinuousOn (fun u : ℝ => ((1+a.val*u:ℝ):ℂ)) I := by fun_prop
  have hq : ContinuousOn q I := hb.cpow continuousOn_const
    (fun u hu => Complex.ofReal_mem_slitPlane.mpr (affine_pos zero_lt_one he hu))
  have hne (u : ℝ) (hu : u ∈ I) : q u ≠ 0 := by
    change ((1+a.val*u:ℝ):ℂ)^(-s) ≠ 0
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (affine_pos zero_lt_one he hu).ne')]
    exact Complex.exp_ne_zero _
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq.inv₀ hne)
  have hfac (x : Label t j) : weight (labelValue x+a.val) s =
      balancedHeat t j s x*q ((labelValue x)⁻¹) := by
    let n := labelValue x
    have hn := zero_lt_one.trans_le (label_one_le x)
    have hi := inverse_unit (label_one_le x)
    have hh : n+a.val = n*(1+a.val*n⁻¹) := by field_simp [show n ≠ 0 from hn.ne']
    change weight (n+a.val) s = _
    rw [hh,weight_mul hn.le (affine_pos zero_lt_one he hi).le,weight_label x s]
  rw [← balanced_heat_summable_iff t j s]
  constructor
  · intro hs
    apply (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro x
    have hi := inverse_unit (label_one_le x)
    have hh : balancedHeat t j s x = weight (labelValue x+a.val) s*(q ((labelValue x)⁻¹))⁻¹ := by
      rw [hfac,mul_assoc,mul_inv_cancel₀ (hne _ hi),mul_one]
    rw [hh,norm_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ hi) (norm_nonneg _)
  · intro hs
    apply (hs.mul_left K).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro x
    rw [hfac,norm_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _ (inverse_unit (label_one_le x))) (norm_nonneg _)

theorem primary_residue_and_support (t : ExceptionalTime) (j : ℕ) (a : {v : ℝ // -1 < v}) (k : ℤ) :
    let w := point t j k
    HTGeometry.laurentCoeff (extension t j a.val) w (-1) = HTGeometry.laurentCoeff (continuation t j) w (-1) ∧
    (meromorphicOrderAt (extension t j a.val) w < 0 ↔
      meromorphicOrderAt (continuation t j) w = (-1:ℤ)) ∧
    (meromorphicOrderAt (extension t j a.val) w = (-1:ℤ) ↔
      meromorphicOrderAt (continuation t j) w = (-1:ℤ)) := by
  let w := point t j k
  let N := fun z : ℂ => quadraticNumerator t j z-z*(center t j:ℂ)*numerator t j (z+1)
  let H := fun z : ℂ => correctionTrace t j 1 a.val z+z*((center t j:ℂ)-(a.val:ℂ))*continuation t j (z+1)
  have hw : -(3/2) < w.re := by change -(3/2:ℝ) < 1/2; norm_num
  have hw' : -(1/2) < w.re := by change -(1/2:ℝ) < 1/2; norm_num
  have h₁ : 1/2 < (w+1).re := by change (1/2:ℝ) < 1/2+1; norm_num
  have hN₁ : AnalyticAt ℂ (fun z => numerator t j (z+1)) w :=
    (numerator_analytic t j ⟨w+1,by linarith only [h₁]⟩).comp (f := fun z : ℂ => z+1)
      (analyticAt_id.add analyticAt_const)
  have hD₁ : AnalyticAt ℂ (fun z => denominator t j (z+1)) w :=
    (scaleFactor_analytic _ _).comp (analyticAt_id.add analyticAt_const)
  have hN : AnalyticAt ℂ N w := (quadratic_analytic t j ⟨w,hw⟩).sub
    ((analyticAt_id.mul analyticAt_const).mul hN₁)
  have hH : AnalyticAt ℂ H w := (correction_analytic t j (b := 1) (a := a.val) zero_lt_one
    (by linarith only [a.property]) ⟨w,hw⟩).add
    ((analyticAt_id.mul analyticAt_const).mul (hN₁.div hD₁ (scale_right t j ⟨w+1,h₁⟩)))
  have hz : denominator t j w = 0 := (scaleFactor_zero_iff (logRadix t j) w).mpr ⟨k,rfl⟩
  have hval : N w = numerator t j w := by
    have hx := digit_expansion t j ⟨w,hw'⟩
    change quadraticNumerator t j w = numerator t j w+w*_*_ at hx
    rw [← scale_difference,hz,sub_zero] at hx
    change quadraticNumerator t j w-w*(center t j:ℂ)*numerator t j (w+1) = _
    rw [hx,physical_num t j ⟨w+1,h₁⟩]
    ring
  have hd := (scaleFactor_derivative (logRadix t j) k).deriv
  have h := simple_scale hH hN (scaleFactor_analytic _ w) hz (by
    rw [hd]
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne'))
  have hf : (fun z => H z+N z/denominator t j z) = extension t j a.val := by
    funext z
    unfold H N extension background
    ring
  dsimp only at h
  rw [hf,hval,hd] at h
  simpa only [clock_residue,clock_pole_iff] using h

#print axioms shifted_heat_summable_iff
#print axioms primary_residue_and_support

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
