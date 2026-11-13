import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm

/-!
# Localized weighted pairings

Cauchy–Schwarz pairs the exponential source norm with a restricted dual
kernel norm. On a terminal interval, the latter is bounded by its length.
-/

noncomputable section
open MeasureTheory Filter Set
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

/-- Half-exponential growth becomes an integrable square after dual weighting. -/
theorem weightedDualKernel_sq_le {k : ℝ → ℝ}
    (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2)) (u : ℝ) :
    (k u * Real.exp (-|u|)) ^ 2 ≤ Real.exp (-|u|) := by
  have h1 : k u ^ 2 ≤ Real.exp |u| := by
    rw [← sq_abs]
    calc |k u| ^ 2 ≤ Real.exp (|u| / 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hb u) 2
      _ = Real.exp |u| := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have he : Real.exp |u| * Real.exp (-|u|) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = k u ^ 2 * (Real.exp (-|u|) * Real.exp (-|u|)) := by ring
    _ ≤ Real.exp |u| * (Real.exp (-|u|) * Real.exp (-|u|)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = Real.exp (-|u|) := by rw [← mul_assoc, he, one_mul]

/-- A spatially restricted pairing pays only the dual mass on that set. -/
theorem sq_setIntegral_mul_kernel_le {f k : ℝ → ℝ}
    (hf : WeightedTwo f) (hk : Continuous k)
    (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2)) (s : Set ℝ) :
    (∫ u in s, f u * k u) ^ 2 ≤
      exponentialSourceMass f * ∫ u in s, Real.exp (-|u|) := by
  let K : ℝ → ℝ := fun u => k u * Real.exp (-|u|)
  have hKc : Continuous K := hk.mul (by fun_prop)
  have hK2 : Integrable (fun u => K u ^ 2) := by
    apply integrable_exp_neg_abs'.mono' (hKc.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact weightedDualKernel_sq_le hb u
  have hAm : AEStronglyMeasurable (fun u => Real.exp |u| * f u) volume :=
    (Real.continuous_exp.comp continuous_abs).aestronglyMeasurable.mul hf.meas
  have hcs := HTGeometry.sq_integral_mul_le (μ := volume.restrict s) hAm.restrict
    hKc.aestronglyMeasurable hf.sq.integrableOn hK2.integrableOn
  have heq : (fun u => (Real.exp |u| * f u) * K u) = fun u => f u * k u := by
    funext u
    have he : Real.exp |u| * Real.exp (-|u|) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ = (Real.exp |u| * Real.exp (-|u|)) * (f u * k u) := by dsimp only [K]; ring
      _ = _ := by rw [he, one_mul]
  rw [heq] at hcs
  have hleft : (∫ u in s, (Real.exp |u| * f u) ^ 2) ≤ exponentialSourceMass f :=
    setIntegral_le_integral hf.sq (Eventually.of_forall fun u => sq_nonneg _)
  have hright : (∫ u in s, K u ^ 2) ≤ ∫ u in s, Real.exp (-|u|) :=
    integral_mono hK2.integrableOn integrable_exp_neg_abs'.integrableOn
      (weightedDualKernel_sq_le hb)
  exact hcs.trans (mul_le_mul hleft hright
    (integral_nonneg fun u => sq_nonneg _) (exponentialSourceMass_nonneg f))

/-- The dual kernel square is at most one, giving the exact interval-length bound. -/
theorem sq_terminalIntegral_mul_kernel_le {f k : ℝ → ℝ}
    (hf : WeightedTwo f) (hk : Continuous k)
    (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2)) {h : ℝ} (hh : 0 ≤ h) :
    (∫ u in Icc (-h) 0, f u * k u) ^ 2 ≤ exponentialSourceMass f * h := by
  have hi : (∫ u in Icc (-h) 0, Real.exp (-|u|)) ≤ h := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-h) 0) :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hbnd := integral_mono integrable_exp_neg_abs'.integrableOn hc
      (fun u => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg u)))
    simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      Real.volume_Icc, zero_sub, neg_neg, ENNReal.toReal_ofReal hh, smul_eq_mul,
      mul_one] using hbnd
  exact (sq_setIntegral_mul_kernel_le hf hk hb _).trans
    (mul_le_mul_of_nonneg_left hi (exponentialSourceMass_nonneg f))

#print axioms sq_terminalIntegral_mul_kernel_le
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
