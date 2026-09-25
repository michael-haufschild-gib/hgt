import GaloisForLFunctions.RHTower.MobiusDivisorCriticalChildAbelMellinWeld

/-!
# Real integral of the physical critical Abel source

The terminal-child source is exactly the weighted integral of the actual
Chebyshev defect, including the floor and Euler-constant corrections.
This is the source-level comparison point for Route P and CCM-FU.
-/

open Complex MeasureTheory Set Finset
namespace RHTower

private noncomputable def criticalAbelRealKernel (t : ℝ) : ℂ :=
  ((Real.sqrt t / (2 * t) : ℝ) : ℂ)

private lemma criticalAbelRealKernel_eq {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (1 / 2 : ℂ) / (2 * t) = criticalAbelRealKernel t := by
  have hroot : (t : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [hroot, criticalAbelRealKernel]
  push_cast
  ring

private lemma criticalAbelRealKernel_integrableOn_Icc {x : ℝ} (_hx : 1 ≤ x) :
    IntegrableOn criticalAbelRealKernel (Icc 1 x) := by
  have hc : ContinuousOn (fun t : ℝ => Real.sqrt t / (2 * t)) (Icc 1 x) := by
    apply Real.continuous_sqrt.continuousOn.div
      (continuousOn_const.mul continuousOn_id)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact mul_ne_zero (by norm_num) ht0.ne'
  exact (Complex.continuous_ofReal.comp_continuousOn hc).integrableOn_Icc

private lemma criticalAbelRealSource_integrableOn {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn
      (fun t : ℝ =>
        ((t : ℂ) ^ (1 / 2 : ℂ) / (2 * t)) *
          ∑ n ∈ Icc 1 ⌊t⌋₊, criticalSourceCoeff n)
      (Ioo 1 x) := by
  have hi : IntegrableOn
      (fun t : ℝ => criticalAbelRealKernel t *
        ∑ n ∈ Icc 1 ⌊t⌋₊, criticalSourceCoeff n) (Icc 1 x) :=
    integrableOn_mul_sum_Icc criticalSourceCoeff (by norm_num)
      (criticalAbelRealKernel_integrableOn_Icc hx)
  apply (hi.mono_set (by intro t ht; exact ⟨ht.1.le, ht.2.le⟩)).congr_fun
  · intro t ht
    change criticalAbelRealKernel t *
      (∑ n ∈ Icc 1 ⌊t⌋₊, criticalSourceCoeff n) =
        ((t : ℂ) ^ (1 / 2 : ℂ) / (2 * t)) *
          (∑ n ∈ Icc 1 ⌊t⌋₊, criticalSourceCoeff n)
    rw [← criticalAbelRealKernel_eq (by linarith [ht.1])]
  · exact measurableSet_Ioo

/-- The terminal critical Abel source as a real integral of the exact
Chebyshev defect, with its floor and Euler-constant corrections retained. -/
theorem criticalContinuousAbel_eq_source_real_integral
    {x : ℝ} (hx : 1 ≤ x) :
    criticalContinuousAbel x =
      ∫ t in Ioo (1 : ℝ) x,
        (Real.sqrt t / (2 * t)) * psiDefect ⌊t⌋₊ := by
  let f : ℝ → ℂ := fun t =>
    ((t : ℂ) ^ (1 / 2 : ℂ) / (2 * t)) *
      ∑ n ∈ Icc 1 ⌊t⌋₊, criticalSourceCoeff n
  have hi : IntegrableOn f (Ioo 1 x) := criticalAbelRealSource_integrableOn hx
  calc
    criticalContinuousAbel x = (∫ t in Ioo (1 : ℝ) x, f t).re := by
      rw [criticalContinuousAbel, squareRootSummatoryPrimitive_eq_integral]
    _ = ∫ t in Ioo (1 : ℝ) x, (f t).re := (integral_re hi).symm
    _ = ∫ t in Ioo (1 : ℝ) x,
          (Real.sqrt t / (2 * t)) * psiDefect ⌊t⌋₊ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hfloor : 1 ≤ ⌊t⌋₊ :=
        (Nat.le_floor_iff ht0.le).mpr (by simpa using ht.1.le)
      dsimp [f]
      rw [criticalAbelRealKernel_eq ht0, criticalSourceCoeff_cumulative _ hfloor]
      change (((Real.sqrt t / (2 * t) : ℝ) : ℂ) *
        (psiDefect ⌊t⌋₊ : ℂ)).re =
          Real.sqrt t / (2 * t) * psiDefect ⌊t⌋₊
      rw [← Complex.ofReal_mul, Complex.ofReal_re]

end RHTower
