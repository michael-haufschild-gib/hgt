import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.QuartetLogMoments
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ConfigurationTailIsolation
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-! Positive theta deformations isolate every positive-depth zeta mode,
with absolute exponential moments of logarithmic growth. -/

open MeasureTheory Complex Set
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower

theorem sourceTransform_I_mul_eq_laplace (k : ℝ → ℝ) (w : ℂ) :
    sourceTransform (fun x => (k x : ℂ)) (I * w) =
      ∫ x : ℝ, (k x : ℂ) * Complex.exp (w * x) := by
  unfold sourceTransform
  apply integral_congr_ae
  filter_upwards [] with x
  have he : -I * (I * w) * (x : ℂ) = w * x := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  rw [he, mul_comm]

theorem sourceTransform_I_mul_conj (k : ℝ → ℝ) (w : ℂ) :
    sourceTransform (fun x => (k x : ℂ)) (I * conj w) =
      conj (sourceTransform (fun x => (k x : ℂ)) (I * w)) := by
  have h := sourceTransform_conj_comp (u := fun x => (k x : ℂ)) (I * conj w)
  simpa only [Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_conj,
    neg_mul, neg_neg] using h

/-- Every active spline exponent is a rotated zero of the actual Xi function. -/
theorem XiC_I_mul_of_evenCoeff_ne_zero {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0) : XiC (I * z) = 0 := by
  have hρ : (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
    rcases mem_of_evenCoeff_ne_zero hz with hz | hz
    · exact hz
    · have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, map_div₀, map_add, map_one]
      simpa only [map_add, hhalf, Complex.conj_conj] using conj_mem_zetaZeroConfig hz
  have hne1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro he
    have hr := hρ.2.2
    rw [he, Complex.one_re] at hr
    exact (lt_irrefl _ hr).elim
  have hxi := (xi_eq_zero_iff hρ.2.1 hne1).mpr hρ.1
  have he : (1 / 2 : ℂ) + (I * z) * I = 1 - (1 / 2 + z) := by
    have hi : (I * z) * I = -z := by
      calc
        _ = (I * I) * z := by ring
        _ = -z := by rw [Complex.I_mul_I]; ring
    rw [hi]
    ring
  rwa [XiC, he, xi_one_sub]

/-- Every active positive-depth zeta mode admits a positive finite-spectrum
filter with logarithmic absolute moment growth. -/
theorem exists_zeta_quartet_log_filter {z₀ : ℂ}
    (hz₀ : evenCoeff zetaZeroConfig (boxSpline 1 3) z₀ ≠ 0) (hre : 0 < z₀.re) :
    ∃ (k : ℝ → ℝ) (C : ℝ) (S : Finset ℂ), 0 < C ∧ Continuous k ∧
      (∀ x, 0 < k x) ∧
      (∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) ∧
      (∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (s * |x|) * k x) ≤
        C * Real.exp ((s + 6) * Real.log (s + 6))) ∧
      sourceTransform (fun x => (k x : ℂ)) (I * z₀) ≠ 0 ∧
      ∀ z ∉ S, evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0 →
        sourceTransform (fun x => (k x : ℂ)) (I * z) = 0 := by
  classical
  have him := evenCoeff_spline_real hz₀
  have hxi := XiC_I_mul_of_evenCoeff_ne_zero hz₀
  have hr : (I * z₀).re = -z₀.im := by simp
  have hi : (I * z₀).im = z₀.re := by simp
  let a : ℂ := if z₀.im < 0 then I * z₀ else -conj (I * z₀)
  have ha : a ∈ xiQuadrantZeros := by
    dsimp only [a]
    split_ifs with hneg
    · exact ⟨by rw [hr]; linarith only [hneg], by rw [hi]; exact hre, hxi⟩
    · have hpos : 0 < z₀.im := by
        by_contra h
        exact him (le_antisymm (not_lt.mp h) (not_lt.mp hneg))
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Complex.neg_re, Complex.conj_re, hr, neg_neg] using hpos
      · simpa only [Complex.neg_im, Complex.conj_im, hi, neg_neg] using hre
      · rw [XiC_even, XiC_conj, hxi, map_zero]
  have hmem : I * z₀ ∈ xiQuartetSet a := by
    by_cases hneg : z₀.im < 0 <;> simp [a, hneg, xiQuartetSet]
  obtain ⟨k, C, hC, hkc, hk, _, hm, hb, hkeep, hzero⟩ := exists_positive_quartet_log_moments ha
  let S : Finset ℂ := ({a, conj a, -a, -conj a} : Finset ℂ).image fun z => -I * z
  refine ⟨k, C, S, hC, hkc, hk, hm, hb, hkeep _ hmem, ?_⟩
  intro z hz hcz
  apply hzero (I * z) (XiC_I_mul_of_evenCoeff_ne_zero hcz)
  intro hmem
  apply hz
  apply Finset.mem_image.mpr
  refine ⟨I * z, ?_, ?_⟩
  · simpa only [xiQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  · rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

#print axioms exists_zeta_quartet_log_filter
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
