import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCompletedDensity
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeUniformPrimeSum

/-!
# Gamma growth forces height tightness

Insert the archimedean coercivity and the mass-uniform prime aperture into the completed source
formula in density coordinates, discard the nonnegative polar term, and use that the divisor form is
nonpositive.  What is left is the confinement

`∫ log(2+|x|)·g_{a,p}(x)² dx ≤ B_C·‖g_{a,p}‖₂²`

with a constant depending only on the scaled degree, uniformly over every mass `a ≥ 4` and every
coefficient vector.  Chebyshev's inequality then makes the family uniformly tight in the height.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Integrability of the logarithmic moment -/

theorem continuous_routeULogWeight : Continuous fun x : ℝ => ((Real.log (2 + |x|) : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.log (continuous_const.add continuous_abs) fun x => ?_
  have h : (0 : ℝ) < 2 + |x| := by positivity
  exact ne_of_gt h

theorem norm_routeULogWeight_le (x : ℝ) :
    ‖((Real.log (2 + |x|) : ℝ) : ℂ)‖ ≤ 0 + Real.log (2 + |x|) := by
  have hlog : 0 ≤ Real.log (2 + |x|) := Real.log_nonneg (by
    have := abs_nonneg x
    linarith)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  linarith

theorem integrable_routeULogWeight_massKernel {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable fun x : ℝ => Real.log (2 + |x|) * (((a ^ 2 + x ^ 2) ^ (n + 1))⁻¹) := by
  refine integrable_of_integrable_ofReal ?_
  have h := integrable_logWeight_mul_massKernel continuous_routeULogWeight
    norm_routeULogWeight_le n (Y := a ^ 2) (by positivity)
  refine h.congr ?_
  filter_upwards with x
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]

theorem integrable_routeULog_mul_testSq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    Integrable fun x : ℝ => Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2 := by
  have hsum : Integrable fun x : ℝ =>
      ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
        (a ^ 2 * (routeUHardEdgeWeilPoly p).coeff k)
          * (Real.log (2 + |x|) * (((a ^ 2 + x ^ 2) ^ k)⁻¹)) := by
    refine integrable_finsetSum _ fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
    exact (integrable_routeULogWeight_massKernel ha j).const_mul _
  refine hsum.congr ?_
  filter_upwards with x
  rw [routeUHardEdgeRationalTest_sq_eq_sum ha p x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## The tightness constant -/

/-- The height-confinement constant attached to a scaled degree. -/
def routeUTightnessConst (C : ℝ) : ℝ :=
  2 * (routeUArchimedeanFloorConst + routeUPrimeUniformConst C)

/-- **(CSHC.3)/(CSHC.14) Gamma growth forces height tightness.** -/
theorem routeUHardEdge_log_moment_le {C a : ℝ} (hC : 0 < C) (ha : 4 ≤ a) (p : Polynomial ℝ)
    {N : ℕ} (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N) (hNC : (N : ℝ) ≤ C * a)
    (hW : (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q)).re ≤ 0) :
    (∫ x : ℝ, Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2)
      ≤ routeUTightnessConst C * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have ha2 : (1 : ℝ) / 2 < a := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpiC : (1 / (Real.pi : ℂ)) = (((1 / Real.pi : ℝ)) : ℂ) := by
    push_cast
    ring
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := ⟨_, rfl⟩
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hI_def]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  obtain ⟨J, hJ_def⟩ : ∃ J : ℝ,
      J = ∫ x : ℝ, routeUArchimedeanRate x * routeUHardEdgeRationalTest a p x ^ 2 := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : ℂ, S = ∑' m : ℕ,
      ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
        * routeUHardEdgeFourierSq a p (Real.log m) := ⟨_, rfl⟩
  -- the density identity, in real parts
  have hdens := tsum_routeUHardEdgeRationalTestSq_eq_density ha2 p
  rw [← hJ_def, ← hS_def, hpiC] at hdens
  have hre := congrArg Complex.re hdens
  rw [Complex.sub_re, Complex.add_re] at hre
  have hre1 : (2 * ((routeUHardEdgePolar a p : ℝ) : ℂ)).re = 2 * routeUHardEdgePolar a p := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hre2 : ((((1 / Real.pi : ℝ)) : ℂ) * ((J : ℝ) : ℂ)).re = (1 / Real.pi) * J := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hre3 : ((((1 / Real.pi : ℝ)) : ℂ) * S).re = (1 / Real.pi) * S.re := by
    rw [Complex.re_ofReal_mul]
  rw [hre1, hre2, hre3] at hre
  -- the prime bound
  have hnormS : S.re ≤ routeUPrimeUniformConst C * I := by
    have h1 : S.re ≤ ‖S‖ := Complex.re_le_norm S
    have h2 : ‖S‖ ≤ ∑' m : ℕ, ((ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m)
        * ‖routeUHardEdgeFourierSq a p (Real.log m)‖ := by
      rw [hS_def]
      refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq (tsum_congr fun m => ?_))
      · refine Summable.congr (summable_routeUHardEdgeFourierNorm hC ha p hN hNC) fun m => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 := routeUHardEdgePrimeSum_uniform_le hC ha p hN hNC
    rw [← hI_def] at h3
    linarith
  -- the polar term is nonnegative
  have hpolar : 0 ≤ routeUHardEdgePolar a p := routeUHardEdgePolar_nonneg ha2 p
  -- the archimedean term is bounded
  have hJ : J ≤ routeUPrimeUniformConst C * I := by
    have hstep : (1 / Real.pi) * J ≤ (1 / Real.pi) * (routeUPrimeUniformConst C * I) := by
      have hinv : (0 : ℝ) < 1 / Real.pi := by positivity
      nlinarith [hre, hW, hpolar, hnormS]
    have hinv : (0 : ℝ) < 1 / Real.pi := by positivity
    exact le_of_mul_le_mul_left (by linarith) hinv
  -- coercivity
  have hcoerc : (1 / 2) * (∫ x : ℝ, Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2)
      - routeUArchimedeanFloorConst * I ≤ J := by
    have hptwise : ∀ x : ℝ,
        (1 / 2) * (Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2)
          - routeUArchimedeanFloorConst * routeUHardEdgeRationalTest a p x ^ 2
        ≤ routeUArchimedeanRate x * routeUHardEdgeRationalTest a p x ^ 2 := by
      intro x
      have hg : 0 ≤ routeUHardEdgeRationalTest a p x ^ 2 := sq_nonneg _
      have hrate := routeUArchimedeanRate_ge x
      nlinarith
    have hint1 : Integrable fun x : ℝ =>
        (1 / 2) * (Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2)
          - routeUArchimedeanFloorConst * routeUHardEdgeRationalTest a p x ^ 2 :=
      ((integrable_routeULog_mul_testSq ha0 p).const_mul _).sub
        ((integrable_routeUHardEdgeRationalTest_sq ha0 p).const_mul _)
    have hint2 := integrable_routeUArchimedeanRate_mul_testSq ha0 p
    have hmono := MeasureTheory.integral_mono hint1 hint2 hptwise
    rw [MeasureTheory.integral_sub ((integrable_routeULog_mul_testSq ha0 p).const_mul _)
      ((integrable_routeUHardEdgeRationalTest_sq ha0 p).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hI_def,
      ← hJ_def] at hmono
    exact hmono
  rw [← hI_def, routeUTightnessConst]
  linarith


/-- **(CSHC.15) Uniform tightness.**  Normalized nonpositive packets of bounded scaled degree put
uniformly little mass beyond any height. -/
theorem routeUHardEdge_tail_le {C a : ℝ} (hC : 0 < C) (ha : 4 ≤ a) (p : Polynomial ℝ)
    {N : ℕ} (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N) (hNC : (N : ℝ) ≤ C * a)
    (hW : (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q)).re ≤ 0)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in {x : ℝ | R < |x|}, routeUHardEdgeRationalTest a p x ^ 2)
      ≤ (routeUTightnessConst C / Real.log (2 + R))
          * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hlogR : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  have hset : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hlogInt := integrable_routeULog_mul_testSq ha0 p
  have hgInt := integrable_routeUHardEdgeRationalTest_sq ha0 p
  have h1 : Real.log (2 + R) * ∫ x in {x : ℝ | R < |x|}, routeUHardEdgeRationalTest a p x ^ 2
      ≤ ∫ x in {x : ℝ | R < |x|}, Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on (hgInt.const_mul _).integrableOn
      hlogInt.integrableOn hset fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    have hg : 0 ≤ routeUHardEdgeRationalTest a p x ^ 2 := sq_nonneg _
    have hlog : Real.log (2 + R) ≤ Real.log (2 + |x|) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right hlog hg
  have h2 : (∫ x in {x : ℝ | R < |x|}, Real.log (2 + |x|)
        * routeUHardEdgeRationalTest a p x ^ 2)
      ≤ ∫ x : ℝ, Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2 := by
    refine MeasureTheory.setIntegral_le_integral hlogInt ?_
    filter_upwards with x
    have hg : 0 ≤ routeUHardEdgeRationalTest a p x ^ 2 := sq_nonneg _
    have hlog : 0 ≤ Real.log (2 + |x|) := Real.log_nonneg (by
      have := abs_nonneg x
      linarith)
    positivity
  have h3 := routeUHardEdge_log_moment_le hC ha p hN hNC hW
  rw [div_mul_eq_mul_div, le_div_iff₀ hlogR]
  calc (∫ x in {x : ℝ | R < |x|}, routeUHardEdgeRationalTest a p x ^ 2) * Real.log (2 + R)
      = Real.log (2 + R) * ∫ x in {x : ℝ | R < |x|},
          routeUHardEdgeRationalTest a p x ^ 2 := by ring
    _ ≤ ∫ x : ℝ, Real.log (2 + |x|) * routeUHardEdgeRationalTest a p x ^ 2 := by linarith
    _ ≤ routeUTightnessConst C * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := h3

end RHTower

end
