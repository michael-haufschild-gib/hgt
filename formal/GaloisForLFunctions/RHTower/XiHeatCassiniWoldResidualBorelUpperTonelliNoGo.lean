import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelSourceLaplace
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualUpperAbscissa
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalGraphNoGo
import GaloisForLFunctions.HTGeometry.NevanlinnaPickGramSplitting

/-!
# Positive-ray Tonelli obstruction for the Route-T residual Borel carrier

On the positive normal Borel ray, the real second-factorial kernel is positive and monotone.
Consequently the integrated norm of each source-ordered Borel edge equals, exactly, the norm of
the corresponding upper-Hardy residual edge.  Absolute Borel--Laplace Fubini is therefore
equivalent to the already-isolated upper residual variation.  At critical half depth it is
incompatible with Route T's critical mesh energy, proving that C5b must use lateral cancellation
or renormalized continuation before taking absolute values.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real positive-axis form of the second-factorial Borel kernel. -/
def secondFactorialBorelRealKernel (r : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ k / ((k.factorial : ℝ) ^ 2)

theorem summable_secondFactorialBorelRealKernelTerm (r : ℝ) :
    Summable (fun k : ℕ => r ^ k / ((k.factorial : ℝ) ^ 2)) := by
  apply Summable.of_norm
  have hmajor := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) |r|).summable
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hmajor
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (sq_nonneg (k.factorial : ℝ))]
  have hkNat : 1 ≤ k.factorial :=
    Nat.one_le_iff_ne_zero.mpr k.factorial_ne_zero
  have hk : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast hkNat
  have hkpos : 0 < (k.factorial : ℝ) := by positivity
  exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg r) k) hkpos
    (by nlinarith [sq_nonneg ((k.factorial : ℝ) - 1)])

theorem secondFactorialBorelKernel_ofReal
    (r : ℝ) :
    secondFactorialBorelKernel (r : ℂ) =
      (secondFactorialBorelRealKernel r : ℂ) := by
  rw [secondFactorialBorelKernel, secondFactorialBorelRealKernel]
  calc
    (∑' k : ℕ, (r : ℂ) ^ k / ((k.factorial : ℂ) ^ 2)) =
        ∑' k : ℕ, ((r ^ k / ((k.factorial : ℝ) ^ 2) : ℝ) : ℂ) := by
      apply tsum_congr
      intro k
      push_cast
      rfl
    _ = ((∑' k : ℕ, r ^ k / ((k.factorial : ℝ) ^ 2) : ℝ) : ℂ) := by
      rw [← Complex.ofRealCLM_apply]
      exact (ContinuousLinearMap.map_tsum Complex.ofRealCLM
        (summable_secondFactorialBorelRealKernelTerm r)).symm

theorem secondFactorialBorelRealKernel_mono
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    secondFactorialBorelRealKernel r ≤ secondFactorialBorelRealKernel R := by
  rw [secondFactorialBorelRealKernel, secondFactorialBorelRealKernel]
  refine Summable.tsum_le_tsum (fun k => ?_)
    (summable_secondFactorialBorelRealKernelTerm r)
    (summable_secondFactorialBorelRealKernelTerm R)
  have hfac : 0 ≤ ((k.factorial : ℝ) ^ 2) := sq_nonneg _
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hrR k) hfac

/-- One source-ordered atom on the positive normal Borel ray. -/
def xiHeatCassiniWoldResidualBorelUpperRaySourceAtom
    (x s : ℝ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeNegativePhase N x *
        secondFactorialBorelKernel
          ((xiMassNthPrimeLogHeight N * s : ℝ) : ℂ) -
      xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x *
        secondFactorialBorelKernel
          ((xiMassNthPrimeLogHeight (N + 1) * s : ℝ) : ℂ))

def xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) : ℝ) : ℂ) *
    xiHeatCassiniWoldResidualBorelUpperRaySourceAtom x (y * t) N

private theorem ordered_upperKernel
    {h H y t : ℝ} (hh : 0 ≤ h) (hH : h ≤ H)
    (hy : 0 ≤ y) (ht : 0 ≤ t) :
    secondFactorialBorelRealKernel (h * (y * t)) ≤
      secondFactorialBorelRealKernel (H * (y * t)) := by
  exact secondFactorialBorelRealKernel_mono
    (mul_nonneg hh (mul_nonneg hy ht))
    (mul_le_mul_of_nonneg_right hH (mul_nonneg hy ht))

theorem norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero
    {y t : ℝ} (hy : 0 ≤ y) (ht : 0 ≤ t) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖ =
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * Real.exp (-t) *
        (secondFactorialBorelRealKernel
            (xiMassNthPrimeLogHeight (N + 1) * (y * t)) -
          secondFactorialBorelRealKernel
            (xiMassNthPrimeLogHeight N * (y * t))) := by
  have hh : 0 ≤ xiMassNthPrimeLogHeight N :=
    (xiMassNthPrimeLogHeight_pos N).le
  have hH : xiMassNthPrimeLogHeight N ≤ xiMassNthPrimeLogHeight (N + 1) :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hmono := ordered_upperKernel hh hH hy ht
  rw [xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom,
    xiHeatCassiniWoldResidualBorelUpperRaySourceAtom]
  simp only [xiHeatCassiniOrderedPrimeNegativePhase, Complex.ofReal_zero,
    mul_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [
    secondFactorialBorelKernel_ofReal,
    secondFactorialBorelKernel_ofReal]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hmono)]
  ring

private theorem secondFactorialBorelKernel_upperRay_mul
    (h y t : ℝ) :
    secondFactorialBorelKernel (((h * (y * t) : ℝ) : ℂ)) =
      secondFactorialBorelKernel ((((h * y : ℝ) : ℂ)) * (t : ℂ)) := by
  congr 1
  push_cast
  ring

theorem integrableOn_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    IntegrableOn
      (xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y N) (Ioi 0) := by
  let R : ℂ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let B : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let w : ℂ := ((h * y : ℝ) : ℂ)
  let W : ℂ := ((H * y : ℝ) : ℂ)
  have hf := (integrableOn_exp_neg_mul_secondFactorialBorelKernel w).const_mul A
  have hg := (integrableOn_exp_neg_mul_secondFactorialBorelKernel W).const_mul B
  apply MeasureTheory.IntegrableOn.congr_fun ((hf.sub hg).const_mul R)
  · intro t ht
    rw [xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom,
      xiHeatCassiniWoldResidualBorelUpperRaySourceAtom,
      secondFactorialBorelKernel_upperRay_mul,
      secondFactorialBorelKernel_upperRay_mul]
    dsimp only [R, A, B, h, H, w, W]
    simp only [Pi.sub_apply]
    ring
  · exact measurableSet_Ioi

private theorem integrableOn_exp_neg_mul_secondFactorialBorelRealKernel (w : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-t) * secondFactorialBorelRealKernel (w * t)) (Ioi 0) := by
  have hc := integrableOn_exp_neg_mul_secondFactorialBorelKernel (w : ℂ)
  apply MeasureTheory.IntegrableOn.congr_fun hc.re
  · intro t ht
    have hwt : (w : ℂ) * (t : ℂ) = ((w * t : ℝ) : ℂ) := by
      push_cast
      rfl
    change (((Real.exp (-t) : ℝ) : ℂ) *
      secondFactorialBorelKernel ((w : ℂ) * (t : ℂ))).re = _
    rw [hwt, secondFactorialBorelKernel_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  · exact measurableSet_Ioi

private theorem integral_exp_neg_mul_secondFactorialBorelRealKernel (w : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-t) * secondFactorialBorelRealKernel (w * t)) =
      Real.exp w := by
  have hr := integrableOn_exp_neg_mul_secondFactorialBorelRealKernel w
  have hc := integral_secondFactorialBorelKernel_eq_exp (w : ℂ)
  rw [show (fun t : ℝ =>
      ((Real.exp (-t) : ℝ) : ℂ) *
        secondFactorialBorelKernel ((w : ℂ) * (t : ℂ))) =
      fun t : ℝ =>
        ((Real.exp (-t) * secondFactorialBorelRealKernel (w * t) : ℝ) : ℂ) by
    funext t
    rw [show (w : ℂ) * (t : ℂ) = ((w * t : ℝ) : ℂ) by
      push_cast
      rfl,
      secondFactorialBorelKernel_ofReal]
    push_cast
    rfl] at hc
  rw [GaloisForLFunctions.HTGeometry.integral_ofReal_eq hr] at hc
  rw [← Complex.ofReal_exp] at hc
  exact Complex.ofReal_injective hc

/-- At `x=0`, the integrated absolute mass of one positive-ray Borel atom is exactly the mass of
the corresponding upper-Hardy edge. -/
theorem integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero
    {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖) =
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (I * (y : ℂ)) N‖ := by
  let Rabs : ℝ := |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N|
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let f : ℝ → ℝ := fun t =>
    Real.exp (-t) * secondFactorialBorelRealKernel ((H * y) * t)
  let g : ℝ → ℝ := fun t =>
    Real.exp (-t) * secondFactorialBorelRealKernel ((h * y) * t)
  have hf : IntegrableOn f (Ioi 0) := by
    dsimp only [f]
    exact integrableOn_exp_neg_mul_secondFactorialBorelRealKernel (H * y)
  have hg : IntegrableOn g (Ioi 0) := by
    dsimp only [g]
    exact integrableOn_exp_neg_mul_secondFactorialBorelRealKernel (h * y)
  calc
    (∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖) =
        ∫ t : ℝ in Ioi 0, Rabs * (f t - g t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖ =
        Rabs * (f t - g t)
      rw [norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero
        hy (le_of_lt ht) N]
      dsimp only [Rabs, f, g, h, H]
      ring
    _ = Rabs * ((∫ t : ℝ in Ioi 0, f t) - ∫ t : ℝ in Ioi 0, g t) := by
      rw [integral_const_mul, integral_sub hf hg]
    _ = Rabs * (Real.exp (H * y) - Real.exp (h * y)) := by
      rw [show (∫ t : ℝ in Ioi 0, f t) = Real.exp (H * y) by
          exact integral_exp_neg_mul_secondFactorialBorelRealKernel (H * y),
        show (∫ t : ℝ in Ioi 0, g t) = Real.exp (h * y) by
          exact integral_exp_neg_mul_secondFactorialBorelRealKernel (h * y)]
    _ = ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (I * (y : ℂ)) N‖ := by
      rw [norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I hy]
      dsimp only [Rabs, h, H]
      rw [show xiMassNthPrimeLogHeight (N + 1) =
          xiMassNthPrimeLogHeight N + xiHeatCassiniOrderedPrimeLogGap N by
        dsimp only [xiHeatCassiniOrderedPrimeLogGap]
        ring,
        add_mul, Real.exp_add]
      ring

/-- Exact positive-ray Tonelli gate: atomwise absolute Borel--Laplace interchange is equivalent to
the corpus upper residual variation, not a weaker analytic prerequisite. -/
theorem summable_integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero_iff
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    Summable (fun N : ℕ => ∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖) ↔
      Summable (xiHeatCassiniWoldResidualUpperVariationAtom y) := by
  rw [show (fun N : ℕ => ∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 y N t‖) =
      fun N : ℕ => ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (I * (y : ℂ)) N‖ by
    funext N
    exact integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero
      hy.le N]
  exact summable_norm_residualAtom_mul_I_iff_upperVariation hy hy1

/-- At critical half depth, the naive positive-ray absolute-Tonelli route is incompatible with
the critical mesh energy already required by Route T. Any viable C5b proof must therefore use a
genuinely lateral cancellation or renormalized continuation. -/
theorem not_summable_integral_norm_upperRaySourceLaplaceAtom_zero_and_criticalEnergy :
    ¬ (Summable (fun N : ℕ => ∫ t : ℝ in Ioi 0,
          ‖xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom 0 (1 / 2) N t‖) ∧
        Summable xiHeatCassiniPrimeGapCriticalEnergy) := by
  rintro ⟨hBorel, henergy⟩
  apply not_half_residualUpperVariation_and_primeGapCriticalEnergy
  exact ⟨
    (summable_integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero_iff
      (by norm_num) (by norm_num)).mp hBorel,
    henergy⟩

end

end RHTower
