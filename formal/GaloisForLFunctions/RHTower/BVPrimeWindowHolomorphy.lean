import GaloisForLFunctions.RHTower.BVPrimeWindowQuadrature
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of bounded-variation prime-window remainders

The compact-uniform BV estimate from `BVPrimeWindowQuadrature` is combined here with
differentiation under the integral and locally normal convergence.  This supplies the concrete
holomorphic error term on `Re s > 1/2` for every compact BV window.
-/

open Complex Filter Function Finset MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- The clamped positive Mellin base is continuous. -/
theorem continuous_mellinBase (W : CompactBVPrimeWindow) : Continuous W.mellinBase := by
  exact continuous_subtype_val.comp
    (LipschitzWith.projIcc W.lower_le_upper).continuous

/-- For fixed Mellin coordinate, the clamped Mellin weight is continuous in the real variable. -/
theorem continuous_mellinWeight (W : CompactBVPrimeWindow) (s : ℂ) :
    Continuous (W.mellinWeight s) := by
  unfold mellinWeight
  rw [← continuousOn_univ]
  apply ContinuousOn.cpow_const
    (Complex.continuous_ofReal.comp W.continuous_mellinBase).continuousOn
  intro x hx
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using W.mellinBase_pos x

private theorem hasDerivAt_mellinWeight_coordinate
    (W : CompactBVPrimeWindow) (x : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ W.mellinWeight z x)
      (-(Real.log (W.mellinBase x) : ℂ) * W.mellinWeight s x) s := by
  have h := ((hasDerivAt_id s).neg).const_cpow
    (c := (W.mellinBase x : ℂ))
    (Or.inl (by exact_mod_cast (W.mellinBase_pos x).ne'))
  rw [← Complex.ofReal_log (W.mellinBase_pos x).le] at h
  convert h using 1 <;> simp [mellinWeight, Function.id_def] <;> ring

/-- The compactly supported BV Mellin transform is entire. -/
theorem differentiable_mellinTransform (W : CompactBVPrimeWindow) :
    Differentiable ℂ W.mellinTransform := by
  intro s₀
  let K : Set ℂ := Metric.closedBall s₀ 1
  have hK : IsCompact K := isCompact_closedBall s₀ 1
  have hKne : K.Nonempty := ⟨s₀, Metric.mem_closedBall_self (by norm_num)⟩
  obtain ⟨Mh, C, hMh0, hMh, hLip⟩ :=
    W.exists_mellinWeight_uniform_lipschitz_bound hK hKne
  have hlogCont : ContinuousOn (fun x : ℝ ↦ |Real.log x|)
      (Set.Icc W.lower W.upper) :=
    (ContinuousOn.abs <| Real.continuousOn_log.mono fun x hx ↦
      (W.lower_pos.trans_le hx.1).ne')
  obtain ⟨L, hL⟩ := (isCompact_Icc : IsCompact (Set.Icc W.lower W.upper)).exists_bound_of_continuousOn
    hlogCont
  have hL0 : 0 ≤ L := by
    exact (abs_nonneg (Real.log W.lower)).trans (by
      simpa only [Real.norm_eq_abs, abs_abs] using
        hL W.lower ⟨le_rfl, W.lower_le_upper⟩)
  let B : ℝ := Mh * L
  have hB0 : 0 ≤ B := mul_nonneg hMh0 hL0
  let F : ℂ → ℝ → ℂ := fun z x ↦ W.mellinIntegrand z x
  let F' : ℂ → ℝ → ℂ := fun z x ↦
    W x * (-(Real.log (W.mellinBase x) : ℂ) * W.mellinWeight z x)
  have hFmeas : ∀ᶠ z in nhds s₀, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    exact (W.mellinIntegrand_integrable z).aestronglyMeasurable
  have hFint : Integrable (F s₀) volume := W.mellinIntegrand_integrable s₀
  have hfactorCont : Continuous (fun x : ℝ ↦
      -(Real.log (W.mellinBase x) : ℂ) * W.mellinWeight s₀ x) := by
    have hlog : Continuous (fun x : ℝ ↦ Real.log (W.mellinBase x)) :=
      W.continuous_mellinBase.log fun x ↦ (W.mellinBase_pos x).ne'
    exact (Complex.continuous_ofReal.comp hlog).neg.mul (W.continuous_mellinWeight s₀)
  have hF'meas : AEStronglyMeasurable (F' s₀) volume := by
    exact W.integrable.aestronglyMeasurable.mul hfactorCont.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume, ∀ z ∈ Metric.ball s₀ 1,
      ‖F' z x‖ ≤ B * ‖W x‖ := by
    filter_upwards with x
    intro z hz
    have hzK : z ∈ K := Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz))
    have hbaseMem := W.mellinBase_mem x
    have hlogBound : |Real.log (W.mellinBase x)| ≤ L := by
      have := hL (W.mellinBase x) hbaseMem
      simpa only [Real.norm_eq_abs, abs_abs] using this
    dsimp only [F', B]
    rw [norm_mul, norm_mul, norm_neg, norm_real]
    calc
      ‖W x‖ * (|Real.log (W.mellinBase x)| * ‖W.mellinWeight z x‖) ≤
          ‖W x‖ * (L * Mh) := by
        gcongr
        exact hMh z hzK x
      _ = Mh * L * ‖W x‖ := by ring
  have hboundInt : Integrable (fun x ↦ B * ‖W x‖) volume :=
    W.integrable.norm.const_mul B
  have hdiff : ∀ᵐ x ∂volume, ∀ z ∈ Metric.ball s₀ 1,
      HasDerivAt (fun w : ℂ ↦ F w x) (F' z x) z := by
    filter_upwards with x
    intro z hz
    exact (hasDerivAt_mellinWeight_coordinate W x z).const_mul (W x)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x ↦ B * ‖W x‖)
    (s := Metric.ball s₀ 1) (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ (by norm_num)) hFmeas hFint hF'meas
    hbound hboundInt hdiff
  exact hmain.2.differentiableAt

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Every finite mesh Riemann sum is entire in the Mellin coordinate. -/
theorem differentiable_gridRiemannSum (W : CompactBVPrimeWindow) (k : ℕ) :
    Differentiable ℂ (W.gridRiemannSum k) := by
  intro s
  unfold gridRiemannSum
  have hsum : DifferentiableAt ℂ
      (fun z => ∑ i ∈ Finset.range (W.gridCount k),
        W.mellinIntegrand z (((i + 1 : ℕ) : ℝ) / k)) s := by
    apply DifferentiableAt.fun_sum
    intro i hi
    exact (hasDerivAt_mellinWeight_coordinate W (((i + 1 : ℕ) : ℝ) / k) s).differentiableAt.const_mul
      (W (((i + 1 : ℕ) : ℝ) / k))
  exact hsum.const_smul ((1 / (k : ℝ)) : ℝ)

/-- The unscaled grid error is entire. -/
theorem differentiable_gridError (W : CompactBVPrimeWindow) (k : ℕ) :
    Differentiable ℂ (W.gridError k) :=
  (W.differentiable_gridRiemannSum k).sub W.differentiable_mellinTransform

/-- For positive scale, the Mellin-scaled grid error is entire. -/
theorem differentiable_scaledGridError (W : CompactBVPrimeWindow) {k : ℕ} (hk : 0 < k) :
    Differentiable ℂ (W.scaledGridError k) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  exact ((differentiable_id.const_sub 1).const_cpow (Or.inl hkC)).mul
    (W.differentiable_gridError k)

/-- One von-Mangoldt-weighted BV quadrature remainder. -/
def errorSummand (W : CompactBVPrimeWindow) (s : ℂ) (k : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
    W.scaledGridError k s

/-- Every weighted BV error term is entire, including the zero index where the arithmetic weight
vanishes. -/
theorem differentiable_errorSummand (W : CompactBVPrimeWindow) (k : ℕ) :
    Differentiable ℂ (fun s => W.errorSummand s k) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hzero : (fun s => W.errorSummand s 0) = fun _ => 0 := by
      funext s
      simp [errorSummand]
    rw [hzero]
    fun_prop
  · unfold errorSummand
    exact (differentiable_const
      (((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ))).mul
        (W.differentiable_scaledGridError hk)

/-- Holomorphic BV quadrature remainder candidate. -/
def errorSeries (W : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  ∑' k : ℕ, W.errorSummand s k

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- The von-Mangoldt-weighted BV error family converges locally normally on `Re s > 1/2`. -/
theorem summableLocallyUniformlyOn_errorSummand (W : CompactBVPrimeWindow) :
    SummableLocallyUniformlyOn
      (fun k : ℕ => fun s : ℂ => W.errorSummand s k)
      {s : ℂ | 1 / 2 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 1 / 2 < s.re at hs
  let r : ℝ := (s.re - 1 / 2) / 2
  let sigma : ℝ := s.re - r
  have hr : 0 < r := by dsimp only [r]; linarith
  have hsigma : 1 / 2 < sigma := by dsimp only [sigma, r]; linarith
  let K : Set ℂ := Metric.closedBall s r
  have hK : IsCompact K := isCompact_closedBall s r
  have hKne : K.Nonempty := ⟨s, Metric.mem_closedBall_self hr.le⟩
  obtain ⟨Q, hQ0, hQ⟩ := W.exists_uniform_norm_scaledGridError_le_rpow hK hKne
  let z : ℂ := ((sigma + 1 / 2 : ℝ) : ℂ)
  have hz : 1 < z.re := by
    dsimp only [z]
    simp only [ofReal_re]
    linarith
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hmajor : Summable (fun k => Q *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
    hvm.norm.mul_left Q
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable hmajor
  intro k x hx
  have hxball : ‖x - s‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hx
  have hxK : x ∈ K := Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))
  have hxre : sigma < x.re := by
    have hre := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re] at hre
    have hreLower := (abs_le.mp hre).1
    dsimp only [sigma]
    linarith
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [errorSummand]
  · have hk1 : 1 ≤ k := hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have herr := hQ x hxK k hk1
    rw [errorSummand, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_nonneg k))]
    calc
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          ‖W.scaledGridError k x‖ ≤
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (Q * (k : ℝ) ^ (-x.re)) := by
            exact mul_le_mul_of_nonneg_left herr
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (Real.sqrt_nonneg k))
      _ ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (Q * (k : ℝ) ^ (-sigma)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast hk1) (by linarith)) hQ0
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.sqrt_nonneg k)
      _ = Q * ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
        rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hk]
        simp only [z, ofReal_re]
        rw [Real.sqrt_eq_rpow]
        rw [show ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (1 / 2 : ℝ) *
            (Q * (k : ℝ) ^ (-sigma)) =
          Q * ArithmeticFunction.vonMangoldt k *
            ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-sigma)) by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le]
              ring]
        rw [← Real.rpow_add hkreal]
        rw [show -(1 / 2 : ℝ) + -sigma = -(sigma + 1 / 2) by ring]
        rw [Real.rpow_neg hkreal.le]
        field_simp

/-- The weighted BV error series is holomorphic on the full quadrature half-plane. -/
theorem differentiableOn_errorSeries_rightHalf (W : CompactBVPrimeWindow) :
    DifferentiableOn ℂ W.errorSeries {s : ℂ | 1 / 2 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    W.summableLocallyUniformlyOn_errorSummand
  intro k s hs
  exact W.differentiable_errorSummand k s

end CompactBVPrimeWindow
end RHTower
