import GaloisForLFunctions.HTGeometry.WeightedJetControl
import GaloisForLFunctions.HTGeometry.FlattenedCauchyJetRigidity
import GaloisForLFunctions.HTGeometry.SignedCauchyJetDetection

/-!
# Surjectivity of the weighted Cauchy-jet control map

Indicators are bounded, hence bounded reweightings, whatever the mass of the base measure.  The
`indicatorConstLp` interface is unavailable here because it asks for a set of finite measure, but at
exponent `∞` boundedness alone suffices, so the indicator is built directly from its uniform bound.

The control map sends the indicator of `S` to the weighted kernels integrated over `S`.  A
real-linear functional annihilating the range therefore forces `Re (w * Q) = 0` almost everywhere,
where `Q` is the jet form of its coefficient packet.  Strict positivity of the density cancels `w`,
and the signed detector kills the coefficients when the base measure has infinite support.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- One weighted kernel coordinate is integrable against the base measure. -/
theorem integrable_weight_mul_cauchyJetKernel (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) (s : jetIndex n) :
    Integrable (fun t => ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) μ := by
  refine Integrable.mono' ((hw.abs).const_mul (cauchyJetKernelBound x n s)) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hw.aestronglyMeasurable).mul (aestronglyMeasurable_cauchyJetKernel μ x n s)
  · filter_upwards with t
    rw [norm_mul, Complex.norm_real]
    calc ‖w t‖ * ‖cauchyJetKernel x n t s‖
        ≤ ‖w t‖ * cauchyJetKernelBound x n s :=
          mul_le_mul_of_nonneg_left (norm_cauchyJetKernel_le x hne n s t)
            (norm_nonneg _)
      _ = cauchyJetKernelBound x n s * |w t| := by
          rw [Real.norm_eq_abs]; ring

omit [DecidableEq ι] in
/-- The weighted jet form is integrable against the base measure. -/
theorem integrable_weight_mul_jetForm (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (c : jetIndex n → ℂ) :
    Integrable (fun t => ((w t : ℝ) : ℂ) *
      (∑ s : jetIndex n, c s * cauchyJetKernel x n t s)) μ := by
  have hrw : (fun t => ((w t : ℝ) : ℂ) *
      (∑ s : jetIndex n, c s * cauchyJetKernel x n t s)) =
      fun t => ∑ s : jetIndex n,
        c s * (((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) := by
    funext t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hrw]
  exact integrable_finsetSum _ fun s _ =>
    (integrable_weight_mul_cauchyJetKernel μ w hw x hne n s).const_mul (c s)

/-- The indicator of a measurable set as a bounded reweighting.  No finiteness of the set is
required, since at exponent `∞` boundedness is the only condition. -/
def indicatorLpTop (μ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) : Lp ℝ ⊤ μ :=
  (memLp_top_of_bound (f := S.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hS).aestronglyMeasurable 1
    (by
      filter_upwards with t
      by_cases h : t ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])).toLp _

theorem indicatorLpTop_coeFn (μ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    indicatorLpTop μ hS =ᵐ[μ] S.indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

set_option linter.unusedSectionVars false in
/-- The weighted control map sends an indicator to the weighted kernels over that set. -/
theorem weightedJetControl_indicatorLpTop (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    {S : Set ℝ} (hS : MeasurableSet S) (s : jetIndex n) :
    weightedJetControl μ w hw x hne n (indicatorLpTop μ hS) s =
      ∫ t in S, ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ := by
  rw [weightedJetControl_apply]
  have hae : ∀ᵐ t ∂μ,
      ((indicatorLpTop μ hS t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) *
          cauchyJetKernel x n t s =
        S.indicator (fun t => ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) t := by
    filter_upwards [indicatorLpTop_coeFn μ hS] with t ht
    rw [ht]
    by_cases h : t ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [integral_congr_ae hae, integral_indicator hS]

/-- **Surjectivity of the weighted control map.**  For a base measure of infinite support with a
strictly positive integrable density, every finite Cauchy-jet vector is realized by a bounded
reweighting.  No finiteness of the base measure is used. -/
theorem surjective_weightedJetControl (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) :
    Function.Surjective
      (weightedJetControl μ w hw x (fun i => ne_of_gt (hupper i)) n) := by
  classical
  set hne : ∀ i, (x i).im ≠ 0 := fun i => ne_of_gt (hupper i) with hnedef
  apply surjective_of_forall_coefficients_eq_zero
    (weightedJetControl μ w hw x hne n).toLinearMap
  intro c hc
  have hQint := integrable_weight_mul_jetForm μ w hw x hne n c
  -- Annihilation on indicators gives vanishing real parts of all set integrals.
  have hset : ∀ S : Set ℝ, MeasurableSet S → μ S < ⊤ →
      ∫ t in S, (((w t : ℝ) : ℂ) *
        (∑ s : jetIndex n, c s * cauchyJetKernel x n t s)).re ∂μ = 0 := by
    intro S hS _
    have hind := hc (indicatorLpTop μ hS)
    have hrw : ∀ s : jetIndex n,
        (weightedJetControl μ w hw x hne n) (indicatorLpTop μ hS) s =
          ∫ t in S, ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
      fun s => weightedJetControl_indicatorLpTop μ w hw x hne n hS s
    simp only [ContinuousLinearMap.coe_coe, hrw] at hind
    have hexch : ∑ s : jetIndex n, c s *
          ∫ t in S, ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ =
        ∫ t in S, ((w t : ℝ) : ℂ) *
          (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ := by
      have hstep1 : ∑ s : jetIndex n, c s *
            ∫ t in S, ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ =
          ∑ s : jetIndex n,
            ∫ t in S, c s * (((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) ∂μ :=
        Finset.sum_congr rfl fun s _ => (integral_const_mul _ _).symm
      have hstep2 : ∑ s : jetIndex n,
            ∫ t in S, c s * (((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) ∂μ =
          ∫ t in S, ∑ s : jetIndex n,
            c s * (((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) ∂μ := by
        rw [integral_finsetSum]
        intro s _
        exact ((integrable_weight_mul_cauchyJetKernel μ w hw x hne n s).restrict).const_mul (c s)
      have hstep3 : ∫ t in S, ∑ s : jetIndex n,
            c s * (((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) ∂μ =
          ∫ t in S, ((w t : ℝ) : ℂ) *
            (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hstep1, hstep2, hstep3]
    have hcomm : ∫ t in S, (((w t : ℝ) : ℂ) *
          (∑ s : jetIndex n, c s * cauchyJetKernel x n t s)).re ∂μ =
        (∫ t in S, ((w t : ℝ) : ℂ) *
          (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ).re :=
      Complex.reCLM.integral_comp_comm hQint.restrict
    rw [hcomm, ← hexch]
    exact hind
  have hae := Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hQint.re hset
  -- Cancel the strictly positive density.
  have hQre : ∀ᵐ t ∂μ,
      (cauchyJetForm x n (fun i j => c ⟨i, j⟩) t).re = 0 := by
    filter_upwards [hae] with t ht
    have hmul : w t * (∑ s : jetIndex n, c s * cauchyJetKernel x n t s).re = 0 := by
      simpa [Complex.re_ofReal_mul] using ht
    have hzero := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (hwpos t))
    rw [← sum_cauchyJetKernel_eq_cauchyJetForm x n c t]
    exact hzero
  have hcurried :=
    cauchyJet_coeff_eq_zero_of_ae_re hsupp x hx hupper n
      (fun i j => c ⟨i, j⟩) hQre
  intro s
  exact hcurried s.1 s.2

end

end GaloisForLFunctions.HTGeometry
