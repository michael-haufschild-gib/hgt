import GaloisForLFunctions.RHTower.BaezDuarteWaveletFourier
import GaloisForLFunctions.RHTower.MobiusCriticalLaplaceIdentity
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import GaloisForLFunctions.RHTower.BaezDuarteWaveletPairing

/-!
# The zero-free-line beta integral

Pairing the `e^{-σt}`-damped critical Möbius boundary vector against the beta wavelet and applying
Plancherel on the vertical line `Re w = σ` turns the Báez--Duarte coefficient into a beta-smoothed
integral of reciprocal zeta.  Removing the damping is dominated convergence, because the wavelet
pairing is already absolutely convergent.
-/

namespace RHTower

open MeasureTheory FourierTransform GaloisForLFunctions.HTGeometry

noncomputable section

theorem memLp_criticalMertens_restrict :
    MemLp criticalMertensVector 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  memLp_criticalMertensVector.restrict _

theorem laplaceRay_criticalMertensVector {w : ℂ} (hw : 0 < w.re) :
    laplaceRay criticalMertensVector w = centeredSchurLimit w := by
  rw [← causalTransform_criticalMertensVector hw, laplaceRay, causalTransform]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [expRay]
  ring_nf

theorem inner_lp_volume_eq (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ f g : ℂ) = ∫ x : ℝ, (starRingEnd ℂ) (f x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x) : ℂ) = _
  rw [RCLike.inner_apply]
  ring

/-- The critical Möbius boundary vector is real. -/
theorem conj_criticalMertensVector (t : ℝ) :
    (starRingEnd ℂ) (criticalMertensVector t) = criticalMertensVector t := by
  rw [criticalMertensVector]
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht, mobiusWeightedPartial, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mobiusRealWeight]
    split_ifs
    · rw [map_zero]
    · rw [map_mul, Complex.conj_ofReal]
      congr 1
      exact map_intCast (starRingEnd ℂ) _
  · rw [Set.indicator_of_notMem ht, map_zero]

theorem conj_bdKernelVector (k : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (bdKernelVector k t) = bdKernelVector k t := by
  rw [bdKernelVector]
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht, Complex.conj_ofReal]
  · rw [Set.indicator_of_notMem ht, map_zero]

/-- The `σ`-damped critical Möbius vector as an `L²` element. -/
def dampedMertensLp {σ : ℝ} (hσ : 0 ≤ σ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_rayDamp memLp_criticalMertens_restrict hσ).toLp (rayDamp criticalMertensVector σ)

/-- The beta wavelet as an `L²` element. -/
def bdKernelLp (k : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_bdKernelVector k).toLp (bdKernelVector k)

theorem coeFn_fourierTransform_bdKernelLp (k : ℕ) :
    ((𝓕 (bdKernelLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => 𝓕 (bdKernelVector k) ξ := by
  have hgm := memLp_bdKernelVector k
  have hgi := integrable_bdKernelVector k
  have hGcoe : ((bdKernelLp k : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] bdKernelVector k := hgm.coeFn_toLp
  have hGint : Integrable ((bdKernelLp k : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    hgi.congr hGcoe.symm
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable (bdKernelLp k) hGint
  filter_upwards [hbridge] with ξ hξ
  rw [hξ, Real.Lp.fourierTransform_apply]
  have hcoe : (((memLp_one_iff_integrable.mpr hGint).toLp
      ((bdKernelLp k : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) : ℝ → ℂ)
      =ᵐ[volume] bdKernelVector k :=
    ((memLp_one_iff_integrable.mpr hGint).coeFn_toLp).trans hGcoe
  exact Real.fourier_congr_ae hcoe ξ

/-- **The spectral side.**  The damped pairing is the zero-free-line beta integral. -/
theorem inner_damped_bdKernel {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    (inner ℂ (dampedMertensLp hσ.le) (bdKernelLp k) : ℂ)
      = ∫ ξ : ℝ,
          (starRingEnd ℂ) (centeredSchurLimit (rayLine σ ξ)) * 𝓕 (bdKernelVector k) ξ := by
  rw [← Lp.inner_fourier_eq, inner_lp_volume_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierTransform_rayDamp memLp_criticalMertens_restrict hσ,
    coeFn_fourierTransform_bdKernelLp k] with ξ h1 h2
  rw [dampedMertensLp] at *
  rw [h1, h2, laplaceRay_criticalMertensVector (by simpa using hσ)]

/-- **The time side.**  The damped pairing is the damped wavelet pairing. -/
theorem inner_damped_bdKernel_time {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    (inner ℂ (dampedMertensLp hσ.le) (bdKernelLp k) : ℂ)
      = ∫ t in Set.Ioi (0 : ℝ),
          mobiusWeightedPartial 1 t * ((Real.exp (-(σ * t)) : ℝ) : ℂ)
            * ((bdKernel k t : ℝ) : ℂ) := by
  rw [inner_lp_volume_eq]
  have hA : ((dampedMertensLp hσ.le : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] rayDamp criticalMertensVector σ :=
    (memLp_two_rayDamp memLp_criticalMertens_restrict hσ.le).coeFn_toLp
  have hB : ((bdKernelLp k : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] bdKernelVector k := (memLp_bdKernelVector k).coeFn_toLp
  have hcong : (∫ x : ℝ, (starRingEnd ℂ) ((dampedMertensLp hσ.le : ℝ → ℂ) x)
        * ((bdKernelLp k : ℝ → ℂ) x))
      = ∫ x : ℝ, (starRingEnd ℂ) (rayDamp criticalMertensVector σ x) * bdKernelVector k x := by
    refine integral_congr_ae ?_
    filter_upwards [hA, hB] with x h1 h2
    rw [h1, h2]
  rw [hcong]
  have hfun : (fun x : ℝ => (starRingEnd ℂ) (rayDamp criticalMertensVector σ x)
      * bdKernelVector k x)
      = Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ =>
          mobiusWeightedPartial 1 t * ((Real.exp (-(σ * t)) : ℝ) : ℂ)
            * ((bdKernel k t : ℝ) : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx, rayDamp, Set.indicator_of_mem hx, bdKernelVector,
        Set.indicator_of_mem hx, map_mul, conj_criticalMertensVector, criticalMertensVector,
        Set.indicator_of_mem hx]
      congr 1
      rw [expRay]
      have hre : (starRingEnd ℂ) (Complex.exp (-(((σ : ℝ) : ℂ) * (x : ℝ))))
          = ((Real.exp (-(σ * x)) : ℝ) : ℂ) := by
        rw [← Complex.exp_conj]
        rw [show (starRingEnd ℂ) (-(((σ : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
            = (((-(σ * x) : ℝ)) : ℂ) by push_cast; simp [Complex.conj_ofReal]]
        rw [← Complex.ofReal_exp]
      rw [hre]
    · rw [Set.indicator_of_notMem hx, rayDamp, Set.indicator_of_notMem hx, map_zero, zero_mul]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi]

/-- **Equation (14c).**  The Báez--Duarte coefficient is the limit of the beta-smoothed
reciprocal-zeta line integrals as the damping is removed. -/
theorem tendsto_bdLineIntegral (k : ℕ) :
    Filter.Tendsto
      (fun σ : ℝ => ∫ ξ : ℝ,
        (starRingEnd ℂ) (centeredSchurLimit (rayLine σ ξ)) * 𝓕 (bdKernelVector k) ξ)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (bdCoeff (k + 1))) := by
  have hint := integrableOn_criticalMertens_bdKernel k
  have hbound : Integrable (fun t : ℝ => ‖mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ)‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hint.norm
  have hdom := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun (σ : ℝ) (t : ℝ) => mobiusWeightedPartial 1 t * ((Real.exp (-(σ * t)) : ℝ) : ℂ)
      * ((bdKernel k t : ℝ) : ℂ))
    (f := fun t : ℝ => mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
    (bound := fun t : ℝ => ‖mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ)‖)
    (l := nhdsWithin 0 (Set.Ioi (0 : ℝ))) ?_ ?_ hbound ?_
  · have heq : ∀ σ : ℝ, 0 < σ →
        (∫ ξ : ℝ, (starRingEnd ℂ) (centeredSchurLimit (rayLine σ ξ)) * 𝓕 (bdKernelVector k) ξ)
          = ∫ t in Set.Ioi (0 : ℝ), mobiusWeightedPartial 1 t * ((Real.exp (-(σ * t)) : ℝ) : ℂ)
              * ((bdKernel k t : ℝ) : ℂ) := by
      intro σ hσ
      rw [← inner_damped_bdKernel hσ k, inner_damped_bdKernel_time hσ k]
    have hcong : (fun σ : ℝ => ∫ ξ : ℝ,
        (starRingEnd ℂ) (centeredSchurLimit (rayLine σ ξ)) * 𝓕 (bdKernelVector k) ξ)
        =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
        fun σ : ℝ => ∫ t in Set.Ioi (0 : ℝ), mobiusWeightedPartial 1 t
          * ((Real.exp (-(σ * t)) : ℝ) : ℂ) * ((bdKernel k t : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact heq σ hσ
    rw [integral_criticalMertens_bdKernel k] at hdom
    exact hdom.congr' hcong.symm
  · filter_upwards with σ
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (memLp_criticalMertensVector.aestronglyMeasurable.restrict).congr
          (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
              rw [criticalMertensVector, Set.indicator_of_mem ht])
      · exact (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · exact (Complex.continuous_ofReal.comp (continuous_bdKernel k)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hσ0 : (0 : ℝ) < σ := hσ
    have hle : Real.exp (-(σ * t)) ≤ 1 := by
      have h : Real.exp (-(σ * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      rwa [Real.exp_zero] at h
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have hA := norm_nonneg (mobiusWeightedPartial 1 t)
    have hB := norm_nonneg (((bdKernel k t : ℝ) : ℂ))
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hA) hB]
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hcont : Filter.Tendsto (fun σ : ℝ => ((Real.exp (-(σ * t)) : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 1) := by
      have h1 : Filter.Tendsto (fun σ : ℝ => ((Real.exp (-(σ * t)) : ℝ) : ℂ))
          (nhds 0) (nhds ((Real.exp (-((0 : ℝ) * t)) : ℝ) : ℂ)) := by
        refine (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (by fun_prop))).continuousAt.tendsto
      simpa using h1.mono_left nhdsWithin_le_nhds
    have h2 := (hcont.const_mul (mobiusWeightedPartial 1 t)).mul_const
      (((bdKernel k t : ℝ) : ℂ))
    simpa using h2

end

end RHTower
