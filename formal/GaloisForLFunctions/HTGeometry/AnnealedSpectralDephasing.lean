import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleFourierDecay
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-!
# Annealed dephasing of an oscillatory family

A phase whose pushforward of the parameter measure is absolutely continuous dephases: the
oscillatory average of any bounded weight against it vanishes at large frequency, because the
average is the Fourier transform of an integrable density.  Absolute continuity is inherited by
every measure dominated by the parameter measure, so one absolute-continuity hypothesis on the
phase covers every bounded weight at once.

Applied entrywise to a family of finite matrices whose centered entries are finite sums of such
oscillatory averages, this upgrades to operator-norm convergence in finite dimension: the annealed
propagator converges to its averaged invariant part.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Riemann--Lebesgue for absolutely continuous phase pushforwards -/

/-- Riemann--Lebesgue for a finite absolutely continuous measure on the line. -/
theorem tendsto_integral_exp_measure_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hac : ν ≪ volume) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I) ∂ν)
      (cocompact ℝ) (𝓝 0) :=
  (spectralDensityFourierAmplitude_tendsto_zero_cocompact (spectralMeasureDensity ν)).congr
    fun t => spectralDensityFourierAmplitude_spectralMeasureDensity ν hac t

variable {Θ : Type*} [MeasurableSpace Θ]

/-- **Unweighted dephasing.**  A phase with absolutely continuous pushforward dephases the
parameter average. -/
theorem tendsto_integral_exp_phase_zero (μ : Measure Θ) [IsFiniteMeasure μ]
    {φ : Θ → ℝ} (hφ : Measurable φ) (hac : Measure.map φ μ ≪ volume) :
    Tendsto (fun t : ℝ => ∫ θ, Complex.exp (-((t * φ θ : ℝ) : ℂ) * Complex.I) ∂μ)
      (cocompact ℝ) (𝓝 0) := by
  haveI : IsFiniteMeasure (Measure.map φ μ) := by
    constructor
    rw [Measure.map_apply hφ MeasurableSet.univ]
    exact measure_lt_top μ _
  refine (tendsto_integral_exp_measure_zero (Measure.map φ μ) hac).congr fun t => ?_
  rw [integral_map hφ.aemeasurable]
  exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable

/-- **Dephasing against a bounded nonnegative weight.** -/
theorem tendsto_integral_exp_phase_nnreal_weight (μ : Measure Θ) [IsFiniteMeasure μ]
    {φ : Θ → ℝ} (hφ : Measurable φ) (hac : Measure.map φ μ ≪ volume)
    (f : Θ → NNReal) (hf : Measurable f) (C : NNReal) (hC : ∀ θ, f θ ≤ C) :
    Tendsto (fun t : ℝ =>
        ∫ θ, ((f θ : ℝ) : ℂ) * Complex.exp (-((t * φ θ : ℝ) : ℂ) * Complex.I) ∂μ)
      (cocompact ℝ) (𝓝 0) := by
  set ν : Measure Θ := μ.withDensity (fun θ => (f θ : ENNReal)) with hν
  haveI hfin : IsFiniteMeasure ν := by
    refine isFiniteMeasure_withDensity ?_
    have hmono : ∫⁻ θ, (f θ : ENNReal) ∂μ ≤ ∫⁻ _θ : Θ, (C : ENNReal) ∂μ :=
      lintegral_mono fun θ => ENNReal.coe_le_coe.mpr (hC θ)
    rw [lintegral_const] at hmono
    refine ne_of_lt (lt_of_le_of_lt hmono ?_)
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ _)
  have hacν : Measure.map φ ν ≪ volume :=
    ((withDensity_absolutelyContinuous μ _).map hφ).trans hac
  refine (tendsto_integral_exp_phase_zero ν hφ hacν).congr fun t => ?_
  rw [hν, integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp [NNReal.smul_def, Complex.real_smul]

/-! ## Bounded complex weights -/

theorem integrable_of_measurable_bounded (μ : Measure Θ) [IsFiniteMeasure μ]
    {F : Θ → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ θ, ‖F θ‖ ≤ B) : Integrable F μ :=
  (integrable_const B).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => by simpa using hB θ)

/-- **Dephasing against a bounded complex weight.**  This is the estimate that removes every
non-diagonal replica term of an annealed spectral average. -/
theorem tendsto_integral_exp_phase_weight (μ : Measure Θ) [IsFiniteMeasure μ]
    {φ : Θ → ℝ} (hφ : Measurable φ) (hac : Measure.map φ μ ≪ volume)
    (g : Θ → ℂ) (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ θ, g θ * Complex.exp (-((t * φ θ : ℝ) : ℂ) * Complex.I) ∂μ)
      (cocompact ℝ) (𝓝 0) := by
  classical
  set e : ℝ → Θ → ℂ := fun t θ => Complex.exp (-((t * φ θ : ℝ) : ℂ) * Complex.I) with he
  have hemeas : ∀ t, Measurable (e t) := by
    intro t
    exact Complex.measurable_exp.comp (by fun_prop)
  have henorm : ∀ t θ, ‖e t θ‖ = 1 := by
    intro t θ
    rw [he, Complex.norm_exp]
    have hre : (-((t * φ θ : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  -- the two shifted nonnegative weights
  set u : Θ → NNReal := fun θ => Real.toNNReal ((g θ).re + C) with hu
  set v : Θ → NNReal := fun θ => Real.toNNReal ((g θ).im + C) with hv
  have hreb : ∀ θ, |(g θ).re| ≤ C := fun θ => le_trans (Complex.abs_re_le_norm _) (hC θ)
  have himb : ∀ θ, |(g θ).im| ≤ C := fun θ => le_trans (Complex.abs_im_le_norm _) (hC θ)
  have hunn : ∀ θ, ((u θ : ℝ)) = (g θ).re + C := by
    intro θ
    rw [hu]
    refine Real.coe_toNNReal _ ?_
    have hb := abs_le.mp (hreb θ)
    linarith [hb.1]
  have hvnn : ∀ θ, ((v θ : ℝ)) = (g θ).im + C := by
    intro θ
    rw [hv]
    refine Real.coe_toNNReal _ ?_
    have hb := abs_le.mp (himb θ)
    linarith [hb.1]
  have humeas : Measurable u := by
    rw [hu]
    exact (Complex.measurable_re.comp hg).add measurable_const |>.real_toNNReal
  have hvmeas : Measurable v := by
    rw [hv]
    exact (Complex.measurable_im.comp hg).add measurable_const |>.real_toNNReal
  have hubdd : ∀ θ, u θ ≤ Real.toNNReal (2 * C) := by
    intro θ
    rw [← NNReal.coe_le_coe, hunn θ, Real.coe_toNNReal _ (by linarith)]
    have hb := abs_le.mp (hreb θ)
    linarith [hb.2]
  have hvbdd : ∀ θ, v θ ≤ Real.toNNReal (2 * C) := by
    intro θ
    rw [← NNReal.coe_le_coe, hvnn θ, Real.coe_toNNReal _ (by linarith)]
    have hb := abs_le.mp (himb θ)
    linarith [hb.2]
  -- decomposition of the weight
  have hdecomp : ∀ θ, g θ =
      (((u θ : ℝ) : ℂ) - (C : ℂ)) + Complex.I * (((v θ : ℝ) : ℂ) - (C : ℂ)) := by
    intro θ
    rw [hunn, hvnn]
    apply Complex.ext <;> simp
  -- integrabilities
  have hint : ∀ t, Integrable (fun θ => g θ * e t θ) μ := by
    intro t
    refine integrable_of_measurable_bounded μ (hg.mul (hemeas t)) (B := C) fun θ => ?_
    rw [norm_mul, henorm, mul_one]
    exact hC θ
  have hintU : ∀ t, Integrable (fun θ => ((u θ : ℝ) : ℂ) * e t θ) μ := by
    intro t
    refine integrable_of_measurable_bounded μ
      ((Complex.continuous_ofReal.measurable.comp
        (measurable_coe_nnreal_real.comp humeas)).mul (hemeas t))
      (B := 2 * C) fun θ => ?_
    rw [norm_mul, henorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (u θ).coe_nonneg, hunn]
    have hb := abs_le.mp (hreb θ)
    linarith [hb.2]
  have hintV : ∀ t, Integrable (fun θ => ((v θ : ℝ) : ℂ) * e t θ) μ := by
    intro t
    refine integrable_of_measurable_bounded μ
      ((Complex.continuous_ofReal.measurable.comp
        (measurable_coe_nnreal_real.comp hvmeas)).mul (hemeas t))
      (B := 2 * C) fun θ => ?_
    rw [norm_mul, henorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (v θ).coe_nonneg, hvnn]
    have hb := abs_le.mp (himb θ)
    linarith [hb.2]
  have hintE : ∀ t, Integrable (e t) μ := by
    intro t
    exact integrable_of_measurable_bounded μ (hemeas t) (B := 1) fun θ => le_of_eq (henorm t θ)
  -- split the integral
  have hsplit : ∀ t : ℝ, ∫ θ, g θ * e t θ ∂μ =
      (∫ θ, ((u θ : ℝ) : ℂ) * e t θ ∂μ - (C : ℂ) * ∫ θ, e t θ ∂μ) +
        Complex.I * (∫ θ, ((v θ : ℝ) : ℂ) * e t θ ∂μ - (C : ℂ) * ∫ θ, e t θ ∂μ) := by
    intro t
    have hpoint : ∀ θ, g θ * e t θ =
        (((u θ : ℝ) : ℂ) * e t θ - (C : ℂ) * e t θ) +
          Complex.I * (((v θ : ℝ) : ℂ) * e t θ - (C : ℂ) * e t θ) := by
      intro θ
      rw [hdecomp θ]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_add, integral_sub (hintU t) ((hintE t).const_mul _),
      integral_const_mul, integral_const_mul, integral_sub (hintV t) ((hintE t).const_mul _),
      integral_const_mul]
    · exact ((hintU t).sub ((hintE t).const_mul _))
    · exact (((hintV t).sub ((hintE t).const_mul _)).const_mul _)
  refine Tendsto.congr (fun t => (hsplit t).symm) ?_
  have hU := tendsto_integral_exp_phase_nnreal_weight μ hφ hac u humeas _ hubdd
  have hV := tendsto_integral_exp_phase_nnreal_weight μ hφ hac v hvmeas _ hvbdd
  have hE := tendsto_integral_exp_phase_zero μ hφ hac
  have hconst : Tendsto (fun _ : ℝ => (C : ℂ)) (cocompact ℝ) (𝓝 (C : ℂ)) := tendsto_const_nhds
  have hI : Tendsto (fun _ : ℝ => Complex.I) (cocompact ℝ) (𝓝 Complex.I) := tendsto_const_nhds
  have hstep := ((hU.sub (hconst.mul hE)).add (hI.mul (hV.sub (hconst.mul hE))))
  have hzero : ((0 : ℂ) - (C : ℂ) * 0) + Complex.I * ((0 : ℂ) - (C : ℂ) * 0) = 0 := by ring
  rw [hzero] at hstep
  exact hstep

/-! ## Operator-norm dephasing of an annealed matrix family -/

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- **Equation (19), abstract form.**  A finite matrix family whose entries are, at every time,
finite sums of bounded oscillatory averages against phases with absolutely continuous pushforward
converges to zero in operator norm.  Applied to the difference between the annealed propagator and
the averaged invariant projector, this is the annealed convergence of the replica propagator. -/
theorem tendsto_annealed_matrix_l2_opNorm_zero (μ : Measure Θ) [IsFiniteMeasure μ]
    {S : Type*} [Fintype S]
    (φ : S → Θ → ℝ) (hφ : ∀ s, Measurable (φ s))
    (hac : ∀ s, Measure.map (φ s) μ ≪ volume)
    (γ : S → w → w → Θ → ℂ) (hγ : ∀ s i j, Measurable (γ s i j))
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ s i j θ, ‖γ s i j θ‖ ≤ Cb)
    (M : ℝ → Matrix w w ℂ)
    (hM : ∀ t i j, M t i j =
      ∑ s, ∫ θ, γ s i j θ * Complex.exp (-((t * φ s θ : ℝ) : ℂ) * Complex.I) ∂μ) :
    Tendsto (fun t : ℝ => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := w)) (M t)‖)
      (cocompact ℝ) (𝓝 0) := by
  refine finiteMatrix_entrywise_tendsto_operatorNorm_zero M fun i j => ?_
  have hterm : ∀ s : S,
      Tendsto (fun t : ℝ => ∫ θ, γ s i j θ *
          Complex.exp (-((t * φ s θ : ℝ) : ℂ) * Complex.I) ∂μ) (cocompact ℝ) (𝓝 0) :=
    fun s => tendsto_integral_exp_phase_weight μ (hφ s) (hac s) (γ s i j) (hγ s i j) hCb0
      fun θ => hCb s i j θ
  have hsum : Tendsto (fun t : ℝ => ∑ s : S, ∫ θ, γ s i j θ *
      Complex.exp (-((t * φ s θ : ℝ) : ℂ) * Complex.I) ∂μ) (cocompact ℝ)
      (𝓝 (∑ _s : S, (0 : ℂ))) := tendsto_finsetSum _ fun s _ => hterm s
  rw [Finset.sum_const, smul_zero] at hsum
  exact hsum.congr fun t => (hM t i j).symm

end GaloisForLFunctions.HTGeometry
