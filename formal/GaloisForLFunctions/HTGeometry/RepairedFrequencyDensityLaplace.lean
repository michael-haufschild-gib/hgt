import GaloisForLFunctions.HTGeometry.RepairedFrequencyDxOverXLaw
import GaloisForLFunctions.HTGeometry.CompactDeterminacy
import GaloisForLFunctions.HTGeometry.IntegralCesaro

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Filter Topology

noncomputable section

/-- The repaired-frequency density tends to half the positive reservoir mass at zero. -/
theorem tendsto_factorialMomentDensity_nhdsGT_zero (nu : Measure ℝ) [IsFiniteMeasure nu] :
    Tendsto (factorialMomentDensity nu) (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 ((nu (Ioi 0)).toReal / 2)) := by
  have hDCT : Tendsto
      (fun x : ℝ => ∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (∫ _y, (1 : ℝ) ∂(nu.restrict (Ioi 0)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards with x
      exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with x
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y x)]
      exact sqrtExpDensity_le_one y x
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hcont : Continuous (fun x : ℝ => sqrtExpDensity y x) := by
        unfold sqrtExpDensity
        fun_prop
      have ht : Tendsto (fun x : ℝ => sqrtExpDensity y x)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (sqrtExpDensity y 0)) :=
        (hcont.tendsto 0).mono_left inf_le_left
      convert ht using 1
      simp [sqrtExpDensity]
  change Tendsto
    (fun x : ℝ => (∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0))) / 2)
    (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 ((nu (Ioi 0)).toReal / 2))
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    measureReal_def, Measure.restrict_apply_univ, mul_one] using hDCT.div_const 2

/-- Push the positive reservoir through inverse square root, the coordinate in which the
repaired-frequency density is a Laplace transform. -/
def inverseSqrtPushforward (nu : Measure ℝ) : Measure ℝ :=
  Measure.map (fun y : ℝ => (Real.sqrt y)⁻¹) (nu.restrict (Ioi 0))

/-- Exact Laplace-transform representation of the repaired-frequency density. -/
theorem factorialMomentDensity_laplace_inverseSqrtPushforward
    (nu : Measure ℝ) [IsFiniteMeasure nu] {t : ℝ} (ht : 0 < t) :
    2 * factorialMomentDensity nu (t ^ 2) =
      ∫ r, Real.exp (-t * r) ∂inverseSqrtPushforward nu := by
  have hmap : Measurable (fun y : ℝ => (Real.sqrt y)⁻¹) := by fun_prop
  have hF : AEStronglyMeasurable (fun r : ℝ => Real.exp (-t * r))
      (inverseSqrtPushforward nu) := by fun_prop
  rw [inverseSqrtPushforward, integral_map hmap.aemeasurable hF]
  rw [factorialMomentDensity]
  have heq : (fun y : ℝ => Real.exp (-t * (Real.sqrt y)⁻¹))
      =ᵐ[nu.restrict (Ioi 0)] fun y => sqrtExpDensity y (t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [sqrtExpDensity, Real.sqrt_div (sq_nonneg t), Real.sqrt_sq ht.le]
    congr 1
    field_simp
  rw [integral_congr_ae heq]
  ring

/-- Exponential compactification of a nonnegative Laplace coordinate. -/
def laplaceCompactification (r : ℝ) : ℝ := Real.exp (-r)

theorem continuous_laplaceCompactification : Continuous laplaceCompactification := by
  unfold laplaceCompactification
  fun_prop

theorem injective_laplaceCompactification : Function.Injective laplaceCompactification := by
  intro x y h
  apply neg_injective
  exact Real.exp_injective h

theorem measurableEmbedding_laplaceCompactification :
    MeasurableEmbedding laplaceCompactification :=
  continuous_laplaceCompactification.measurableEmbedding injective_laplaceCompactification

/-- A finite measure carried by the nonnegative half-line has Laplace transform converging to its
total mass as the parameter tends to zero from the right. -/
theorem tendsto_laplaceIntegral_nhdsGT_zero (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici 0)ᶜ = 0) :
    Tendsto (fun t : ℝ => ∫ r, Real.exp (-t * r) ∂tau)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (tau Set.univ).toReal) := by
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  have hDCT : Tendsto (fun t : ℝ => ∫ r, Real.exp (-t * r) ∂tau)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (∫ _r, (1 : ℝ) ∂tau)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards with t
      fun_prop
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hae] with r hr
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg ht.le hr)
    · filter_upwards with r
      have hcont : Continuous (fun t : ℝ => Real.exp (-t * r)) := by fun_prop
      change Tendsto (fun t : ℝ => Real.exp (-t * r))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (1 : ℝ))
      have htend : Tendsto (fun t : ℝ => Real.exp (-t * r))
          (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (Real.exp (-(0 : ℝ) * r))) :=
        hcont.continuousAt.continuousWithinAt
      simpa only [neg_zero, zero_mul, Real.exp_zero] using htend
  simpa [integral_const, measureReal_def] using hDCT

/-- Push a nonnegative Laplace coordinate into the compact interval `[0,1]`. -/
def compactifiedLaplaceMeasure (tau : Measure ℝ) : Measure ℝ :=
  Measure.map laplaceCompactification tau

instance compactifiedLaplaceMeasure_isFinite (tau : Measure ℝ) [IsFiniteMeasure tau] :
    IsFiniteMeasure (compactifiedLaplaceMeasure tau) :=
  Measure.isFiniteMeasure_map tau laplaceCompactification

theorem compactifiedLaplaceMeasure_carried_Icc (tau : Measure ℝ)
    (htau : tau (Ici 0)ᶜ = 0) :
    compactifiedLaplaceMeasure tau (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [compactifiedLaplaceMeasure, Measure.map_apply
    continuous_laplaceCompactification.measurable measurableSet_Icc.compl]
  apply measure_mono_null _ htau
  intro r hr
  simp only [mem_preimage, mem_compl_iff] at hr ⊢
  intro hr0
  apply hr
  constructor
  · exact Real.exp_nonneg _
  · rw [laplaceCompactification, Real.exp_le_one_iff]
    exact neg_nonpos.mpr hr0

theorem compactifiedLaplaceMeasure_moment (tau : Measure ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂compactifiedLaplaceMeasure tau =
      ∫ r, Real.exp (-(k : ℝ) * r) ∂tau := by
  rw [compactifiedLaplaceMeasure, integral_map
    continuous_laplaceCompactification.measurable.aemeasurable]
  · apply integral_congr_ae
    filter_upwards with r
    simp [laplaceCompactification, ← Real.exp_nat_mul]
  · fun_prop

/-- Uniqueness of the Laplace transform for finite measures on the nonnegative half-line, derived
from the corpus's compact moment determinacy theorem after exponential compactification. -/
theorem measure_eq_of_laplace_eq {tau sigma : Measure ℝ}
    [IsFiniteMeasure tau] [IsFiniteMeasure sigma]
    (htau : tau (Ici 0)ᶜ = 0) (hsigma : sigma (Ici 0)ᶜ = 0)
    (hLaplace : ∀ t : ℝ, 0 < t →
      ∫ r, Real.exp (-t * r) ∂tau = ∫ r, Real.exp (-t * r) ∂sigma) :
    tau = sigma := by
  have hmass : (tau Set.univ).toReal = (sigma Set.univ).toReal := by
    apply tendsto_nhds_unique (tendsto_laplaceIntegral_nhdsGT_zero tau htau)
    exact (tendsto_laplaceIntegral_nhdsGT_zero sigma hsigma).congr'
      (by filter_upwards [self_mem_nhdsWithin] with t ht; exact (hLaplace t ht).symm)
  have hcompact : compactifiedLaplaceMeasure tau = compactifiedLaplaceMeasure sigma := by
    let s : ℕ → ℝ := fun k => ∫ x, x ^ k ∂compactifiedLaplaceMeasure tau
    apply _root_.HTGeometry.measure_eq_of_moments_eq_of_carried (s := s)
        (compactifiedLaplaceMeasure_carried_Icc tau htau)
        (compactifiedLaplaceMeasure_carried_Icc sigma hsigma)
    · intro k
      rfl
    · intro k
      apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      filter_upwards [ae_iff.mpr (compactifiedLaplaceMeasure_carried_Icc tau htau)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 k)]
      exact pow_le_one₀ hx.1 hx.2
    · intro k
      unfold s
      rw [compactifiedLaplaceMeasure_moment, compactifiedLaplaceMeasure_moment]
      cases k with
      | zero => simpa [integral_const, measureReal_def] using hmass
      | succ k => simpa [Nat.cast_succ] using hLaplace (k + 1) (by positivity)
    · intro k
      apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      filter_upwards [ae_iff.mpr (compactifiedLaplaceMeasure_carried_Icc sigma hsigma)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 k)]
      exact pow_le_one₀ hx.1 hx.2
  exact measurableEmbedding_laplaceCompactification.map_injective hcompact

theorem inverseSqrtPushforward_carried_Ici (nu : Measure ℝ) :
    inverseSqrtPushforward nu (Ici (0 : ℝ))ᶜ = 0 := by
  rw [inverseSqrtPushforward, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  rw [Measure.restrict_apply (measurableSet_Ici.compl.preimage (by fun_prop))]
  apply measure_mono_null _ (measure_empty)
  rintro y ⟨hy, _⟩
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hy
  exact (not_lt_of_ge (inv_nonneg.mpr (Real.sqrt_nonneg y)) hy).elim

/-- Inverse coordinate to `y ↦ y⁻¹ᐟ²` on the positive half-line. -/
def inverseSquareReconstruction (r : ℝ) : ℝ := r⁻¹ ^ 2

theorem measurable_inverseSquareReconstruction : Measurable inverseSquareReconstruction := by
  unfold inverseSquareReconstruction
  fun_prop

theorem map_inverseSquareReconstruction_inverseSqrtPushforward (nu : Measure ℝ) :
    Measure.map inverseSquareReconstruction (inverseSqrtPushforward nu) =
      nu.restrict (Ioi 0) := by
  rw [inverseSqrtPushforward,
    Measure.map_map measurable_inverseSquareReconstruction (by fun_prop)]
  calc
    Measure.map (inverseSquareReconstruction ∘ fun y : ℝ => (Real.sqrt y)⁻¹)
        (nu.restrict (Ioi 0)) = Measure.map id (nu.restrict (Ioi 0)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simp [inverseSquareReconstruction, Real.sq_sqrt hy.le]
    _ = nu.restrict (Ioi 0) := Measure.map_id

/-- The full positive repaired-frequency density determines the positive reservoir measure. -/
theorem restrict_Ioi_eq_of_factorialMomentDensity_eq {nu sigma : Measure ℝ}
    [IsFiniteMeasure nu] [IsFiniteMeasure sigma]
    (hDensity : ∀ x : ℝ, 0 < x →
      factorialMomentDensity nu x = factorialMomentDensity sigma x) :
    nu.restrict (Ioi 0) = sigma.restrict (Ioi 0) := by
  letI : IsFiniteMeasure (inverseSqrtPushforward nu) :=
    Measure.isFiniteMeasure_map (nu.restrict (Ioi 0)) (fun y : ℝ => (Real.sqrt y)⁻¹)
  letI : IsFiniteMeasure (inverseSqrtPushforward sigma) :=
    Measure.isFiniteMeasure_map (sigma.restrict (Ioi 0)) (fun y : ℝ => (Real.sqrt y)⁻¹)
  have hpush : inverseSqrtPushforward nu = inverseSqrtPushforward sigma := by
    apply measure_eq_of_laplace_eq (inverseSqrtPushforward_carried_Ici nu)
      (inverseSqrtPushforward_carried_Ici sigma)
    intro t ht
    rw [← factorialMomentDensity_laplace_inverseSqrtPushforward nu ht,
      ← factorialMomentDensity_laplace_inverseSqrtPushforward sigma ht,
      hDensity (t ^ 2) (sq_pos_of_pos ht)]
  rw [← map_inverseSquareReconstruction_inverseSqrtPushforward nu,
    ← map_inverseSquareReconstruction_inverseSqrtPushforward sigma, hpush]

/-- The factorial-moment reservoir density is continuous on the real line. -/
theorem continuous_factorialMomentDensity (nu : Measure ℝ) [IsFiniteMeasure nu] :
    Continuous (factorialMomentDensity nu) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hDCT : Tendsto
      (fun z : ℝ => ∫ y, sqrtExpDensity y z ∂(nu.restrict (Ioi 0)))
      (𝓝 x) (𝓝 (∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards with z
      exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with z
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y z)]
      exact sqrtExpDensity_le_one y z
    · filter_upwards with y
      exact (show ContinuousAt (fun z : ℝ => sqrtExpDensity y z) x by
        unfold sqrtExpDensity
        fun_prop)
  change Tendsto
    (fun z : ℝ => (∫ y, sqrtExpDensity y z ∂(nu.restrict (Ioi 0))) / 2)
    (𝓝 x) (𝓝 ((∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0))) / 2))
  exact hDCT.div_const 2

/-- Logarithmic substitution for the repaired-frequency density. -/
theorem intervalIntegral_factorialMomentDensity_mul_inv
    (nu : Measure ℝ) [IsFiniteMeasure nu] {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, factorialMomentDensity nu x * x⁻¹) =
      ∫ u in Real.log a..Real.log b, factorialMomentDensity nu (Real.exp u) := by
  let g : ℝ → ℝ := fun x => factorialMomentDensity nu x * x⁻¹
  have hg : ContinuousOn g
      (Real.exp '' uIcc (Real.log a) (Real.log b)) := by
    intro x hx
    rcases hx with ⟨u, _hu, rfl⟩
    exact (continuous_factorialMomentDensity nu).continuousAt.mul
      (continuousAt_id.inv₀ (Real.exp_ne_zero u)) |>.continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log a) (b := Real.log b) (f := Real.exp) (f' := Real.exp) (g := g)
    (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hg
  rw [Real.exp_log ha, Real.exp_log hb] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro u _
  simp [g, Function.comp_apply, Real.exp_ne_zero]

/-- On every interval away from zero, repaired-frequency mass is the ordinary integral of
`factorialMomentDensity nu / x`. -/
theorem repairedFrequencyMeasure_Ioo_toReal_eq_intervalIntegral
    (nu : Measure ℝ) [IsFiniteMeasure nu] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (repairedFrequencyMeasure nu (Ioo a b)).toReal =
      ∫ x in a..b, factorialMomentDensity nu x * x⁻¹ := by
  have hcont : ContinuousOn (fun x : ℝ => factorialMomentDensity nu x * x⁻¹)
      (Icc a b) := by
    intro x hx
    exact (continuous_factorialMomentDensity nu).continuousAt.mul
      (continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha hx.1))) |>.continuousWithinAt
  have hint : IntegrableOn (fun x : ℝ => factorialMomentDensity nu x * x⁻¹)
      (Ioo a b) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)]
      fun x : ℝ => factorialMomentDensity nu x * x⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (factorialMomentDensity_nonneg nu x)
      (inv_nonneg.mpr (le_trans ha.le hx.1.le))
  have hofReal := ofReal_integral_eq_lintegral_ofReal hint hnonneg
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab] at hofReal
  have hmeasure : repairedFrequencyMeasure nu (Ioo a b) =
      ENNReal.ofReal (∫ x in a..b, factorialMomentDensity nu x * x⁻¹) := by
    rw [repairedFrequencyMeasure, withDensity_apply _ measurableSet_Ioo,
      positiveMultiplicativeHaar,
      setLIntegral_withDensity_eq_setLIntegral_mul (volume.restrict (Ioi 0))
        (by fun_prop) (measurable_factorialMomentDensity nu).ennreal_ofReal measurableSet_Ioo]
    change (∫⁻ x, ENNReal.ofReal x⁻¹ * ENNReal.ofReal (factorialMomentDensity nu x)
        ∂((volume.restrict (Ioi 0)).restrict (Ioo a b))) = _
    rw [Measure.restrict_restrict_of_subset (show Ioo a b ⊆ Ioi 0 by
      intro x hx; exact lt_of_lt_of_le ha hx.1.le)]
    calc
      (∫⁻ x in Ioo a b, ENNReal.ofReal x⁻¹ *
          ENNReal.ofReal (factorialMomentDensity nu x) ∂volume) =
          ∫⁻ x in Ioo a b,
            ENNReal.ofReal (factorialMomentDensity nu x * x⁻¹) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards with x
        rw [ENNReal.ofReal_mul (factorialMomentDensity_nonneg nu x), mul_comm]
      _ = _ := hofReal.symm
  rw [hmeasure, ENNReal.toReal_ofReal]
  exact intervalIntegral.integral_nonneg hab fun x hx =>
    mul_nonneg (factorialMomentDensity_nonneg nu x)
      (inv_nonneg.mpr (le_trans ha.le hx.1))

/-- Exact logarithmic divergence rate of the repaired-frequency measure. -/
theorem tendsto_repairedFrequencyMeasure_log_ratio
    (nu : Measure ℝ) [IsFiniteMeasure nu] {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun epsilon : ℝ =>
      (repairedFrequencyMeasure nu (Ioo epsilon delta)).toReal /
        Real.log (delta / epsilon))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 ((nu (Ioi 0)).toReal / 2)) := by
  let f : ℝ → ℝ := fun u => factorialMomentDensity nu (Real.exp (-u))
  have hfcont : Continuous f := by
    exact (continuous_factorialMomentDensity nu).comp
      (Real.continuous_exp.comp continuous_neg)
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    · filter_upwards with u
      exact Real.exp_pos _
  have hf : Tendsto f atTop (𝓝 ((nu (Ioi 0)).toReal / 2)) :=
    (tendsto_factorialMomentDensity_nhdsGT_zero nu).comp hexp
  have havg := _root_.HTGeometry.tendsto_intervalAverage_atTop_of_tendsto
    hfcont hf (-Real.log delta)
  have hneglog : Tendsto (fun epsilon : ℝ => -Real.log epsilon)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hcomp := havg.comp hneglog
  apply hcomp.congr'
  have hlt : ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Ioi 0), epsilon < delta :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hdelta)
  filter_upwards [self_mem_nhdsWithin, hlt] with epsilon hepsilon hepsdelta
  rw [repairedFrequencyMeasure_Ioo_toReal_eq_intervalIntegral nu hepsilon hepsdelta.le,
    intervalIntegral_factorialMomentDensity_mul_inv nu hepsilon hdelta,
    Real.log_div hdelta.ne' hepsilon.ne']
  have hneg : (∫ u in Real.log epsilon..Real.log delta,
      factorialMomentDensity nu (Real.exp u)) =
      ∫ u in -Real.log delta..-Real.log epsilon,
        factorialMomentDensity nu (Real.exp (-u)) := by
    symm
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := fun u : ℝ => factorialMomentDensity nu (Real.exp u))
        (a := -Real.log delta) (b := -Real.log epsilon))
  rw [hneg]
  change (∫ u in -Real.log delta..-Real.log epsilon, f u) /
      (-Real.log epsilon - -Real.log delta) = _
  simp only [f]
  congr 1
  ring

/-- Exact logarithmic divergence rate for every source with the card's shifted-factorial moments. -/
theorem tendsto_sourceMeasure_log_ratio_of_shiftedFactorialMoments
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta)
    (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    Tendsto (fun epsilon : ℝ =>
      (mu (Ioo epsilon delta)).toReal / Real.log (delta / epsilon))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 ((nu (Ioi 0)).toReal / 2)) := by
  have hcanonical := tendsto_repairedFrequencyMeasure_log_ratio nu hdelta
  apply hcanonical.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hset : Ioo epsilon delta ⊆ Ioi (0 : ℝ) := fun x hx =>
    lt_of_lt_of_le hepsilon hx.1.le
  have heq := setLIntegral_source_eq_repairedFrequencyMeasure hR hsupp hmu hmomInt hmom
    hset (fun _ => (1 : ENNReal))
  simpa only [setLIntegral_one] using congrArg
    (fun z : ENNReal => z.toReal / Real.log (delta / epsilon)) heq.symm

end
end GaloisForLFunctions.HTGeometry
