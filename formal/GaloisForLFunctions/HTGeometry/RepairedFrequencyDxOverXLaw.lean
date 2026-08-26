import GaloisForLFunctions.HTGeometry.RepairedFrequencyLocalDivergence

/-!
# The repaired-frequency `dx/x` law

The shifted factorial moment problem has already been solved and proved determinate in
`RepairedFrequencyLocalDivergence`.  This file cancels its strictly positive `x`-weight on the
open half-line.  The resulting source is exactly the explicit factorial-moment density measured
against multiplicative Haar measure `dx/x`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- Multiplicative Haar measure `dx/x` on the positive real half-line. -/
def positiveMultiplicativeHaar : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal x⁻¹

/-- The forced repaired-frequency measure attached to a compact positive target. -/
def repairedFrequencyMeasure (nu : Measure ℝ) : Measure ℝ :=
  positiveMultiplicativeHaar.withDensity fun x => ENNReal.ofReal (factorialMomentDensity nu x)

/-- Dividing the shifted factorial representing measure by its positive coordinate produces the
explicit repaired-frequency measure. -/
theorem factorialMomentMeasure_withDensity_inv_eq_repairedFrequencyMeasure
    (nu : Measure ℝ) [IsFiniteMeasure nu] :
    (factorialMomentMeasure nu).withDensity (fun x => (ENNReal.ofReal x)⁻¹) =
      repairedFrequencyMeasure nu := by
  let base : Measure ℝ := volume.restrict (Ioi 0)
  let d : ℝ → ENNReal := fun x => ENNReal.ofReal (factorialMomentDensity nu x)
  let invx : ℝ → ENNReal := fun x => (ENNReal.ofReal x)⁻¹
  let rinv : ℝ → ENNReal := fun x => ENNReal.ofReal x⁻¹
  have hd : Measurable d := (measurable_factorialMomentDensity nu).ennreal_ofReal
  have hi : Measurable invx := measurable_id.ennreal_ofReal.inv
  have hr : Measurable rinv := measurable_id.inv.ennreal_ofReal
  have hprod : d * invx =ᵐ[base] rinv * d := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    dsimp only [invx, rinv]
    rw [Pi.mul_apply, Pi.mul_apply, ENNReal.ofReal_inv_of_pos hx0]
    exact mul_comm _ _
  change (base.withDensity d).withDensity invx = (base.withDensity rinv).withDensity d
  calc
    (base.withDensity d).withDensity invx = base.withDensity (d * invx) :=
      (withDensity_mul base hd hi).symm
    _ = base.withDensity (rinv * d) := withDensity_congr_ae hprod
    _ = (base.withDensity rinv).withDensity d := withDensity_mul base hr hd

/-- **Exact density law.**  Every positive source with the card's shifted-factorial moments agrees
on `(0,∞)` with `factorialMomentDensity nu · dx/x`. -/
theorem restrict_Ioi_eq_repairedFrequencyMeasure_of_shiftedFactorialMoments
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    mu.restrict (Ioi 0) = repairedFrequencyMeasure nu := by
  have heq := shiftedMeasure_eq_factorialMomentMeasure hR hsupp hmu hmomInt hmom
  have heqI := congrArg (fun m : Measure ℝ => m.restrict (Ioi 0)) heq
  have hfactmem : ∀ᵐ x ∂(factorialMomentMeasure nu), x ∈ Ioi (0 : ℝ) := by
    rw [factorialMomentMeasure]
    exact (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Ioi)
  rw [Measure.restrict_eq_self_of_ae_mem hfactmem,
    restrict_withDensity measurableSet_Ioi] at heqI
  have hinv := congrArg
    (fun m : Measure ℝ => m.withDensity fun x => (ENNReal.ofReal x)⁻¹) heqI
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal x) := ENNReal.measurable_ofReal
  have hne0 : ∀ᵐ x ∂(mu.restrict (Ioi 0)), ENNReal.ofReal x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hx
  have hnetop : ∀ᵐ x ∂(mu.restrict (Ioi 0)), ENNReal.ofReal x ≠ ⊤ := by
    filter_upwards with x using ENNReal.ofReal_ne_top
  rw [factorialMomentMeasure_withDensity_inv_eq_repairedFrequencyMeasure nu,
    withDensity_inv_same hmeas hne0 hnetop] at hinv
  exact hinv.symm

/-- The reservoir density never exceeds half of the target's positive mass. -/
theorem factorialMomentDensity_le_positiveMass (nu : Measure ℝ) [IsFiniteMeasure nu] (x : ℝ) :
    factorialMomentDensity nu x ≤ (nu (Ioi 0)).toReal / 2 := by
  have hint : Integrable (fun y => sqrtExpDensity y x) (nu.restrict (Ioi 0)) := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y x)]
      exact sqrtExpDensity_le_one y x
  have hmono : (∫ y, sqrtExpDensity y x ∂(nu.restrict (Ioi 0)))
      ≤ ∫ _y, (1 : ℝ) ∂(nu.restrict (Ioi 0)) :=
    integral_mono hint (integrable_const 1) (fun y => sqrtExpDensity_le_one y x)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
    measureReal_def] at hmono
  rw [factorialMomentDensity]
  exact div_le_div_of_nonneg_right hmono (by norm_num)

/-- On `(0,δ)`, target mass above `η` gives the exact uniform lower density used in the card. -/
theorem factorialMomentDensity_lower_on_Ioo {nu : Measure ℝ} [IsFiniteMeasure nu]
    {eta delta x : ℝ} (heta : 0 < eta) (hx : x ∈ Ioo 0 delta) :
    Real.exp (-Real.sqrt (delta / eta)) * (nu (Ici eta)).toReal / 2
      ≤ factorialMomentDensity nu x := by
  have hint : Integrable (fun y => sqrtExpDensity y x) (nu.restrict (Ioi 0)) := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y x)]
      exact sqrtExpDensity_le_one y x
  have hsub : Ici eta ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le heta hy
  have hmono : (∫ y in Ici eta, sqrtExpDensity y x ∂nu)
      ≤ ∫ y in Ioi (0 : ℝ), sqrtExpDensity y x ∂nu := by
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub)
    filter_upwards with y using sqrtExpDensity_nonneg y x
  have hpt : ∀ y ∈ Ici eta,
      Real.exp (-Real.sqrt (delta / eta)) ≤ sqrtExpDensity y x := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le heta hy
    rw [sqrtExpDensity]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hy0 heta]
    calc
      x * eta ≤ delta * eta := mul_le_mul_of_nonneg_right hx.2.le heta.le
      _ ≤ delta * y := mul_le_mul_of_nonneg_left hy (le_trans hx.1.le hx.2.le)
  have hconst : (∫ _y in Ici eta, Real.exp (-Real.sqrt (delta / eta)) ∂nu)
      ≤ ∫ y in Ici eta, sqrtExpDensity y x ∂nu := by
    refine setIntegral_mono_on (integrable_const _).integrableOn ?_ measurableSet_Ici hpt
    exact hint.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hconst
  rw [factorialMomentDensity]
  exact div_le_div_of_nonneg_right (le_trans hconst hmono) (by norm_num)

theorem measure_Ioi_eq_measure_Ioc_of_ae_mem_Icc {nu : Measure ℝ} {R : ℝ}
    (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) :
    nu (Ioi 0) = nu (Ioc 0 R) := by
  refine measure_congr ?_
  filter_upwards [hsupp] with y hy
  change (0 < y) = (0 < y ∧ y ≤ R)
  apply propext
  constructor
  · intro hy0
    exact ⟨hy0, hy.2⟩
  · exact fun hy' => hy'.1

theorem measure_Ici_eq_measure_Icc_of_ae_mem_Icc {nu : Measure ℝ} {R eta : ℝ}
    (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R) :
    nu (Ici eta) = nu (Icc eta R) := by
  refine measure_congr ?_
  filter_upwards [hsupp] with y hy
  change (eta ≤ y) = (eta ≤ y ∧ y ≤ R)
  apply propext
  constructor
  · intro hyeta
    exact ⟨hyeta, hy.2⟩
  · exact fun hy' => hy'.1

/-- **Quantitative `dx/x` law.**  Every nonnegative Borel weight is trapped between the exact
card constants times its multiplicative-Haar integral.  The statement is in `ℝ≥0∞`, so it also
records the infinite cases without an integrability premise. -/
theorem repairedFrequency_weighted_lintegral_bounds
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R eta delta : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (heta : 0 < eta) (_hdelta : 0 < delta)
    {w : ℝ → ENNReal} (hw : Measurable w) :
    ENNReal.ofReal
        (Real.exp (-Real.sqrt (delta / eta)) * (nu (Icc eta R)).toReal / 2) *
          (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar)
      ≤ ∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu ∧
    (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu)
      ≤ ENNReal.ofReal ((nu (Ioc 0 R)).toReal / 2) *
          (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) := by
  have hlowerReal : ∀ x ∈ Ioo (0 : ℝ) delta,
      Real.exp (-Real.sqrt (delta / eta)) * (nu (Icc eta R)).toReal / 2
        ≤ factorialMomentDensity nu x := by
    intro x hx
    rw [← measure_Ici_eq_measure_Icc_of_ae_mem_Icc hsupp]
    exact factorialMomentDensity_lower_on_Ioo heta hx
  have hupperReal : ∀ x : ℝ,
      factorialMomentDensity nu x ≤ (nu (Ioc 0 R)).toReal / 2 := by
    intro x
    rw [← measure_Ioi_eq_measure_Ioc_of_ae_mem_Icc hsupp]
    exact factorialMomentDensity_le_positiveMass nu x
  rw [repairedFrequencyMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul positiveMultiplicativeHaar
      (measurable_factorialMomentDensity nu).ennreal_ofReal hw measurableSet_Ioo]
  constructor
  · rw [← lintegral_const_mul _ hw]
    refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hlowerReal x hx)) (w x)
  · rw [← lintegral_const_mul _ hw]
    refine setLIntegral_mono' measurableSet_Ioo fun x _hx => ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hupperReal x)) (w x)

end

end GaloisForLFunctions.HTGeometry
