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

/-- Finiteness against the forced reservoir is exactly finiteness against `dx/x`. -/
theorem repairedFrequency_weighted_lintegral_ne_top_iff
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R eta delta : ℝ} (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (heta : 0 < eta) (hdelta : 0 < delta) (hnu : nu (Icc eta R) ≠ 0)
    {w : ℝ → ENNReal} (hw : Measurable w) :
    (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu) ≠ ⊤ ↔
      (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) ≠ ⊤ := by
  let A := ∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar
  let B := ∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu
  let c := ENNReal.ofReal
    (Real.exp (-Real.sqrt (delta / eta)) * (nu (Icc eta R)).toReal / 2)
  let d := ENNReal.ofReal ((nu (Ioc 0 R)).toReal / 2)
  have hbounds := repairedFrequency_weighted_lintegral_bounds hsupp heta hdelta hw
  change c * A ≤ B ∧ B ≤ d * A at hbounds
  have hmass : 0 < (nu (Icc eta R)).toReal :=
    ENNReal.toReal_pos hnu (measure_ne_top nu _)
  have hcReal : 0 < Real.exp (-Real.sqrt (delta / eta)) *
      (nu (Icc eta R)).toReal / 2 := by positivity
  have hc0 : c ≠ 0 := by
    change ENNReal.ofReal (Real.exp (-Real.sqrt (delta / eta)) *
      (nu (Icc eta R)).toReal / 2) ≠ 0
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hcReal
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro hB hA
    have htop : c * A = ⊤ := (ENNReal.mul_eq_top).2 (Or.inl ⟨hc0, hA⟩)
    exact hB (top_unique (htop ▸ hbounds.1))
  · rintro hA hBtop
    apply ENNReal.mul_ne_top hdtop hA
    exact top_unique (hBtop ▸ hbounds.2)

/-- The exact density law transported from the canonical reservoir back to any source satisfying
the card's moment conditions. -/
theorem setLIntegral_source_eq_repairedFrequencyMeasure
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu)
    {s : Set ℝ} (hs : s ⊆ Ioi 0) (w : ℝ → ENNReal) :
    (∫⁻ x in s, w x ∂mu) = ∫⁻ x in s, w x ∂repairedFrequencyMeasure nu := by
  have heq := restrict_Ioi_eq_repairedFrequencyMeasure_of_shiftedFactorialMoments
    hR hsupp hmu hmomInt hmom
  have hres := congrArg (fun m : Measure ℝ => m.restrict s) heq
  rw [Measure.restrict_restrict_of_subset hs] at hres
  exact congrArg (fun m : Measure ℝ => ∫⁻ x, w x ∂m) hres

theorem exists_pos_measure_Ici_of_measure_Ioi_ne_zero {nu : Measure ℝ}
    (hpos : nu (Ioi 0) ≠ 0) :
    ∃ eta : ℝ, 0 < eta ∧ nu (Ici eta) ≠ 0 := by
  have hUnion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ici (1 / (n + 1 : ℝ)) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn.le⟩
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)) hn
  by_contra h
  push Not at h
  have hn : ∀ n : ℕ, nu (Ici (1 / (n + 1 : ℝ))) = 0 := by
    intro n
    exact h _ (by positivity)
  apply hpos
  rw [hUnion]
  exact measure_iUnion_null hn

/-- Quantitative card bounds for every source satisfying the shifted-factorial moments. -/
theorem source_weighted_lintegral_bounds
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R eta delta : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (heta : 0 < eta) (hdelta : 0 < delta)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu)
    {w : ℝ → ENNReal} (hw : Measurable w) :
    ENNReal.ofReal
        (Real.exp (-Real.sqrt (delta / eta)) * (nu (Icc eta R)).toReal / 2) *
          (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar)
      ≤ ∫⁻ x in Ioo 0 delta, w x ∂mu ∧
    (∫⁻ x in Ioo 0 delta, w x ∂mu)
      ≤ ENNReal.ofReal ((nu (Ioc 0 R)).toReal / 2) *
          (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) := by
  have heq := setLIntegral_source_eq_repairedFrequencyMeasure hR hsupp hmu hmomInt hmom
    (s := Ioo 0 delta) (fun _ hx => hx.1) w
  rw [heq]
  exact repairedFrequency_weighted_lintegral_bounds hsupp heta hdelta hw

/-- **Zero-frequency repaired-source `dx/x` law.**  For a compact target with positive mass away
from zero, local weighted integrability is equivalent to `dx/x` integrability for every
nonnegative Borel weight. -/
theorem source_weighted_lintegral_ne_top_iff
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (hpos : nu (Ioi 0) ≠ 0) (hdelta : 0 < delta)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu)
    {w : ℝ → ENNReal} (hw : Measurable w) :
    (∫⁻ x in Ioo 0 delta, w x ∂mu) ≠ ⊤ ↔
      (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) ≠ ⊤ := by
  obtain ⟨eta, heta, hmass⟩ := exists_pos_measure_Ici_of_measure_Ioi_ne_zero hpos
  have hmass' : nu (Icc eta R) ≠ 0 := by
    rw [← measure_Ici_eq_measure_Icc_of_ae_mem_Icc hsupp]
    exact hmass
  rw [setLIntegral_source_eq_repairedFrequencyMeasure hR hsupp hmu hmomInt hmom
    (s := Ioo 0 delta) (fun _ hx => hx.1) w]
  exact repairedFrequency_weighted_lintegral_ne_top_iff hsupp heta hdelta hmass' hw

/-- Any two nontrivial compact-target repaired-frequency measures are boundedly equivalent on a
fixed punctured neighborhood of zero. Constants are finite positive `ℝ≥0∞` scalars because
measures themselves take values in `ℝ≥0∞`. -/
theorem exists_repairedFrequencyMeasure_local_bounded_equivalence
    {nu₁ nu₂ : Measure ℝ} [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    {R₁ R₂ delta : ℝ} (hdelta : 0 < delta)
    (hsupp₁ : ∀ᵐ y ∂nu₁, y ∈ Icc 0 R₁) (hsupp₂ : ∀ᵐ y ∂nu₂, y ∈ Icc 0 R₂)
    (hpos₁ : nu₁ (Ioi 0) ≠ 0) (hpos₂ : nu₂ (Ioi 0) ≠ 0) :
    ∃ c C : ENNReal, 0 < c ∧ c ≤ C ∧ C < ⊤ ∧
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo 0 delta →
        c * repairedFrequencyMeasure nu₂ E ≤ repairedFrequencyMeasure nu₁ E ∧
        repairedFrequencyMeasure nu₁ E ≤ C * repairedFrequencyMeasure nu₂ E := by
  obtain ⟨eta₁, heta₁, hetaMass₁⟩ := exists_pos_measure_Ici_of_measure_Ioi_ne_zero hpos₁
  obtain ⟨eta₂, heta₂, hetaMass₂⟩ := exists_pos_measure_Ici_of_measure_Ioi_ne_zero hpos₂
  have hetaIcc₁ : nu₁ (Icc eta₁ R₁) ≠ 0 := by
    rwa [← measure_Ici_eq_measure_Icc_of_ae_mem_Icc hsupp₁]
  have hetaIcc₂ : nu₂ (Icc eta₂ R₂) ≠ 0 := by
    rwa [← measure_Ici_eq_measure_Icc_of_ae_mem_Icc hsupp₂]
  let A₁ : ENNReal := ENNReal.ofReal
    (Real.exp (-Real.sqrt (delta / eta₁)) * (nu₁ (Icc eta₁ R₁)).toReal / 2)
  let A₂ : ENNReal := ENNReal.ofReal
    (Real.exp (-Real.sqrt (delta / eta₂)) * (nu₂ (Icc eta₂ R₂)).toReal / 2)
  let B₁ : ENNReal := ENNReal.ofReal ((nu₁ (Ioc 0 R₁)).toReal / 2)
  let B₂ : ENNReal := ENNReal.ofReal ((nu₂ (Ioc 0 R₂)).toReal / 2)
  have hA₁pos : 0 < A₁ := by
    change 0 < ENNReal.ofReal
      (Real.exp (-Real.sqrt (delta / eta₁)) * (nu₁ (Icc eta₁ R₁)).toReal / 2)
    rw [ENNReal.ofReal_pos]
    have hm : 0 < (nu₁ (Icc eta₁ R₁)).toReal :=
      ENNReal.toReal_pos hetaIcc₁ (measure_ne_top nu₁ _)
    positivity
  have hA₂pos : 0 < A₂ := by
    change 0 < ENNReal.ofReal
      (Real.exp (-Real.sqrt (delta / eta₂)) * (nu₂ (Icc eta₂ R₂)).toReal / 2)
    rw [ENNReal.ofReal_pos]
    have hm : 0 < (nu₂ (Icc eta₂ R₂)).toReal :=
      ENNReal.toReal_pos hetaIcc₂ (measure_ne_top nu₂ _)
    positivity
  have hB₁pos : 0 < B₁ := by
    change 0 < ENNReal.ofReal ((nu₁ (Ioc 0 R₁)).toReal / 2)
    rw [ENNReal.ofReal_pos]
    rw [← measure_Ioi_eq_measure_Ioc_of_ae_mem_Icc hsupp₁]
    exact div_pos (ENNReal.toReal_pos hpos₁ (measure_ne_top nu₁ _)) (by norm_num)
  have hB₂pos : 0 < B₂ := by
    change 0 < ENNReal.ofReal ((nu₂ (Ioc 0 R₂)).toReal / 2)
    rw [ENNReal.ofReal_pos]
    rw [← measure_Ioi_eq_measure_Ioc_of_ae_mem_Icc hsupp₂]
    exact div_pos (ENNReal.toReal_pos hpos₂ (measure_ne_top nu₂ _)) (by norm_num)
  let c₀ : ENNReal := A₁ * B₂⁻¹
  let C₀ : ENNReal := B₁ * A₂⁻¹
  let c : ENNReal := min 1 c₀
  let C : ENNReal := max 1 C₀
  refine ⟨c, C, ?_, ?_, ?_, ?_⟩
  · exact lt_min one_pos (ENNReal.mul_pos hA₁pos.ne'
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
  · exact le_trans (min_le_left _ _) (le_max_left _ _)
  · refine max_lt (by simp) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_lt_top.mpr hA₂pos)
  · intro E hE hEsub
    let w : ℝ → ENNReal := E.indicator fun _ => 1
    have hw : Measurable w := measurable_const.indicator hE
    have hbounds₁ := repairedFrequency_weighted_lintegral_bounds hsupp₁ heta₁ hdelta hw
    have hbounds₂ := repairedFrequency_weighted_lintegral_bounds hsupp₂ heta₂ hdelta hw
    have hsimp (m : Measure ℝ) : (∫⁻ x in Ioo 0 delta, w x ∂m) = m E := by
      simp only [w, setLIntegral_indicator hE, inter_eq_left.mpr hEsub, setLIntegral_one]
    change A₁ * (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar)
        ≤ (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu₁) ∧
      (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu₁)
        ≤ B₁ * (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) at hbounds₁
    change A₂ * (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar)
        ≤ (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu₂) ∧
      (∫⁻ x in Ioo 0 delta, w x ∂repairedFrequencyMeasure nu₂)
        ≤ B₂ * (∫⁻ x in Ioo 0 delta, w x ∂positiveMultiplicativeHaar) at hbounds₂
    rw [hsimp positiveMultiplicativeHaar, hsimp (repairedFrequencyMeasure nu₁)] at hbounds₁
    rw [hsimp positiveMultiplicativeHaar, hsimp (repairedFrequencyMeasure nu₂)] at hbounds₂
    constructor
    · calc
        c * repairedFrequencyMeasure nu₂ E
            ≤ c₀ * repairedFrequencyMeasure nu₂ E :=
          mul_le_mul_left (min_le_right _ _) _
        _ ≤ c₀ * (B₂ * positiveMultiplicativeHaar E) :=
          mul_le_mul_right hbounds₂.2 _
        _ = A₁ * positiveMultiplicativeHaar E := by
          simp only [c₀]
          calc
            (A₁ * B₂⁻¹) * (B₂ * positiveMultiplicativeHaar E) =
                A₁ * (B₂⁻¹ * B₂) * positiveMultiplicativeHaar E := by ac_rfl
            _ = A₁ * positiveMultiplicativeHaar E := by
              rw [ENNReal.inv_mul_cancel hB₂pos.ne' ENNReal.ofReal_ne_top, mul_one]
        _ ≤ repairedFrequencyMeasure nu₁ E := hbounds₁.1
    · calc
        repairedFrequencyMeasure nu₁ E ≤ B₁ * positiveMultiplicativeHaar E := hbounds₁.2
        _ = C₀ * (A₂ * positiveMultiplicativeHaar E) := by
          simp only [C₀]
          calc
            B₁ * positiveMultiplicativeHaar E =
                B₁ * (A₂⁻¹ * A₂) * positiveMultiplicativeHaar E := by
              rw [ENNReal.inv_mul_cancel hA₂pos.ne' ENNReal.ofReal_ne_top, mul_one]
            _ = (B₁ * A₂⁻¹) * (A₂ * positiveMultiplicativeHaar E) := by ac_rfl
        _ ≤ C₀ * repairedFrequencyMeasure nu₂ E :=
          mul_le_mul_right hbounds₂.1 _
        _ ≤ C * repairedFrequencyMeasure nu₂ E :=
          mul_le_mul_left (le_max_right _ _) _

/-- Local bounded equivalence transported to arbitrary positive sources realizing the two target
moment sequences. -/
theorem exists_sourceMeasure_local_bounded_equivalence_of_shiftedFactorialMoments
    {nu₁ nu₂ : Measure ℝ} [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    {R₁ R₂ delta : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hdelta : 0 < delta)
    (hsupp₁ : ∀ᵐ y ∂nu₁, y ∈ Icc 0 R₁) (hsupp₂ : ∀ᵐ y ∂nu₂, y ∈ Icc 0 R₂)
    (hpos₁ : nu₁ (Ioi 0) ≠ 0) (hpos₂ : nu₂ (Ioi 0) ≠ 0)
    {mu₁ mu₂ : Measure ℝ} (hmu₁ : ∀ᵐ x ∂mu₁, 0 ≤ x) (hmu₂ : ∀ᵐ x ∂mu₂, 0 ≤ x)
    (hmomInt₁ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu₁)
    (hmomInt₂ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu₂)
    (hmom₁ : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu₁)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu₁)
    (hmom₂ : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu₂)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu₂) :
    ∃ c C : ENNReal, 0 < c ∧ c ≤ C ∧ C < ⊤ ∧
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo 0 delta →
        c * mu₂ E ≤ mu₁ E ∧ mu₁ E ≤ C * mu₂ E := by
  obtain ⟨c, C, hc, hcC, hC, hbounded⟩ :=
    exists_repairedFrequencyMeasure_local_bounded_equivalence hdelta hsupp₁ hsupp₂ hpos₁ hpos₂
  refine ⟨c, C, hc, hcC, hC, ?_⟩
  intro E hE hEsub
  have hsub : E ⊆ Ioi (0 : ℝ) := fun x hx => hEsub hx |>.1
  have heq₁ := restrict_Ioi_eq_repairedFrequencyMeasure_of_shiftedFactorialMoments
    hR₁ hsupp₁ hmu₁ hmomInt₁ hmom₁
  have heq₂ := restrict_Ioi_eq_repairedFrequencyMeasure_of_shiftedFactorialMoments
    hR₂ hsupp₂ hmu₂ hmomInt₂ hmom₂
  have hmeasure₁ : mu₁ E = repairedFrequencyMeasure nu₁ E := by
    calc
      mu₁ E = (mu₁.restrict (Ioi 0)) E := by
        rw [Measure.restrict_apply hE, inter_eq_left.mpr hsub]
      _ = repairedFrequencyMeasure nu₁ E := congrArg (fun m : Measure ℝ => m E) heq₁
  have hmeasure₂ : mu₂ E = repairedFrequencyMeasure nu₂ E := by
    calc
      mu₂ E = (mu₂.restrict (Ioi 0)) E := by
        rw [Measure.restrict_apply hE, inter_eq_left.mpr hsub]
      _ = repairedFrequencyMeasure nu₂ E := congrArg (fun m : Measure ℝ => m E) heq₂
  rw [hmeasure₁, hmeasure₂]
  exact hbounded E hE hEsub

end

end GaloisForLFunctions.HTGeometry
