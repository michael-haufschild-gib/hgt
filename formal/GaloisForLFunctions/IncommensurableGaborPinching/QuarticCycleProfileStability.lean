import GaloisForLFunctions.HTGeometry.AtomlessProjectivePositiveAperture
import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quartic frequency leakage and concentration

Alternating samples from two separated tails force a quartic cycle to leave the
total-variation-two region. Quantiles turn this observation into concentration of
the frequency density, and Cauchy–Schwarz converts concentration into an effective
bandwidth bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace GaloisForLFunctions.IncommensurableGaborPinching

noncomputable section

/-- The four edge differences around a real frequency cycle. -/
def quarticCycleVariation (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  |u.1.1 - u.1.2| + |u.1.2 - u.2.1| +
    |u.2.1 - u.2.2| + |u.2.2 - u.1.1|

/-- Probability mass of cycles outside the total-variation-two region. -/
def quarticCycleLeakage (μ : Measure ℝ) : ℝ :=
  ((μ.prod μ).prod (μ.prod μ)).real {u | 2 < quarticCycleVariation u}

theorem quarticCycleLeakage_nonneg (μ : Measure ℝ) :
    0 ≤ quarticCycleLeakage μ := ENNReal.toReal_nonneg

private theorem variation_of_alternating {a b : ℝ}
    {u : (ℝ × ℝ) × (ℝ × ℝ)}
    (h1 : u.1.1 ≤ a) (h2 : b ≤ u.1.2)
    (h3 : u.2.1 ≤ a) (h4 : b ≤ u.2.2) :
    4 * (b - a) ≤ quarticCycleVariation u := by
  have e1 := le_abs_self (u.1.2 - u.1.1)
  have e2 := le_abs_self (u.1.2 - u.2.1)
  have e3 := le_abs_self (u.2.2 - u.2.1)
  have e4 := le_abs_self (u.2.2 - u.1.1)
  rw [abs_sub_comm u.1.2 u.1.1] at e1
  rw [abs_sub_comm u.2.2 u.2.1] at e3
  dsimp only [quarticCycleVariation]
  linarith

private theorem variation_of_reverse_alternating {a b : ℝ}
    {u : (ℝ × ℝ) × (ℝ × ℝ)}
    (h1 : b ≤ u.1.1) (h2 : u.1.2 ≤ a)
    (h3 : b ≤ u.2.1) (h4 : u.2.2 ≤ a) :
    4 * (b - a) ≤ quarticCycleVariation u := by
  have e1 := le_abs_self (u.1.1 - u.1.2)
  have e2 := le_abs_self (u.2.1 - u.1.2)
  have e3 := le_abs_self (u.2.1 - u.2.2)
  have e4 := le_abs_self (u.1.1 - u.2.2)
  rw [abs_sub_comm u.2.1 u.1.2] at e2
  rw [abs_sub_comm u.1.1 u.2.2] at e4
  dsimp only [quarticCycleVariation]
  linarith

/-- Two separated tails contribute both alternating orientations. -/
theorem two_mul_tail_product_sq_le_quarticCycleLeakage
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ}
    (hab : 1 / 2 < b - a) :
    2 * (μ.real (Iic a) * μ.real (Ioi b)) ^ 2 ≤ quarticCycleLeakage μ := by
  let L : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (Iic a ×ˢ Ioi b) ×ˢ (Iic a ×ˢ Ioi b)
  let R : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (Ioi b ×ˢ Iic a) ×ˢ (Ioi b ×ˢ Iic a)
  let ν := (μ.prod μ).prod (μ.prod μ)
  have hLm : MeasurableSet L :=
    (measurableSet_Iic.prod measurableSet_Ioi).prod
      (measurableSet_Iic.prod measurableSet_Ioi)
  have hRm : MeasurableSet R :=
    (measurableSet_Ioi.prod measurableSet_Iic).prod
      (measurableSet_Ioi.prod measurableSet_Iic)
  have hdis : Disjoint L R := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    have hlow : u.1.1 ≤ a := hu.1.1
    have hhigh : b < u.1.1 := hv.1.1
    linarith
  have hsub : L ∪ R ⊆ {u | 2 < quarticCycleVariation u} := by
    intro u hu
    rcases hu with hu | hu
    · have h := variation_of_alternating hu.1.1 hu.1.2.le hu.2.1 hu.2.2.le
      dsimp only [Set.mem_setOf_eq]
      linarith
    · have h := variation_of_reverse_alternating hu.1.1.le hu.1.2 hu.2.1.le hu.2.2
      dsimp only [Set.mem_setOf_eq]
      linarith
  have hle := ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
  rw [measure_union hdis hRm, ENNReal.toReal_add (measure_ne_top ν _)
    (measure_ne_top ν _)] at hle
  have hL : (ν L).toReal = (μ.real (Iic a) * μ.real (Ioi b)) ^ 2 := by
    simp only [ν, L, Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def]
    ring
  have hR : (ν R).toReal = (μ.real (Iic a) * μ.real (Ioi b)) ^ 2 := by
    simp only [ν, R, Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def]
    ring
  rw [hL, hR] at hle
  simpa only [quarticCycleLeakage, measureReal_def, ν, two_mul] using hle

theorem two_mul_tail_mass_pow_four_le_quarticCycleLeakage
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b ε : ℝ}
    (hab : 1 / 2 < b - a)
    (ha : μ.real (Iic a) = ε) (hb : μ.real (Ioi b) = ε) :
    2 * ε ^ 4 ≤ quarticCycleLeakage μ := by
  have h := two_mul_tail_product_sq_le_quarticCycleLeakage μ hab
  rw [ha, hb] at h
  convert h using 1 <;> ring

/-- Small leakage places the central quantile mass inside a half-length interval. -/
theorem exists_short_interval_mass_of_quarticCycleLeakage_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hleak : quarticCycleLeakage μ < 2 * ε ^ 4) :
    ∃ a b : ℝ, a < b ∧ b - a ≤ 1 / 2 ∧ μ.real (Ioc a b) = 1 - 2 * ε := by
  obtain ⟨a, ha⟩ := HTGeometry.exists_cdf_eq_of_mem_Ioo μ
    (show ε ∈ Ioo (0 : ℝ) 1 from ⟨hε, by linarith⟩)
  obtain ⟨b, hb⟩ := HTGeometry.exists_cdf_eq_of_mem_Ioo μ
    (show 1 - ε ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  have hab : a < b := by
    by_contra hn
    have hc := monotone_cdf μ (le_of_not_gt hn)
    rw [ha, hb] at hc
    linarith
  have hleft : μ.real (Iic a) = ε := by rw [← cdf_eq_real, ha]
  have hright : μ.real (Ioi b) = ε := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, ← cdf_eq_real μ b, hb]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
    ring
  have hshort : b - a ≤ 1 / 2 := by
    by_contra hn
    exact (not_le_of_gt hleak)
      (two_mul_tail_mass_pow_four_le_quarticCycleLeakage μ (lt_of_not_ge hn)
        hleft hright)
  refine ⟨a, b, hab, hshort, ?_⟩
  rw [measureReal_def, ← measure_cdf μ, StieltjesFunction.measure_Ioc, ha, hb]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - ε - ε)]
  ring

/-- The probability law carried by a nonnegative frequency density. -/
def frequencyDensityLaw (w : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (w x))

theorem frequencyDensityLaw_isProbabilityMeasure {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    IsProbabilityMeasure (frequencyDensityLaw w) := by
  constructor
  rw [frequencyDensityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hw0),
    hw1, ENNReal.ofReal_one]

theorem frequencyDensityLaw_noAtoms (w : ℝ → ℝ) :
    NullSingletonClass (frequencyDensityLaw w) := by
  constructor
  intro x
  rw [frequencyDensityLaw, withDensity_apply _ (measurableSet_singleton x)]
  simp

theorem frequencyDensityLaw_real {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (frequencyDensityLaw w).real s = ∫ x in s, w x := by
  rw [measureReal_def, frequencyDensityLaw, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hw.integrableOn
      (Filter.Eventually.of_forall hw0)]
  exact ENNReal.toReal_ofReal (integral_nonneg hw0)

/-- Interval mass cannot exceed the square-root of length times global square energy. -/
theorem frequencyDensityLaw_interval_mass_sq_le {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw2 : Integrable (fun x => w x ^ 2)) {a b : ℝ} (hab : a ≤ b) :
    ((frequencyDensityLaw w).real (Ioc a b)) ^ 2 ≤
      (b - a) * ∫ x, w x ^ 2 := by
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (w x)) volume :=
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hcs := HTGeometry.SchurKernel.sq_lintegral_le_measure_mul
    (volume.restrict (Ioc a b)) hmeas.restrict
  have hglobal : (∫⁻ x in Ioc a b, (ENNReal.ofReal (w x)) ^ 2) ≤
      ENNReal.ofReal (∫ x, w x ^ 2) := by
    calc (∫⁻ x in Ioc a b, (ENNReal.ofReal (w x)) ^ 2)
        ≤ ∫⁻ x, (ENNReal.ofReal (w x)) ^ 2 :=
          lintegral_mono_measure Measure.restrict_le_self
      _ = ∫⁻ x, ENNReal.ofReal (w x ^ 2) := by
          apply lintegral_congr
          intro x
          exact (ENNReal.ofReal_pow (hw0 x) 2).symm
      _ = ENNReal.ofReal (∫ x, w x ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hw2
            (Filter.Eventually.of_forall fun x => sq_nonneg (w x))).symm
  have hfull := hcs.trans (mul_le_mul_left' hglobal _)
  rw [Measure.restrict_apply_univ, Real.volume_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hw.integrableOn
      (Filter.Eventually.of_forall hw0)] at hfull
  have hreal := ENNReal.toReal_mono (by finiteness) hfull
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg hw0),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg (w x))] at hreal
  simpa only [frequencyDensityLaw_real hw hw0 measurableSet_Ioc] using hreal

/-- Every admissible tail level gives an explicit energy lower bound. -/
theorem density_energy_lower_of_quarticCycleLeakage_lt {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1)
    (hw2 : Integrable (fun x => w x ^ 2)) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hleak : quarticCycleLeakage (frequencyDensityLaw w) < 2 * ε ^ 4) :
    2 * (1 - 2 * ε) ^ 2 ≤ ∫ x, w x ^ 2 := by
  letI := frequencyDensityLaw_isProbabilityMeasure hw hw0 hw1
  letI := frequencyDensityLaw_noAtoms w
  obtain ⟨a, b, hab, hshort, hmass⟩ :=
    exists_short_interval_mass_of_quarticCycleLeakage_lt
      (frequencyDensityLaw w) hε hεhalf hleak
  have hcs := frequencyDensityLaw_interval_mass_sq_le hw hw0 hw2 hab.le
  rw [hmass] at hcs
  have hE : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg (w x)
  have hmul := mul_le_mul_of_nonneg_right hshort hE
  linarith

/-- The nonnegative fourth root appearing in the leakage stability estimate. -/
def quarticLeakageRoot (μ : Measure ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (8 * quarticCycleLeakage μ))

theorem quarticLeakageRoot_nonneg (μ : Measure ℝ) : 0 ≤ quarticLeakageRoot μ :=
  Real.sqrt_nonneg _

theorem quarticLeakageRoot_pow_four (μ : Measure ℝ) :
    quarticLeakageRoot μ ^ 4 = 8 * quarticCycleLeakage μ := by
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg (8 * quarticCycleLeakage μ))
  have h2 := Real.sq_sqrt
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (quarticCycleLeakage_nonneg μ))
  change (Real.sqrt (Real.sqrt (8 * quarticCycleLeakage μ))) ^ 4 = _
  calc (Real.sqrt (Real.sqrt (8 * quarticCycleLeakage μ))) ^ 4
      = ((Real.sqrt (Real.sqrt (8 * quarticCycleLeakage μ))) ^ 2) ^ 2 := by ring
    _ = 8 * quarticCycleLeakage μ := by rw [h1, h2]

theorem quarticLeakageRoot_lt_one {μ : Measure ℝ}
    (hδ : quarticCycleLeakage μ < 1 / 8) : quarticLeakageRoot μ < 1 := by
  by_contra h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (le_of_not_gt h) 4
  rw [quarticLeakageRoot_pow_four] at hpow
  norm_num at hpow
  linarith

/-- Leakage bounds the square energy of every probability density from below. -/
theorem density_energy_ge_quartic_leakage {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1)
    (hw2 : Integrable (fun x => w x ^ 2))
    (hδ : quarticCycleLeakage (frequencyDensityLaw w) < 1 / 8) :
    2 * (1 - quarticLeakageRoot (frequencyDensityLaw w)) ^ 2 ≤ ∫ x, w x ^ 2 := by
  let r := quarticLeakageRoot (frequencyDensityLaw w)
  have hr0 : 0 ≤ r := quarticLeakageRoot_nonneg _
  have hr1 : r < 1 := quarticLeakageRoot_lt_one hδ
  have hr4 : r ^ 4 = 8 * quarticCycleLeakage (frequencyDensityLaw w) :=
    quarticLeakageRoot_pow_four _
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (r / 2),
      2 * (1 - 2 * ε) ^ 2 ≤ ∫ x, w x ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show r / 2 < 1 / 2 by linarith)).filter_mono
        nhdsWithin_le_nhds] with ε hε hεhalf
    have hε0 : 0 < ε := lt_of_le_of_lt (by linarith : 0 ≤ r / 2) hε
    have hpow : (r / 2) ^ 4 < ε ^ 4 :=
      pow_lt_pow_left₀ hε (by linarith : 0 ≤ r / 2) (by norm_num)
    have hleak : quarticCycleLeakage (frequencyDensityLaw w) < 2 * ε ^ 4 := by
      nlinarith only [hpow, hr4]
    exact density_energy_lower_of_quarticCycleLeakage_lt hw hw0 hw1 hw2
      hε0 hεhalf hleak
  have hc : Continuous (fun ε : ℝ => 2 * (1 - 2 * ε) ^ 2) := by fun_prop
  have hlim := hc.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (r / 2) ≤ 𝓝 (r / 2))
  have h := le_of_tendsto hlim hevent
  simpa only [show 1 - 2 * (r / 2) = 1 - r by ring] using h

/-- Small quartic leakage forces effective bandwidth close to one half. -/
theorem effectiveBandwidth_le_of_quarticCycleLeakage {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1)
    (hw2 : Integrable (fun x => w x ^ 2))
    (hδ : quarticCycleLeakage (frequencyDensityLaw w) < 1 / 8) :
    1 / (∫ x, w x ^ 2) ≤
      1 / (2 * (1 - quarticLeakageRoot (frequencyDensityLaw w)) ^ 2) := by
  have hroot := quarticLeakageRoot_lt_one hδ
  have hpos : 0 < 2 * (1 - quarticLeakageRoot (frequencyDensityLaw w)) ^ 2 := by
    exact mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr hroot))
  exact one_div_le_one_div_of_le hpos
    (density_energy_ge_quartic_leakage hw hw0 hw1 hw2 hδ)

private theorem real_Ioi_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : ℝ) : μ.real (Ioi b) = 1 - cdf μ b := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, ← cdf_eq_real μ b]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one]

private theorem cdf_eq_one_of_separated_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hδ : quarticCycleLeakage μ = 0) {a b : ℝ}
    (hab : 1 / 2 < b - a) (ha : 0 < cdf μ a) : cdf μ b = 1 := by
  apply le_antisymm (cdf_le_one μ b)
  by_contra hb
  have hb' : 0 < 1 - cdf μ b := by linarith
  have hpos := sq_pos_of_pos (mul_pos ha hb')
  have h := two_mul_tail_product_sq_le_quarticCycleLeakage μ hab
  rw [← cdf_eq_real μ a, real_Ioi_eq_one_sub_cdf μ b, hδ] at h
  linarith

/-- Zero leakage is exactly concentration on a half-length interval. -/
theorem quarticCycleLeakage_eq_zero_iff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    quarticCycleLeakage μ = 0 ↔ ∃ a : ℝ, μ.real (Ioc a (a + 1 / 2)) = 1 := by
  constructor
  · intro hδ
    obtain ⟨m, hm⟩ := HTGeometry.exists_cdf_eq_of_mem_Ioo μ
      (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    let A : Set ℝ := {x | 0 < cdf μ x}
    have hAne : A.Nonempty := ⟨m, by dsimp only [A, Set.mem_setOf_eq]; rw [hm]; norm_num⟩
    have hAbdd : BddBelow A := by
      refine ⟨m - 1, ?_⟩
      intro x hx
      by_contra h
      have hgap : 1 / 2 < m - x := by linarith
      have hfull := cdf_eq_one_of_separated_positive_tail μ hδ hgap hx
      rw [hm] at hfull
      norm_num at hfull
    let a := sInf A
    have hleft : ∀ x : ℝ, x < a → cdf μ x = 0 := by
      intro x hx
      apply le_antisymm _ (cdf_nonneg μ x)
      by_contra h
      have hxA : x ∈ A := lt_of_not_ge h
      have hax : a ≤ x := csInf_le hAbdd hxA
      linarith
    have ha0 : cdf μ a = 0 := by
      have hc := (HTGeometry.continuous_cdf_of_noAtoms μ).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] a ≤ 𝓝 a)
      have hle : cdf μ a ≤ 0 := le_of_tendsto hc (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hleft x hx).le)
      exact le_antisymm hle (cdf_nonneg μ a)
    have hright : ∀ x : ℝ, a + 1 / 2 < x → cdf μ x = 1 := by
      intro x hx
      obtain ⟨z, hzA, hzx⟩ := exists_lt_of_csInf_lt hAne
        (show sInf A < x - 1 / 2 by dsimp only [a] at hx; linarith)
      exact cdf_eq_one_of_separated_positive_tail μ hδ (by linarith) hzA
    have hb1 : cdf μ (a + 1 / 2) = 1 := by
      have hc := (HTGeometry.continuous_cdf_of_noAtoms μ).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (a + 1 / 2) ≤ 𝓝 (a + 1 / 2))
      have hge : 1 ≤ cdf μ (a + 1 / 2) := ge_of_tendsto hc (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hright x hx).ge)
      exact le_antisymm (cdf_le_one μ _) hge
    refine ⟨a, ?_⟩
    rw [measureReal_def, ← measure_cdf μ, StieltjesFunction.measure_Ioc, ha0, hb1]
    norm_num
  · rintro ⟨a, ha⟩
    let I := Ioc a (a + 1 / 2)
    let R : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (I ×ˢ I) ×ˢ (I ×ˢ I)
    let ν := (μ.prod μ).prod (μ.prod μ)
    have hRm : MeasurableSet R :=
      (measurableSet_Ioc.prod measurableSet_Ioc).prod
        (measurableSet_Ioc.prod measurableSet_Ioc)
    have hR : ν.real R = 1 := by
      simp only [ν, R, I, measureReal_prod_prod, ha, one_mul]
    have hdist : ∀ x ∈ I, ∀ y ∈ I, |x - y| ≤ 1 / 2 := by
      intro x hx y hy
      exact abs_sub_le_iff.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
    have hsub : {u | 2 < quarticCycleVariation u} ⊆ Rᶜ := by
      intro u hu hmem
      have h1 := hdist _ hmem.1.1 _ hmem.1.2
      have h2 := hdist _ hmem.1.2 _ hmem.2.1
      have h3 := hdist _ hmem.2.1 _ hmem.2.2
      have h4 := hdist _ hmem.2.2 _ hmem.1.1
      dsimp only [quarticCycleVariation, Set.mem_setOf_eq] at hu
      linarith
    have hle := measureReal_mono (μ := ν) hsub
    rw [measureReal_compl hRm, hR] at hle
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, sub_self] at hle
    exact le_antisymm hle (quarticCycleLeakage_nonneg μ)

end

end GaloisForLFunctions.IncommensurableGaborPinching
