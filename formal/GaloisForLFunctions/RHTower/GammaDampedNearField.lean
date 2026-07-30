import GaloisForLFunctions.RHTower.GammaDampedFarField

/-!
# Uniform Laurent bounds on the near-field window

All critical-line points `α - iu` with `1 < σ ≤ 2` and `|u| ≤ 6π` lie in the compact set

```text
K = closedBall 1 (1/2 + 6π) ∩ {re ≥ 1} ⊆ {re > 1/2},
```

on which the two Laurent parts `B(z) = 1/(Γℝ(z)ζ(2z))` and `C(z) = A(z)/ζ(2z) + H(z)` and their
derivatives are continuous, hence uniformly bounded.  This is the uniform constant the near-field
estimate needs.
-/

open Metric

namespace RHTower

noncomputable section

/-- The compact near-field window of the critical line. -/
def nearFieldSet : Set ℂ := Metric.closedBall 1 (1 / 2 + 6 * Real.pi) ∩ {z : ℂ | 1 ≤ z.re}

theorem isCompact_nearFieldSet : IsCompact nearFieldSet := by
  refine (isCompact_closedBall (1 : ℂ) (1 / 2 + 6 * Real.pi)).inter_right ?_
  exact isClosed_le continuous_const Complex.continuous_re

theorem nearFieldSet_subset : nearFieldSet ⊆ {z : ℂ | 1 / 2 < z.re} := by
  intro z hz
  have h : (1 : ℝ) ≤ z.re := hz.2
  exact lt_of_lt_of_le (by norm_num) h

theorem mem_nearFieldSet {σ u : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hu : |u| ≤ 6 * Real.pi) :
    gammaDampedCriticalLinePoint σ u ∈ nearFieldSet := by
  constructor
  · rw [Metric.mem_closedBall, Complex.dist_eq]
    have hre : (gammaDampedCriticalLinePoint σ u - 1).re = (σ - 1) / 2 := by
      simp [gammaDampedCriticalLinePoint]
      ring
    have him : (gammaDampedCriticalLinePoint σ u - 1).im = -u := by
      simp [gammaDampedCriticalLinePoint]
    have hb := Complex.norm_le_abs_re_add_abs_im (gammaDampedCriticalLinePoint σ u - 1)
    rw [hre, him, abs_neg] at hb
    have h1 : |(σ - 1) / 2| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    linarith
  · show (1 : ℝ) ≤ (gammaDampedCriticalLinePoint σ u).re
    rw [gammaDampedCriticalLinePoint_re]
    linarith

/-! ### The uniform bound -/

theorem analyticOnNhd_gammaDampedResidueFactor :
    AnalyticOnNhd ℂ gammaDampedResidueFactor {z : ℂ | 1 / 2 < z.re} :=
  fun _ hz => analyticAt_gammaDampedResidueFactor hz

theorem analyticOnNhd_gammaDampedPoleFree :
    AnalyticOnNhd ℂ gammaDampedPoleFree {z : ℂ | 1 / 2 < z.re} :=
  fun _ hz => analyticAt_gammaDampedPoleFree hz

/-- **The uniform Laurent bound on the near-field window.** -/
theorem exists_nearField_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M := by
  have hcB : ContinuousOn gammaDampedResidueFactor nearFieldSet :=
    (analyticOnNhd_gammaDampedResidueFactor.mono nearFieldSet_subset).continuousOn
  have hcB' : ContinuousOn (deriv gammaDampedResidueFactor) nearFieldSet :=
    ((analyticOnNhd_gammaDampedResidueFactor.mono nearFieldSet_subset).deriv).continuousOn
  have hcC : ContinuousOn gammaDampedPoleFree nearFieldSet :=
    (analyticOnNhd_gammaDampedPoleFree.mono nearFieldSet_subset).continuousOn
  have hcC' : ContinuousOn (deriv gammaDampedPoleFree) nearFieldSet :=
    ((analyticOnNhd_gammaDampedPoleFree.mono nearFieldSet_subset).deriv).continuousOn
  obtain ⟨MB, hMB⟩ := isCompact_nearFieldSet.exists_bound_of_continuousOn hcB
  obtain ⟨MB', hMB'⟩ := isCompact_nearFieldSet.exists_bound_of_continuousOn hcB'
  obtain ⟨MC, hMC⟩ := isCompact_nearFieldSet.exists_bound_of_continuousOn hcC
  obtain ⟨MC', hMC'⟩ := isCompact_nearFieldSet.exists_bound_of_continuousOn hcC'
  refine ⟨max 0 (max (max MB MB') (max MC MC')), le_max_left _ _, fun z hz => ?_⟩
  refine ⟨le_trans (hMB z hz) ?_, le_trans (hMB' z hz) ?_, le_trans (hMC z hz) ?_,
    le_trans (hMC' z hz) ?_⟩
  · exact le_trans (le_trans (le_max_left MB MB') (le_max_left _ _)) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_right MB MB') (le_max_left _ _)) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_left MC MC') (le_max_right _ _)) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_right MC MC') (le_max_right _ _)) (le_max_right _ _)

/-! ### The Laurent split of the symbol -/

/-- The pole part of the spectral symbol. -/
def gammaDampedPolePart (σ u : ℝ) : ℂ :=
  gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
      (gammaDampedCriticalLinePoint σ u - 1) ^ 2 -
    ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
      gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
      (gammaDampedCriticalLinePoint σ u - 1)

/-- The regular part of the spectral symbol. -/
def gammaDampedRegPart (σ u : ℝ) : ℂ :=
  -(deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
      (gammaDampedCriticalLinePoint σ u - 1)) -
    deriv gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u) -
    ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
      gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)

theorem gammaDampedCriticalLinePoint_sub_one_re (σ u : ℝ) :
    (gammaDampedCriticalLinePoint σ u - 1).re = (σ - 1) / 2 := by
  simp [gammaDampedCriticalLinePoint]
  ring

theorem norm_gammaDampedCriticalLinePoint_sub_one_ge {σ u : ℝ} (hσ1 : 1 < σ) :
    (σ - 1) / 2 ≤ ‖gammaDampedCriticalLinePoint σ u - 1‖ := by
  have h := Complex.abs_re_le_norm (gammaDampedCriticalLinePoint σ u - 1)
  rw [gammaDampedCriticalLinePoint_sub_one_re, abs_of_nonneg (by linarith : (0:ℝ) ≤ (σ-1)/2)] at h
  exact h

theorem gammaDampedCriticalLinePoint_sub_one_ne_zero {σ u : ℝ} (hσ1 : 1 < σ) :
    gammaDampedCriticalLinePoint σ u - 1 ≠ 0 := by
  intro h
  have hge := norm_gammaDampedCriticalLinePoint_sub_one_ge (u := u) hσ1
  rw [h, norm_zero] at hge
  linarith

/-- **The Laurent split.**  `D = (pole part) + (regular part)`. -/
theorem gammaDampedSymbol_eq_polePart_add_regPart {σ u : ℝ} (hσ1 : 1 < σ) :
    gammaDampedSymbol σ u = gammaDampedPolePart σ u + gammaDampedRegPart σ u := by
  have hre : 1 < (gammaDampedCriticalLinePoint σ u).re := by
    rw [gammaDampedCriticalLinePoint_re]
    linarith
  have hne := gammaDampedCriticalLinePoint_sub_one_ne_zero (u := u) hσ1
  rw [gammaDampedSymbol, deriv_lSeries_gammaDampedCoeff hre,
    lSeries_gammaDampedCoeff_laurent hre, gammaDampedPolePart, gammaDampedRegPart]
  field_simp
  ring

/-- **The regular part is `O(1/ε)` on the near-field window.** -/
theorem norm_gammaDampedRegPart_le {σ u M : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hu : |u| ≤ 6 * Real.pi) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) :
    ‖gammaDampedRegPart σ u‖ ≤ M * (5 / (σ - 1)) := by
  have hε : (0 : ℝ) < σ - 1 := by linarith
  have hmem := mem_nearFieldSet hσ1 hσ2 hu
  obtain ⟨hB, hB', hC, hC'⟩ := hM _ hmem
  have hznorm : (σ - 1) / 2 ≤ ‖gammaDampedCriticalLinePoint σ u - 1‖ :=
    norm_gammaDampedCriticalLinePoint_sub_one_ge hσ1
  have hzpos : (0 : ℝ) < ‖gammaDampedCriticalLinePoint σ u - 1‖ := by linarith
  have hdiv : ‖deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
      (gammaDampedCriticalLinePoint σ u - 1)‖ ≤ M * (2 / (σ - 1)) := by
    rw [norm_div, div_le_iff₀ hzpos]
    have hinv : (1 : ℝ) ≤ (2 / (σ - 1)) * ‖gammaDampedCriticalLinePoint σ u - 1‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      linarith
    nlinarith [hB', hM0, norm_nonneg (deriv gammaDampedResidueFactor
      (gammaDampedCriticalLinePoint σ u))]
  have hmC : squarefreeMobiusLogMoment 1 σ *
      ‖gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)‖ ≤ (2 / (σ - 1)) * M := by
    refine mul_le_mul hm hC (norm_nonneg _) (by positivity)
  have hone : M ≤ M * (1 / (σ - 1)) := by
    have h1 : (1 : ℝ) ≤ 1 / (σ - 1) := by
      rw [le_div_iff₀ hε]
      linarith
    nlinarith
  calc ‖gammaDampedRegPart σ u‖
      ≤ ‖deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
          (gammaDampedCriticalLinePoint σ u - 1)‖ +
        ‖deriv gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)‖ +
        squarefreeMobiusLogMoment 1 σ *
          ‖gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)‖ := by
        rw [gammaDampedRegPart]
        have h1 := norm_sub_le
          (-(deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
            (gammaDampedCriticalLinePoint σ u - 1)) -
            deriv gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u))
          (((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
            gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u))
        have h2 := norm_sub_le
          (-(deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) /
            (gammaDampedCriticalLinePoint σ u - 1)))
          (deriv gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u))
        have h3 : ‖((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
            gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)‖
            = squarefreeMobiusLogMoment 1 σ *
              ‖gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
        rw [norm_neg] at h2
        linarith
    _ ≤ M * (2 / (σ - 1)) + M * (1 / (σ - 1)) + (2 / (σ - 1)) * M := by
        linarith [hdiv, hC', hmC, hone]
    _ = M * (5 / (σ - 1)) := by ring

/-! ### The energy in density form -/

/-- **The odd energy of `(21)` as a density integral.** -/
theorem gammaDampedOddEnergy_eq_density {σ : ℝ} (hσ : 1 < σ) :
    (∫ y : ℝ, ((gammaDampedSymbol σ y).im) ^ 2 ∂HTGeometry.gammaCyclicMeasure)
      = ∫ x : ℝ, ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x :=
  HTGeometry.integral_gammaCyclicMeasure_eq_density
    ((Complex.continuous_im.comp (continuous_gammaDampedSymbol hσ)).pow 2)

/-! ### Continuity of the two parts -/

theorem continuous_criticalPath (σ : ℝ) :
    Continuous fun u : ℝ => gammaDampedCriticalLinePoint σ u := by
  unfold gammaDampedCriticalLinePoint
  fun_prop

theorem analyticAt_parts {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    AnalyticAt ℂ gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) ∧
      AnalyticAt ℂ gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u) := by
  have hre : (1 : ℝ) / 2 < (gammaDampedCriticalLinePoint σ u).re := by
    rw [gammaDampedCriticalLinePoint_re]
    linarith
  exact ⟨analyticAt_gammaDampedResidueFactor hre, analyticAt_gammaDampedPoleFree hre⟩

theorem continuous_gammaDampedRegPart {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun u : ℝ => gammaDampedRegPart σ u := by
  have hpath := continuous_criticalPath σ
  have hB' : Continuous fun u : ℝ =>
      deriv gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      ((((analyticAt_parts hσ u).1).deriv).continuousAt).comp hpath.continuousAt
  have hC : Continuous fun u : ℝ => gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (((analyticAt_parts hσ u).2).continuousAt).comp hpath.continuousAt
  have hC' : Continuous fun u : ℝ =>
      deriv gammaDampedPoleFree (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      ((((analyticAt_parts hσ u).2).deriv).continuousAt).comp hpath.continuousAt
  have hden : Continuous fun u : ℝ => gammaDampedCriticalLinePoint σ u - 1 :=
    hpath.sub continuous_const
  unfold gammaDampedRegPart
  exact ((hB'.div hden fun u => gammaDampedCriticalLinePoint_sub_one_ne_zero hσ).neg.sub
    hC').sub (continuous_const.mul hC)

theorem continuous_gammaDampedPolePart {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun u : ℝ => gammaDampedPolePart σ u := by
  have hpath := continuous_criticalPath σ
  have hB : Continuous fun u : ℝ => gammaDampedResidueFactor (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (((analyticAt_parts hσ u).1).continuousAt).comp hpath.continuousAt
  have hden : Continuous fun u : ℝ => gammaDampedCriticalLinePoint σ u - 1 :=
    hpath.sub continuous_const
  have hne : ∀ u : ℝ, gammaDampedCriticalLinePoint σ u - 1 ≠ 0 := fun u =>
    gammaDampedCriticalLinePoint_sub_one_ne_zero hσ
  unfold gammaDampedPolePart
  exact (hB.div (hden.pow 2) fun u => pow_ne_zero 2 (hne u)).sub
    ((continuous_const.mul hB).div hden hne)

/-! ### The near-field energy of the regular part -/

open MeasureTheory

theorem setIntegral_gammaCyclicDensity_le_one (S : Set ℝ) :
    (∫ x in S, HTGeometry.gammaCyclicDensity x) ≤ 1 := by
  have h := setIntegral_le_integral (s := S) HTGeometry.integrable_gammaCyclicDensity
    (Filter.Eventually.of_forall HTGeometry.gammaCyclicDensity_nonneg)
  rw [HTGeometry.integral_gammaCyclicDensity] at h
  exact h

theorem isCompact_nearWindow : IsCompact {x : ℝ | |x| ≤ 3} := by
  have : {x : ℝ | |x| ≤ 3} = Set.Icc (-3) 3 := by
    ext x
    simp [abs_le, Set.mem_Icc]
  rw [this]
  exact isCompact_Icc

/-- **The regular part carries `O(1/ε²)` energy on the near window.** -/
theorem gammaDampedNearRegEnergy_le {σ M : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) :
    (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ (5 * M / (σ - 1)) ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ 3} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hcont : Continuous fun x : ℝ =>
      ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x :=
    (((Complex.continuous_im.comp ((continuous_gammaDampedRegPart hσ1).comp
      (by fun_prop))).pow 2).mul HTGeometry.continuous_gammaCyclicDensity)
  have hint : IntegrableOn (fun x : ℝ =>
      ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      {x : ℝ | |x| ≤ 3} :=
    hcont.continuousOn.integrableOn_compact isCompact_nearWindow
  have hintmaj : IntegrableOn (fun x : ℝ =>
      (5 * M / (σ - 1)) ^ 2 * HTGeometry.gammaCyclicDensity x) {x : ℝ | |x| ≤ 3} :=
    (HTGeometry.integrable_gammaCyclicDensity.const_mul _).integrableOn
  have hbound : ∀ x ∈ {x : ℝ | |x| ≤ 3},
      ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x
        ≤ (5 * M / (σ - 1)) ^ 2 * HTGeometry.gammaCyclicDensity x := by
    intro x hx
    have hx3 : |x| ≤ 3 := hx
    have hu : |2 * Real.pi * x| ≤ 6 * Real.pi := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)]
      nlinarith
    have hR := norm_gammaDampedRegPart_le hσ1 hσ2 hu hM0 hM hm0 hm
    have him : |(gammaDampedRegPart σ (2 * Real.pi * x)).im|
        ≤ ‖gammaDampedRegPart σ (2 * Real.pi * x)‖ := Complex.abs_im_le_norm _
    have hsq : ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 ≤ (M * (5 / (σ - 1))) ^ 2 := by
      have h1 : |(gammaDampedRegPart σ (2 * Real.pi * x)).im| ≤ M * (5 / (σ - 1)) :=
        le_trans him hR
      have h2 : (0 : ℝ) ≤ M * (5 / (σ - 1)) := le_trans (abs_nonneg _) h1
      nlinarith [sq_abs ((gammaDampedRegPart σ (2 * Real.pi * x)).im), abs_nonneg
        ((gammaDampedRegPart σ (2 * Real.pi * x)).im)]
    have heq : (M * (5 / (σ - 1))) ^ 2 = (5 * M / (σ - 1)) ^ 2 := by ring
    rw [heq] at hsq
    have hρ : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity x := HTGeometry.gammaCyclicDensity_nonneg x
    nlinarith [hsq, hρ]
  calc (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ ∫ x in {x : ℝ | |x| ≤ 3},
          (5 * M / (σ - 1)) ^ 2 * HTGeometry.gammaCyclicDensity x :=
        setIntegral_mono_on hint hintmaj hmeas hbound
    _ = (5 * M / (σ - 1)) ^ 2 * ∫ x in {x : ℝ | |x| ≤ 3}, HTGeometry.gammaCyclicDensity x := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (5 * M / (σ - 1)) ^ 2 := by
        have h1 := setIntegral_gammaCyclicDensity_le_one {x : ℝ | |x| ≤ 3}
        have h2 : (0 : ℝ) ≤ (5 * M / (σ - 1)) ^ 2 := sq_nonneg _
        nlinarith

/-! ### The scaled pole part -/

/-- The pole part at the scaled critical point, multiplied by `ε²`. -/
def scaledPolePart (ε v : ℝ) : ℂ := ((ε : ℂ)) ^ 2 * gammaDampedPolePart (1 + ε) (ε * v)

theorem gammaDampedCriticalLinePoint_sub_one_eq (ε v : ℝ) :
    gammaDampedCriticalLinePoint (1 + ε) (ε * v) - 1 = (ε : ℂ) * criticalDirection v := by
  rw [← criticalScaledPoint_eq, criticalScaledPoint]
  ring

theorem norm_criticalDirection_sq (v : ℝ) : ‖criticalDirection v‖ ^ 2 = 1 / 4 + v ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, criticalDirection, Complex.normSq_apply]
  simp
  ring

theorem norm_criticalDirection_pos (v : ℝ) : 0 < ‖criticalDirection v‖ :=
  norm_pos_iff.mpr (criticalDirection_ne_zero v)

/-- The scaled pole part in Laurent coordinates. -/
theorem scaledPolePart_eq {ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    scaledPolePart ε v
      = gammaDampedResidueFactor (gammaDampedCriticalLinePoint (1 + ε) (ε * v)) /
          (criticalDirection v) ^ 2 -
        ((ε * squarefreeMobiusLogMoment 1 (1 + ε) : ℝ) : ℂ) *
          gammaDampedResidueFactor (gammaDampedCriticalLinePoint (1 + ε) (ε * v)) /
          criticalDirection v := by
  have hw : criticalDirection v ≠ 0 := criticalDirection_ne_zero v
  have hεc : ((ε : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hε
  rw [scaledPolePart, gammaDampedPolePart, gammaDampedCriticalLinePoint_sub_one_eq]
  push_cast
  field_simp

/-- **The uniform majorant for the scaled pole part.** -/
theorem norm_sq_scaledPolePart_le {ε v M : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 (1 + ε))
    (hmK : ε * squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2)
    (hv : |ε * v| ≤ 6 * Real.pi) :
    ‖scaledPolePart ε v‖ ^ 2 ≤ 2 * M ^ 2 / (1 / 4 + v ^ 2) ^ 2 + 8 * M ^ 2 / (1 / 4 + v ^ 2) := by
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hmem := mem_nearFieldSet hσ1 hσ2 hv
  obtain ⟨hB, -, -, -⟩ := hM _ hmem
  have hwpos : 0 < ‖criticalDirection v‖ := norm_criticalDirection_pos v
  have hwsq : ‖criticalDirection v‖ ^ 2 = 1 / 4 + v ^ 2 := norm_criticalDirection_sq v
  have hεm : (0 : ℝ) ≤ ε * squarefreeMobiusLogMoment 1 (1 + ε) := by positivity
  have hden : (0 : ℝ) < 1 / 4 + v ^ 2 := by positivity
  have hnorm : ‖scaledPolePart ε v‖ ≤ M / (1 / 4 + v ^ 2) + 2 * M / ‖criticalDirection v‖ := by
    rw [scaledPolePart_eq hε v]
    have h1 : ‖gammaDampedResidueFactor (gammaDampedCriticalLinePoint (1 + ε) (ε * v)) /
        (criticalDirection v) ^ 2‖ ≤ M / (1 / 4 + v ^ 2) := by
      rw [norm_div, norm_pow, hwsq]
      gcongr
    have h2 : ‖((ε * squarefreeMobiusLogMoment 1 (1 + ε) : ℝ) : ℂ) *
        gammaDampedResidueFactor (gammaDampedCriticalLinePoint (1 + ε) (ε * v)) /
        criticalDirection v‖ ≤ 2 * M / ‖criticalDirection v‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hεm]
      gcongr
    exact le_trans (norm_sub_le _ _) (by linarith)
  have hnn : (0 : ℝ) ≤ M / (1 / 4 + v ^ 2) + 2 * M / ‖criticalDirection v‖ := by positivity
  have hsq : ‖scaledPolePart ε v‖ ^ 2
      ≤ (M / (1 / 4 + v ^ 2) + 2 * M / ‖criticalDirection v‖) ^ 2 := by
    nlinarith [norm_nonneg (scaledPolePart ε v), hnorm]
  have hsq2 : (2 * M / ‖criticalDirection v‖) ^ 2 = 4 * M ^ 2 / (1 / 4 + v ^ 2) := by
    rw [div_pow, mul_pow, hwsq]
    ring
  have h1 : (M / (1 / 4 + v ^ 2)) ^ 2 = M ^ 2 / (1 / 4 + v ^ 2) ^ 2 := by
    rw [div_pow]
  have hyoung : (M / (1 / 4 + v ^ 2) + 2 * M / ‖criticalDirection v‖) ^ 2
      ≤ 2 * (M / (1 / 4 + v ^ 2)) ^ 2 + 2 * (2 * M / ‖criticalDirection v‖) ^ 2 := by
    nlinarith [sq_nonneg (M / (1 / 4 + v ^ 2) - 2 * M / ‖criticalDirection v‖)]
  rw [h1, hsq2] at hyoung
  have hexpand : 2 * (M ^ 2 / (1 / 4 + v ^ 2) ^ 2) + 2 * (4 * M ^ 2 / (1 / 4 + v ^ 2))
      = 2 * M ^ 2 / (1 / 4 + v ^ 2) ^ 2 + 8 * M ^ 2 / (1 / 4 + v ^ 2) := by
    field_simp
    ring
  rw [hexpand] at hyoung
  linarith [hsq, hyoung]

/-! ### The pointwise limit of the scaled pole part -/

open Filter Topology

theorem eventually_moment_bounds :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ squarefreeMobiusLogMoment 1 (1 + ε) ∧
        ε * squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2 := by
  have h := tendsto_mul_squarefreeMobiusLogMoment
  have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε * squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2 :=
    h.eventually_le_const (by norm_num)
  have h2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (1 : ℝ) / 2 ≤ ε * squarefreeMobiusLogMoment 1 (1 + ε) :=
    h.eventually_const_le (by norm_num)
  filter_upwards [h1, h2, self_mem_nhdsWithin] with ε he1 he2 hε
  have hεpos : (0 : ℝ) < ε := hε
  exact ⟨by nlinarith [he2], he1⟩

theorem eventually_scaled_mem (v : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), |ε * v| ≤ 6 * Real.pi := by
  have hπ : (0 : ℝ) < 6 * Real.pi / (|v| + 1) := by
    have := Real.pi_pos
    positivity
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall := hid.eventually_le_const hπ
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hpos
  have hεpos : (0 : ℝ) < ε := hpos
  have hv : (0 : ℝ) ≤ |v| := abs_nonneg v
  rw [abs_mul, abs_of_pos hεpos]
  have hbound : ε * |v| ≤ (6 * Real.pi / (|v| + 1)) * |v| := by
    exact mul_le_mul_of_nonneg_right hε hv
  have hfrac : (6 * Real.pi / (|v| + 1)) * |v| ≤ 6 * Real.pi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have := Real.pi_pos
    nlinarith
  linarith

theorem eventually_one_lt (_v : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε ∧ ε ≤ 1 := by
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall := hid.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hpos
  exact ⟨hpos, hε⟩

/-- **The scaled regular part vanishes.** -/
theorem tendsto_scaled_regPart (v : ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto (fun ε : ℝ => ((ε : ℂ)) ^ 2 * gammaDampedRegPart (1 + ε) (ε * v))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hlin : Tendsto (fun ε : ℝ => 5 * M * ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun ε : ℝ => 5 * M * ε) (nhds (0 : ℝ)) (nhds (5 * M * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [eventually_moment_bounds, eventually_scaled_mem v, eventually_one_lt v]
    with ε hmom hmem hone
  obtain ⟨hεpos, hε1⟩ := hone
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hR := norm_gammaDampedRegPart_le hσ1 hσ2 hmem hM0 hM hmom.1 (by
    have := hmom.2
    rw [le_div_iff₀ (by linarith : (0:ℝ) < (1 + ε) - 1)]
    linarith)
  have hεc : ‖((ε : ℂ)) ^ 2‖ = ε ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos]
  rw [norm_mul, hεc]
  have hRε : ‖gammaDampedRegPart (1 + ε) (ε * v)‖ ≤ M * (5 / ε) := by
    have h := hR
    rw [show (1 : ℝ) + ε - 1 = ε by ring] at h
    exact h
  have hstep : ε ^ 2 * ‖gammaDampedRegPart (1 + ε) (ε * v)‖ ≤ ε ^ 2 * (M * (5 / ε)) :=
    mul_le_mul_of_nonneg_left hRε (by positivity)
  have heq : ε ^ 2 * (M * (5 / ε)) = 5 * M * ε := by
    field_simp
  linarith [hstep, heq]

/-- **The pointwise limit of the scaled pole part.** -/
theorem tendsto_scaledPolePart (v : ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto (fun ε : ℝ => scaledPolePart ε v) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / riemannZeta 2) *
        ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹))) := by
  have hD := tendsto_sq_mul_gammaDampedSpectralSymbol v
  have hR := tendsto_scaled_regPart v hM0 hM
  have hsub := hD.sub hR
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_one_lt v] with ε hone
  obtain ⟨hεpos, -⟩ := hone
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hsplit := gammaDampedSymbol_eq_polePart_add_regPart (σ := 1 + ε) (u := ε * v) hσ1
  rw [scaledPolePart, gammaDampedSpectralSymbol_eq ε v, hsplit]
  ring

/-! ### The scaled near-field integrand -/

theorem norm_sq_scaledPolePart_le' {ε v M : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 (1 + ε))
    (hmK : ε * squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2)
    (hv : |ε * v| ≤ 6 * Real.pi) :
    ‖scaledPolePart ε v‖ ^ 2 ≤ 64 * M ^ 2 / (1 + v ^ 2) := by
  have hbase := norm_sq_scaledPolePart_le hε hε2 hM0 hM hm0 hmK hv
  have hd1 : (0 : ℝ) < 1 / 4 + v ^ 2 := by positivity
  have hd2 : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have hcmp : (1 : ℝ) / (1 / 4 + v ^ 2) ≤ 4 / (1 + v ^ 2) := by
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith
  have h1 : 2 * M ^ 2 / (1 / 4 + v ^ 2) ^ 2 ≤ 32 * M ^ 2 / (1 + v ^ 2) := by
    have hsq : (1 : ℝ) / (1 / 4 + v ^ 2) ^ 2 ≤ 16 / (1 + v ^ 2) := by
      have hstep : (1 : ℝ) / (1 / 4 + v ^ 2) ^ 2 ≤ 16 / (1 + v ^ 2) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
      have hstep2 : (16 : ℝ) / (1 + v ^ 2) ^ 2 ≤ 16 / (1 + v ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) hd2]
        nlinarith [sq_nonneg v]
      linarith
    have hM2 : (0 : ℝ) ≤ 2 * M ^ 2 := by positivity
    calc 2 * M ^ 2 / (1 / 4 + v ^ 2) ^ 2 = 2 * M ^ 2 * (1 / (1 / 4 + v ^ 2) ^ 2) := by ring
      _ ≤ 2 * M ^ 2 * (16 / (1 + v ^ 2)) := by nlinarith [hsq, hM2]
      _ = 32 * M ^ 2 / (1 + v ^ 2) := by ring
  have h2 : 8 * M ^ 2 / (1 / 4 + v ^ 2) ≤ 32 * M ^ 2 / (1 + v ^ 2) := by
    have hM2 : (0 : ℝ) ≤ 8 * M ^ 2 := by positivity
    calc 8 * M ^ 2 / (1 / 4 + v ^ 2) = 8 * M ^ 2 * (1 / (1 / 4 + v ^ 2)) := by ring
      _ ≤ 8 * M ^ 2 * (4 / (1 + v ^ 2)) := by nlinarith [hcmp, hM2]
      _ = 32 * M ^ 2 / (1 + v ^ 2) := by ring
  have hsum : 32 * M ^ 2 / (1 + v ^ 2) + 32 * M ^ 2 / (1 + v ^ 2) = 64 * M ^ 2 / (1 + v ^ 2) := by
    ring
  linarith

/-- The scaled near-field integrand, cut off to the window where the Laurent bounds hold. -/
def scaledPoleIntegrand (ε v : ℝ) : ℝ :=
  Set.indicator {w : ℝ | |ε * w| ≤ 6 * Real.pi}
    (fun w => ((scaledPolePart ε w).im) ^ 2 *
      HTGeometry.gammaCyclicDensity (ε * w / (2 * Real.pi))) v

theorem measurableSet_scaledWindow (ε : ℝ) :
    MeasurableSet {w : ℝ | |ε * w| ≤ 6 * Real.pi} :=
  measurableSet_le (by fun_prop) measurable_const

theorem continuous_scaledPolePart_im {ε : ℝ} (hε : 0 < ε) :
    Continuous fun v : ℝ => ((scaledPolePart ε v).im) ^ 2 := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have h : Continuous fun v : ℝ => scaledPolePart ε v := by
    unfold scaledPolePart
    exact continuous_const.mul ((continuous_gammaDampedPolePart hσ).comp (by fun_prop))
  exact (Complex.continuous_im.comp h).pow 2

theorem measurable_scaledPoleIntegrand {ε : ℝ} (hε : 0 < ε) :
    Measurable (scaledPoleIntegrand ε) := by
  refine Measurable.indicator ?_ (measurableSet_scaledWindow ε)
  exact ((continuous_scaledPolePart_im hε).measurable).mul
    (HTGeometry.continuous_gammaCyclicDensity.measurable.comp (by fun_prop))

/-- **The uniform majorant of the scaled integrand.** -/
theorem abs_scaledPoleIntegrand_le {ε v M : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 (1 + ε))
    (hmK : ε * squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2) :
    |scaledPoleIntegrand ε v|
      ≤ (64 * M ^ 2 * ∫ t : ℝ, ‖HTGeometry.coshHalf t‖) / (1 + v ^ 2) := by
  have hA : (0 : ℝ) ≤ ∫ t : ℝ, ‖HTGeometry.coshHalf t‖ :=
    MeasureTheory.integral_nonneg fun t => norm_nonneg _
  have hd2 : (0 : ℝ) < 1 + v ^ 2 := by positivity
  by_cases hv : v ∈ {w : ℝ | |ε * w| ≤ 6 * Real.pi}
  · rw [scaledPoleIntegrand, Set.indicator_of_mem hv]
    have hvv : |ε * v| ≤ 6 * Real.pi := hv
    have hsq := norm_sq_scaledPolePart_le' hε hε2 hM0 hM hm0 hmK hvv
    have him : ((scaledPolePart ε v).im) ^ 2 ≤ ‖scaledPolePart ε v‖ ^ 2 := by
      have h := Complex.abs_im_le_norm (scaledPolePart ε v)
      nlinarith [sq_abs ((scaledPolePart ε v).im), abs_nonneg ((scaledPolePart ε v).im),
        norm_nonneg (scaledPolePart ε v)]
    have hρ0 : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity (ε * v / (2 * Real.pi)) :=
      HTGeometry.gammaCyclicDensity_nonneg _
    have hρ : HTGeometry.gammaCyclicDensity (ε * v / (2 * Real.pi))
        ≤ ∫ t : ℝ, ‖HTGeometry.coshHalf t‖ :=
      HTGeometry.gammaCyclicDensity_le_bound _
    have hnn : (0 : ℝ) ≤ ((scaledPolePart ε v).im) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg (by positivity)]
    calc ((scaledPolePart ε v).im) ^ 2 *
          HTGeometry.gammaCyclicDensity (ε * v / (2 * Real.pi))
        ≤ (64 * M ^ 2 / (1 + v ^ 2)) * ∫ t : ℝ, ‖HTGeometry.coshHalf t‖ := by
          refine mul_le_mul (le_trans him hsq) hρ hρ0 (by positivity)
      _ = (64 * M ^ 2 * ∫ t : ℝ, ‖HTGeometry.coshHalf t‖) / (1 + v ^ 2) := by ring
  · rw [scaledPoleIntegrand, Set.indicator_of_notMem hv, abs_zero]
    positivity

/-- **The pointwise limit of the scaled integrand.** -/
theorem tendsto_scaledPoleIntegrand (v : ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto (fun ε : ℝ => scaledPoleIntegrand ε v) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((((1 / riemannZeta 2) *
        ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity 0)) := by
  have hP := tendsto_scaledPolePart v hM0 hM
  have him : Tendsto (fun ε : ℝ => ((scaledPolePart ε v).im) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((((1 / riemannZeta 2) * ((criticalDirection v)⁻¹ ^ 2 -
        (criticalDirection v)⁻¹)).im) ^ 2)) :=
    ((Complex.continuous_im.tendsto _).comp hP).pow 2
  have hρ : Tendsto (fun ε : ℝ => HTGeometry.gammaCyclicDensity (ε * v / (2 * Real.pi)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (HTGeometry.gammaCyclicDensity 0)) := by
    have hc : Continuous fun ε : ℝ => ε * v / (2 * Real.pi) := by fun_prop
    have h0 : (0 : ℝ) * v / (2 * Real.pi) = 0 := by simp
    have harg := hc.tendsto 0
    rw [h0] at harg
    exact (HTGeometry.continuous_gammaCyclicDensity.tendsto 0).comp
      (harg.mono_left nhdsWithin_le_nhds)
  refine (him.mul hρ).congr' ?_
  filter_upwards [eventually_scaled_mem v] with ε hv
  exact (Set.indicator_of_mem (show v ∈ {w : ℝ | |ε * w| ≤ 6 * Real.pi} from hv)
    (fun w : ℝ => ((scaledPolePart ε w).im) ^ 2 *
      HTGeometry.gammaCyclicDensity (ε * w / (2 * Real.pi)))).symm

/-! ### The dominated-convergence limit -/

theorem integrable_poleMajorant (C : ℝ) : MeasureTheory.Integrable fun v : ℝ => C / (1 + v ^ 2) := by
  refine (integrable_inv_one_add_sq.const_mul C).congr ?_
  filter_upwards with v
  rw [div_eq_mul_inv]

/-- **The near-field pole limit.** -/
theorem tendsto_integral_scaledPoleIntegrand {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto (fun ε : ℝ => ∫ v : ℝ, scaledPoleIntegrand ε v)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ v : ℝ, (((1 / riemannZeta 2) *
        ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity 0)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => (64 * M ^ 2 * ∫ t : ℝ, ‖HTGeometry.coshHalf t‖) / (1 + v ^ 2)) ?_ ?_
    (integrable_poleMajorant _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (measurable_scaledPoleIntegrand hε).aestronglyMeasurable
  · filter_upwards [eventually_moment_bounds, eventually_one_lt (0 : ℝ)] with ε hmom hone
    obtain ⟨hεpos, hε1⟩ := hone
    filter_upwards with v
    rw [Real.norm_eq_abs]
    exact abs_scaledPoleIntegrand_le hεpos hε1 hM0 hM hmom.1 hmom.2
  · filter_upwards with v
    exact tendsto_scaledPoleIntegrand v hM0 hM

/-- The limiting value in closed form. -/
theorem integral_poleLimit_eq :
    (∫ v : ℝ, (((1 / riemannZeta 2) *
        ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity 0)
      = HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi) := by
  have hcongr : ∀ v : ℝ, (((1 / riemannZeta 2) *
      ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity 0
      = HTGeometry.gammaCyclicDensity 0 * (6 / Real.pi ^ 2) ^ 2 *
        (criticalPoleProfile v) ^ 2 := by
    intro v
    rw [im_gammaDampedSpectralLimit v]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul, integral_criticalPoleProfile_sq]
  ring

/-! ### The change of variables -/

theorem im_scaledPolePart (ε v : ℝ) :
    (scaledPolePart ε v).im = ε ^ 2 * (gammaDampedPolePart (1 + ε) (ε * v)).im := by
  rw [scaledPolePart, show ((ε : ℂ)) ^ 2 = (((ε ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **The change of variables.**  The scaled integral is the near-field pole energy. -/
theorem integral_scaledPoleIntegrand_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ v : ℝ, scaledPoleIntegrand ε v)
      = 2 * Real.pi * ε ^ 3 * ∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ 3} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hpt : ∀ v : ℝ, scaledPoleIntegrand ε v
      = ε ^ 4 * Set.indicator {x : ℝ | |x| ≤ 3}
          (fun x => ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) ((ε / (2 * Real.pi)) * v) := by
    intro v
    have harg : 2 * Real.pi * ((ε / (2 * Real.pi)) * v) = ε * v := by
      field_simp
    have hdens : (ε / (2 * Real.pi)) * v = ε * v / (2 * Real.pi) := by
      field_simp
    have hiff : ((ε / (2 * Real.pi)) * v ∈ {x : ℝ | |x| ≤ 3}) ↔ (v ∈ {w : ℝ | |ε * w| ≤ 6 * Real.pi}) := by
      simp only [Set.mem_setOf_eq, hdens, abs_div, abs_of_pos hπ]
      rw [div_le_iff₀ hπ]
      constructor <;> intro h <;> linarith
    by_cases hv : v ∈ {w : ℝ | |ε * w| ≤ 6 * Real.pi}
    · rw [scaledPoleIntegrand, Set.indicator_of_mem hv,
        Set.indicator_of_mem (hiff.mpr hv), harg, hdens, im_scaledPolePart]
      ring
    · rw [scaledPoleIntegrand, Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (fun h => hv (hiff.mp h)), mul_zero]
  calc (∫ v : ℝ, scaledPoleIntegrand ε v)
      = ∫ v : ℝ, ε ^ 4 * Set.indicator {x : ℝ | |x| ≤ 3}
          (fun x => ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) ((ε / (2 * Real.pi)) * v) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ε ^ 4 * ∫ v : ℝ, Set.indicator {x : ℝ | |x| ≤ 3}
          (fun x => ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) ((ε / (2 * Real.pi)) * v) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ε ^ 4 * (|(ε / (2 * Real.pi))⁻¹| • ∫ x : ℝ, Set.indicator {x : ℝ | |x| ≤ 3}
          (fun x => ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) x) := by
        rw [MeasureTheory.Measure.integral_comp_mul_left]
    _ = 2 * Real.pi * ε ^ 3 * ∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x := by
        rw [MeasureTheory.integral_indicator hmeas, smul_eq_mul,
          abs_of_pos (by positivity : (0:ℝ) < (ε / (2 * Real.pi))⁻¹)]
        field_simp

/-! ### The Young split of the near-field energy -/

theorem integrableOn_near_sq {σ : ℝ} (_hσ : 1 < σ) (f : ℝ → ℂ) (hf : Continuous f) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => ((f (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      {x : ℝ | |x| ≤ 3} := by
  have hcont : Continuous fun x : ℝ =>
      ((f (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x :=
    (((Complex.continuous_im.comp (hf.comp (by fun_prop))).pow 2).mul
      HTGeometry.continuous_gammaCyclicDensity)
  exact hcont.continuousOn.integrableOn_compact isCompact_nearWindow

/-- **The Young upper bound on the near window.** -/
theorem near_energy_le {σ t : ℝ} (hσ : 1 < σ) (ht : 0 < t) :
    (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ (1 + t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
        + (1 + 1 / t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) := by
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ 3} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hD := integrableOn_near_sq hσ _ (continuous_gammaDampedSymbol hσ)
  have hP := integrableOn_near_sq hσ _ (continuous_gammaDampedPolePart hσ)
  have hR := integrableOn_near_sq hσ _ (continuous_gammaDampedRegPart hσ)
  have hbound : ∀ x ∈ {x : ℝ | |x| ≤ 3},
      ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x
        ≤ (1 + t) * (((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) +
          (1 + 1 / t) * (((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) := by
    intro x _
    have hsplit := gammaDampedSymbol_eq_polePart_add_regPart (σ := σ) (u := 2 * Real.pi * x) hσ
    have him : (gammaDampedSymbol σ (2 * Real.pi * x)).im
        = (gammaDampedPolePart σ (2 * Real.pi * x)).im +
          (gammaDampedRegPart σ (2 * Real.pi * x)).im := by
      rw [hsplit, Complex.add_im]
    have hρ : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity x := HTGeometry.gammaCyclicDensity_nonneg x
    have hyoung : ((gammaDampedPolePart σ (2 * Real.pi * x)).im +
        (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2
        ≤ (1 + t) * ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 +
          (1 + 1 / t) * ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by
      have hkey : 0 ≤ t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im -
          (1 / t) * (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by positivity
      have hexp : t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im -
          (1 / t) * (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2
          = t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 -
            2 * (gammaDampedPolePart σ (2 * Real.pi * x)).im *
              (gammaDampedRegPart σ (2 * Real.pi * x)).im +
            (1 / t) * ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by
        field_simp
        ring
      nlinarith [hkey, hexp]
    rw [him]
    nlinarith [hyoung, hρ]
  calc (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ ∫ x in {x : ℝ | |x| ≤ 3},
          ((1 + t) * (((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) +
          (1 + 1 / t) * (((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x)) := by
        refine MeasureTheory.setIntegral_mono_on hD ((hP.const_mul _).add (hR.const_mul _))
          hmeas hbound
    _ = (1 + t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
        + (1 + 1 / t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) := by
        rw [MeasureTheory.integral_add (hP.const_mul _) (hR.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **The Young lower bound on the near window.** -/
theorem le_near_energy {σ t : ℝ} (hσ : 1 < σ) (ht : 0 < t) :
    (1 - t) * (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      - (1 / t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ ∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x := by
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ 3} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hD := integrableOn_near_sq hσ _ (continuous_gammaDampedSymbol hσ)
  have hP := integrableOn_near_sq hσ _ (continuous_gammaDampedPolePart hσ)
  have hR := integrableOn_near_sq hσ _ (continuous_gammaDampedRegPart hσ)
  have hbound : ∀ x ∈ {x : ℝ | |x| ≤ 3},
      (1 - t) * (((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x) -
        (1 / t) * (((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x)
        ≤ ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x := by
    intro x _
    have hsplit := gammaDampedSymbol_eq_polePart_add_regPart (σ := σ) (u := 2 * Real.pi * x) hσ
    have him : (gammaDampedSymbol σ (2 * Real.pi * x)).im
        = (gammaDampedPolePart σ (2 * Real.pi * x)).im +
          (gammaDampedRegPart σ (2 * Real.pi * x)).im := by
      rw [hsplit, Complex.add_im]
    have hρ : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity x := HTGeometry.gammaCyclicDensity_nonneg x
    have hyoung : (1 - t) * ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 -
        (1 / t) * ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2
        ≤ ((gammaDampedPolePart σ (2 * Real.pi * x)).im +
          (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by
      have hkey : 0 ≤ t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im +
          (1 / t) * (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by positivity
      have hexp : t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im +
          (1 / t) * (gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2
          = t * ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 +
            2 * (gammaDampedPolePart σ (2 * Real.pi * x)).im *
              (gammaDampedRegPart σ (2 * Real.pi * x)).im +
            (1 / t) * ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 := by
        field_simp
        ring
      nlinarith [hkey, hexp, sq_nonneg ((gammaDampedRegPart σ (2 * Real.pi * x)).im)]
    rw [him]
    nlinarith [hyoung, hρ]
  calc (1 - t) * (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      - (1 / t) * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      = ∫ x in {x : ℝ | |x| ≤ 3},
          ((1 - t) * (((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x) -
          (1 / t) * (((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x)) := by
        rw [MeasureTheory.integral_sub (hP.const_mul _) (hR.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ _ := by
        have hPR : MeasureTheory.IntegrableOn (fun x : ℝ =>
            (1 - t) * (((gammaDampedPolePart σ (2 * Real.pi * x)).im) ^ 2 *
              HTGeometry.gammaCyclicDensity x) -
            (1 / t) * (((gammaDampedRegPart σ (2 * Real.pi * x)).im) ^ 2 *
              HTGeometry.gammaCyclicDensity x)) {x : ℝ | |x| ≤ 3} :=
          (hP.const_mul (1 - t)).sub (hR.const_mul (1 / t))
        exact MeasureTheory.setIntegral_mono_on hPR hD hmeas hbound

/-! ### The three energies -/

/-- The near-field pole energy at the critical scaling. -/
def nearPoleEnergy (ε : ℝ) : ℝ :=
  ε ^ 3 * ∫ x in {x : ℝ | |x| ≤ 3},
    ((gammaDampedPolePart (1 + ε) (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x

/-- The near-field regular energy at the critical scaling. -/
def nearRegEnergy (ε : ℝ) : ℝ :=
  ε ^ 3 * ∫ x in {x : ℝ | |x| ≤ 3},
    ((gammaDampedRegPart (1 + ε) (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x

/-- The far-field energy at the critical scaling. -/
def farEnergy (ε : ℝ) : ℝ :=
  ε ^ 3 * ∫ x in {x : ℝ | 3 ≤ |x|},
    ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x

/-- The total odd energy at the critical scaling. -/
def totalEnergy (ε : ℝ) : ℝ :=
  ε ^ 3 * ∫ y : ℝ, ((gammaDampedSymbol (1 + ε) y).im) ^ 2 ∂HTGeometry.gammaCyclicMeasure

theorem tendsto_nearPoleEnergy {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto nearPoleEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / (2 * Real.pi)) *
        (HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi)))) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have hlim := tendsto_integral_scaledPoleIntegrand hM0 hM
  rw [integral_poleLimit_eq] at hlim
  have hconst := hlim.const_mul (1 / (2 * Real.pi))
  refine hconst.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  rw [integral_scaledPoleIntegrand_eq hεpos, nearPoleEnergy]
  field_simp

theorem tendsto_nearRegEnergy {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ nearFieldSet,
      ‖gammaDampedResidueFactor z‖ ≤ M ∧ ‖deriv gammaDampedResidueFactor z‖ ≤ M ∧
        ‖gammaDampedPoleFree z‖ ≤ M ∧ ‖deriv gammaDampedPoleFree z‖ ≤ M) :
    Tendsto nearRegEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hlin : Tendsto (fun ε : ℝ => 25 * M ^ 2 * ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun ε : ℝ => 25 * M ^ 2 * ε) (nhds (0 : ℝ)) (nhds (25 * M ^ 2 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [eventually_moment_bounds, eventually_one_lt (0 : ℝ)] with ε hmom hone
  obtain ⟨hεpos, hε1⟩ := hone
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hbound := gammaDampedNearRegEnergy_le hσ1 hσ2 hM0 hM hmom.1 (by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < (1 + ε) - 1)]
    linarith [hmom.2])
  have hnn : (0 : ℝ) ≤ ∫ x in {x : ℝ | |x| ≤ 3},
      ((gammaDampedRegPart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity x := by
    refine MeasureTheory.setIntegral_nonneg
      (measurableSet_le continuous_abs.measurable measurable_const) fun x _ => ?_
    have := HTGeometry.gammaCyclicDensity_nonneg x
    positivity
  have hεnn : (0 : ℝ) ≤ ε ^ 3 := by positivity
  rw [Real.norm_eq_abs, nearRegEnergy, abs_of_nonneg (by positivity)]
  have hstep : ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3},
      ((gammaDampedRegPart (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity x) ≤ ε ^ 3 * (5 * M / ((1 + ε) - 1)) ^ 2 :=
    mul_le_mul_of_nonneg_left hbound hεnn
  have heq : ε ^ 3 * (5 * M / ((1 + ε) - 1)) ^ 2 = 25 * M ^ 2 * ε := by
    rw [show (1 : ℝ) + ε - 1 = ε by ring]
    field_simp
    ring
  linarith [hstep, heq]

theorem tendsto_farEnergy :
    Tendsto farEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set T : ℝ := ∫ x in {x : ℝ | 3 ≤ |x|},
    (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) ^ 2 *
      HTGeometry.gammaCyclicDensity x with hT
  have hlin : Tendsto (fun ε : ℝ => 144 * T * ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun ε : ℝ => 144 * T * ε) (nhds (0 : ℝ)) (nhds (144 * T * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [eventually_moment_bounds, eventually_one_lt (0 : ℝ)] with ε hmom hone
  obtain ⟨hεpos, hε1⟩ := hone
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hbound := gammaDampedFarEnergy_le hσ1 hσ2 hmom.1 (by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < (1 + ε) - 1)]
    linarith [hmom.2])
  rw [← hT] at hbound
  have hεnn : (0 : ℝ) ≤ ε ^ 3 := by positivity
  have hnn : (0 : ℝ) ≤ ∫ x in {x : ℝ | 3 ≤ |x|},
      ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity x := by
    refine MeasureTheory.setIntegral_nonneg
      (measurableSet_le measurable_const continuous_abs.measurable) fun x _ => ?_
    have := HTGeometry.gammaCyclicDensity_nonneg x
    positivity
  rw [Real.norm_eq_abs, farEnergy, abs_of_nonneg (by positivity)]
  have hstep : ε ^ 3 * (∫ x in {x : ℝ | 3 ≤ |x|},
      ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity x)
      ≤ ε ^ 3 * ((12 / ((1 + ε) - 1)) ^ 2 * T) :=
    mul_le_mul_of_nonneg_left hbound hεnn
  have heq : ε ^ 3 * ((12 / ((1 + ε) - 1)) ^ 2 * T) = 144 * T * ε := by
    rw [show (1 : ℝ) + ε - 1 = ε by ring]
    field_simp
    ring
  linarith [hstep, heq]

/-! ### The critical limit -/

theorem integrable_energy {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) :
    MeasureTheory.Integrable (fun x : ℝ =>
      ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x) := by
  rw [← MeasureTheory.integrableOn_univ]
  have hcover : (Set.univ : Set ℝ) = {x : ℝ | |x| ≤ 3} ∪ {x : ℝ | 3 ≤ |x|} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
    exact (le_total |x| 3).imp id id
  rw [hcover]
  exact (integrableOn_near_sq hσ1 _ (continuous_gammaDampedSymbol hσ1)).union
    (integrableOn_farEnergy hσ1 hσ2 hm0 hm)

theorem totalEnergy_eq {ε : ℝ} (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 (1 + ε))
    (hm : squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2 / ((1 + ε) - 1)) :
    totalEnergy ε
      = ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3},
          ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x)
        + ε ^ 3 * ∫ x in {x : ℝ | |x| ≤ 3}ᶜ,
          ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
            HTGeometry.gammaCyclicDensity x := by
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ 3} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hint := integrable_energy hσ1 hσ2 hm0 hm
  rw [totalEnergy, gammaDampedOddEnergy_eq_density hσ1,
    ← MeasureTheory.integral_add_compl hmeas hint]
  ring

theorem compl_energy_le {ε : ℝ} (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 (1 + ε))
    (hm : squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2 / ((1 + ε) - 1)) :
    0 ≤ ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3}ᶜ,
        ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x)
      ∧ ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3}ᶜ,
        ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x) ≤ farEnergy ε := by
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hσ2 : (1 : ℝ) + ε ≤ 2 := by linarith
  have hnonneg : ∀ x : ℝ, 0 ≤ ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
      HTGeometry.gammaCyclicDensity x := by
    intro x
    have := HTGeometry.gammaCyclicDensity_nonneg x
    positivity
  have hfar := integrableOn_farEnergy hσ1 hσ2 hm0 hm
  have hsub : {x : ℝ | |x| ≤ 3}ᶜ ⊆ {x : ℝ | 3 ≤ |x|} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    exact le_of_lt hx
  have hmono : (∫ x in {x : ℝ | |x| ≤ 3}ᶜ,
      ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ ∫ x in {x : ℝ | 3 ≤ |x|},
        ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x := by
    refine MeasureTheory.setIntegral_mono_set hfar
      (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hsub)
  have hnn : 0 ≤ ∫ x in {x : ℝ | |x| ≤ 3}ᶜ,
      ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
        HTGeometry.gammaCyclicDensity x := by
    refine MeasureTheory.setIntegral_nonneg
      ((measurableSet_le continuous_abs.measurable measurable_const).compl) fun x _ => hnonneg x
  refine ⟨by positivity, ?_⟩
  rw [farEnergy]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **`(17)`: the critical limit of the odd energy.** -/
theorem tendsto_totalEnergy :
    Tendsto totalEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / (2 * Real.pi)) *
        (HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi)))) := by
  obtain ⟨M, hM0, hM⟩ := exists_nearField_bound
  have hP := tendsto_nearPoleEnergy hM0 hM
  have hR := tendsto_nearRegEnergy hM0 hM
  have hF := tendsto_farEnergy
  set Λ := (1 / (2 * Real.pi)) *
    (HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi)) with hΛdef
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 := HTGeometry.gammaCyclicDensity_nonneg 0
    have h2 := Real.pi_pos
    positivity
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set t := min 1 (δ / (8 * (Λ + 1))) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htΛ : t * (Λ + 1) ≤ δ / 8 := by
    have h : t ≤ δ / (8 * (Λ + 1)) := min_le_right _ _
    have hpos : (0 : ℝ) < Λ + 1 := by linarith
    calc t * (Λ + 1) ≤ (δ / (8 * (Λ + 1))) * (Λ + 1) := mul_le_mul_of_nonneg_right h hpos.le
      _ = δ / 8 := by field_simp
  have hPδ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), |nearPoleEnergy ε - Λ| < δ / 8 := by
    have h := Metric.tendsto_nhds.mp hP (δ / 8) (by positivity)
    simpa [Real.dist_eq] using h
  have hPle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), nearPoleEnergy ε ≤ Λ + 1 :=
    hP.eventually_le_const (by linarith)
  have hRδ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), |nearRegEnergy ε| < t * δ / 8 := by
    have h := Metric.tendsto_nhds.mp hR (t * δ / 8) (by positivity)
    simpa [Real.dist_eq] using h
  have hFδ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), |farEnergy ε| < δ / 8 := by
    have h := Metric.tendsto_nhds.mp hF (δ / 8) (by positivity)
    simpa [Real.dist_eq] using h
  filter_upwards [hPδ, hPle, hRδ, hFδ, eventually_moment_bounds, eventually_one_lt (0 : ℝ)]
    with ε hPd hPl hRd hFd hmom hone
  obtain ⟨hεpos, hε1⟩ := hone
  have hσ1 : (1 : ℝ) < 1 + ε := by linarith
  have hmdiv : squarefreeMobiusLogMoment 1 (1 + ε) ≤ 2 / ((1 + ε) - 1) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (1 + ε) - 1)]
    linarith [hmom.2]
  have hsplit := totalEnergy_eq hεpos hε1 hmom.1 hmdiv
  obtain ⟨hc0, hcF⟩ := compl_energy_le hεpos hε1 hmom.1 hmdiv
  have hε3 : (0 : ℝ) ≤ ε ^ 3 := by positivity
  have hupper : ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3},
      ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 * HTGeometry.gammaCyclicDensity x)
      ≤ (1 + t) * nearPoleEnergy ε + (1 + 1 / t) * nearRegEnergy ε := by
    have h := mul_le_mul_of_nonneg_left (near_energy_le (σ := 1 + ε) (t := t) hσ1 ht0) hε3
    rw [nearPoleEnergy, nearRegEnergy]
    nlinarith [h]
  have hlower : (1 - t) * nearPoleEnergy ε - (1 / t) * nearRegEnergy ε
      ≤ ε ^ 3 * (∫ x in {x : ℝ | |x| ≤ 3},
        ((gammaDampedSymbol (1 + ε) (2 * Real.pi * x)).im) ^ 2 *
          HTGeometry.gammaCyclicDensity x) := by
    have h := mul_le_mul_of_nonneg_left (le_near_energy (σ := 1 + ε) (t := t) hσ1 ht0) hε3
    rw [nearPoleEnergy, nearRegEnergy]
    nlinarith [h]
  have habsR := abs_lt.mp hRd
  have habsP := abs_lt.mp hPd
  have habsF := abs_lt.mp hFd
  have h1 : t * nearPoleEnergy ε ≤ δ / 8 :=
    le_trans (mul_le_mul_of_nonneg_left hPl ht0.le) htΛ
  have h2 : (1 / t) * nearRegEnergy ε ≤ δ / 8 := by
    have hstep : (1 / t) * nearRegEnergy ε ≤ (1 / t) * (t * δ / 8) :=
      mul_le_mul_of_nonneg_left (le_of_lt habsR.2) (by positivity)
    have heq : (1 / t) * (t * δ / 8) = δ / 8 := by field_simp
    linarith
  have h2' : -(δ / 8) ≤ (1 / t) * nearRegEnergy ε := by
    have hstep : (1 / t) * (-(t * δ / 8)) ≤ (1 / t) * nearRegEnergy ε :=
      mul_le_mul_of_nonneg_left (le_of_lt habsR.1) (by positivity)
    have heq : (1 / t) * (-(t * δ / 8)) = -(δ / 8) := by field_simp
    linarith
  have h3 : nearRegEnergy ε ≤ δ / 8 := by
    have : t * δ / 8 ≤ δ / 8 := by nlinarith
    linarith [habsR.2]
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hsplit, hc0, hlower, habsP.1, h1, h2]
  · linarith [hsplit, hcF, hupper, habsP.2, h1, h2, h3, habsF.2]

/-! ### The card constant -/

theorem gammaCyclicDensity_zero :
    HTGeometry.gammaCyclicDensity 0 = 2 * Real.pi * gammaCyclicDensityZero := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have hfourier := HTGeometry.fourier_coshHalf_apply 0
  rw [Real.fourier_eq] at hfourier
  have hcongr : ∀ v : ℝ, (Real.fourierChar (-(inner ℝ v (0 : ℝ))) • HTGeometry.coshHalf v)
      = (((Real.cosh v ^ (-(1 / 2) : ℝ) : ℝ)) : ℂ) := by
    intro v
    rw [Real.inner_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, Circle.smul_def]
    simp [HTGeometry.coshHalf]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_complex_ofReal] at hfourier
  have hval : (HTGeometry.gammaCyclicDensity 0 : ℝ)
      = ∫ t : ℝ, Real.cosh t ^ (-(1 / 2) : ℝ) := by
    exact_mod_cast hfourier.symm
  rw [hval, gammaCyclicDensityZero]
  field_simp

/-- The card's normalised critical energy `2√2 ε²/Z(σ) ∫ (Im D)² dν_Γ`. -/
def gammaDampedNormalisedEnergy (ε : ℝ) : ℝ :=
  2 * Real.sqrt 2 * (ε ^ 2 / squarefreeMobiusTotal (1 + ε)) *
    ∫ y : ℝ, ((gammaDampedSymbol (1 + ε) y).im) ^ 2 ∂HTGeometry.gammaCyclicMeasure

/-- **`(17)` in the card's normalisation: the critical energy is `C_Γ`.** -/
theorem tendsto_gammaDampedNormalisedEnergy :
    Tendsto gammaDampedNormalisedEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds gammaCriticalConstant) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the pole scaling in the `ε` parametrisation
  have hmap : Tendsto (fun ε : ℝ => 1 + ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Tendsto (fun ε : ℝ => 1 + ε) (nhds 0) (nhds 1) := by
        simpa using! (continuous_const.add continuous_id).tendsto (0 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : (0 : ℝ) < ε := hε
      simp only [Set.mem_Ioi]
      linarith
  have hZ : Tendsto (fun ε : ℝ => ε * squarefreeMobiusTotal (1 + ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (6 / Real.pi ^ 2)) := by
    refine (tendsto_sub_one_mul_squarefreeMobiusTotal.comp hmap).congr fun ε => ?_
    simp only [Function.comp_apply]
    ring_nf
  have hne : (6 : ℝ) / Real.pi ^ 2 ≠ 0 := by positivity
  have hinv := hZ.inv₀ hne
  have hE := tendsto_totalEnergy
  have hprod := (hinv.const_mul (2 * Real.sqrt 2)).mul hE
  have hval : 2 * Real.sqrt 2 * (6 / Real.pi ^ 2)⁻¹ *
      (1 / (2 * Real.pi) *
        (HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi)))
      = gammaCriticalConstant := by
    rw [gammaCyclicDensity_zero, gammaCriticalConstant_eq_residueDensityProfile,
      re_riemannZeta_two]
    field_simp
  rw [← hval]
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hZpos : 0 < squarefreeMobiusTotal (1 + ε) :=
    squarefreeMobiusTotal_pos (by linarith)
  rw [gammaDampedNormalisedEnergy, totalEnergy]
  field_simp

end

end RHTower
