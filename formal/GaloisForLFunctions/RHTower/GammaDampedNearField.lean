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

end

end RHTower
