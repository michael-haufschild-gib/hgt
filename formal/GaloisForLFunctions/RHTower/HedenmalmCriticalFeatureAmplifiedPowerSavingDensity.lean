import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureAmplifiedExponentDensity
import GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget

/-!
# Deep HCF amplification is polynomially rare

The HCF amplified diagonal `𝒜(t, σ)` at height `t` grows like `e^{σ M(t)}`, where `M(t)` is the
depth of the deepest zero cone over `t`.  RH says that `M ≡ 0`.  Unconditionally the heights with
`M(t) > κ` (the depth-`κ` shadow) have density zero
(`eventually_volume_amplifiedTrace_exceeds_exp_le`).

**Theorem** (`eventually_volume_amplifiedTrace_exceeds_exp_le_powerSaving`).  For every
`0 < κ ≤ 1`, for all large `U`, the heights `t ∈ [U/4 + 2, U/2 - 2]` at which `𝒜(t, ·)` is not
dominated by `e^{σκ} H(t)` have measure at most `U^{1 - √κ/40}`.  This is a power saving.

Mechanism.  A copy of depth `> κ` over `t` gives a zero `ρ` with `Re ρ > 1/2 + √κ` whose shadow
`|Im ρ - t| < Re ρ - 1/2 < 1/2` contains `t` (`DeBruijn.exists_xiZero_of_obstruct`).  So the deep
shadow in the window is covered by shadows of at most `U^{1 - √κ/40}` zeros, counted with
multiplicity (`exists_zetaZeroDensity_powerSaving`), each of length `< 1`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Power-saving window bound for the deep shadow.** -/
theorem eventually_volume_criticalFeatureAmplifiedDeepShadow_le_powerSaving {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      volume (criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T₁ + 1) (T₂ - 1)) ≤
        ENNReal.ofReal (U ^ (1 - Real.sqrt κ / 40)) := by
  classical
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsκ1 : Real.sqrt κ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hκ1
  filter_upwards [exists_zetaZeroDensity_powerSaving hsκ hsκ1, eventually_ge_atTop (100 : ℝ)]
    with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hdens⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zc := Z.filter (fun w => 1 / 2 + Real.sqrt κ ≤ w.re)
  have hsub : criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T₁ + 1) (T₂ - 1) ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨⟨q, hq⟩, ht⟩
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hdeep : (Real.sqrt κ) ^ 2 < (xiSpectralPoint q).im ^ 2 := by
      rw [Real.sq_sqrt hκ.le]
      nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
    have hlt : ((xiSpectralPoint q).re - t) ^ 2 < (xiSpectralPoint q).im ^ 2 := by linarith
    obtain ⟨ρ, hρ0, hρ1, hρ2, hρx⟩ := DeBruijn.exists_xiZero_of_obstruct ht0
      (riemannHeat_zero_xiSpectralPoint q) hdeep hlt hsκ.le
    have hζρ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hρx' := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hζρ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hρ1.le⟩,
      ⟨by linarith, by linarith⟩⟩
  have hm : ∀ w ∈ Zc, 1 / 2 ≤ w.re ∧ 1 ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    intro w hw
    obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub hm).trans (ENNReal.ofReal_le_ofReal ?_)
  -- each shadow has length `2 (Re w - 1/2) < 1`
  have hshort : ∀ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
      ((analyticOrderAt riemannZeta w).toNat : ℝ) / 2 := by
    intro w hw
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hw0⟩ := (hZ w).mp hwZ
    have hre1 : w.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h hw0
    have hm0 : (0 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcount := hdens Z hZ
  calc 2 * ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)
      ≤ 2 * ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) / 2 := by
        gcongr with w hw; exact hshort w hw
    _ = ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by ring
    _ ≤ U ^ (1 - Real.sqrt κ / 40) := hcount

/-- **Deep HCF amplification is polynomially rare.**  For every `0 < κ ≤ 1`, for all large `U`, the
heights `t ∈ [U/4 + 2, U/2 - 2]` at which the amplified HCF trace is not dominated by
`e^{σκ} H(t)` for all `σ ≥ 0` have measure at most `U^{1 - √κ/40}`. -/
theorem eventually_volume_amplifiedTrace_exceeds_exp_le_powerSaving {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) :
    ∀ᶠ U in atTop,
      volume {t : ℝ | t ∈ Icc (U / 4 + 2) (U / 2 - 2) ∧
        ¬ ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
          Real.exp (σ * κ) * criticalFeatureHermitianEnergyTrace t} ≤
        ENNReal.ofReal (U ^ (1 - Real.sqrt κ / 40)) := by
  filter_upwards [eventually_volume_criticalFeatureAmplifiedDeepShadow_le_powerSaving hκ hκ1]
    with U hU
  obtain ⟨T₁, hT₁, T₂, hT₂, hvol⟩ := hU
  have hsub : {t : ℝ | t ∈ Icc (U / 4 + 2) (U / 2 - 2) ∧
      ¬ ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
        Real.exp (σ * κ) * criticalFeatureHermitianEnergyTrace t} ⊆
      criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T₁ + 1) (T₂ - 1) := by
    rintro t ⟨ht, hfail⟩
    refine ⟨?_, ⟨by linarith [ht.1, hT₁.2], by linarith [ht.2, hT₂.1]⟩⟩
    by_contra hns
    exact hfail fun σ hσ =>
      norm_criticalFeatureGaussianAmplifiedTrace_le_exp_of_not_mem_deepShadow hns hσ
  exact (measure_mono hsub).trans hvol

end

end RHTower
