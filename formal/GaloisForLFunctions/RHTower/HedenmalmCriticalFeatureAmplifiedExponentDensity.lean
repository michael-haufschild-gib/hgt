import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureGaussianAmplifiedReceiver
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMoment

/-!
# The amplification exponent of the HCF trace vanishes at almost every height

For a height `t` the Gaussian-amplified critical-feature diagonal
`𝒜(t, σ) = Σ_γ F_t(γ)² exp(-σ (γ - t)²)` grows at most like `exp(σ δ)` whenever no zero copy has
light-cone depth `(Im γ)² - (Re γ - t)²` exceeding `δ`
(`norm_criticalFeatureGaussianAmplifiedTrace_le_exp_of_not_mem_deepShadow`).  The heights where
some copy is deeper form the depth-`δ` shadow (`criticalFeatureAmplifiedDeepShadow δ`).

**Theorem** (`eventually_volume_amplifiedTrace_exceeds_exp_le`).  For every `δ > 0` and `η > 0`, for
all large `U`, the heights `t ∈ [U/4 + 2, U/2 - 2]` at which `𝒜(t, ·)` is not dominated by
`exp(σ δ) · H(t)` have measure at most `η U`.

Mechanism.  A copy of depth greater than `δ` at height `t` yields a zero `ρ` with
`Re ρ > 1/2 + √δ` whose shadow `|Im ρ - t| < Re ρ - 1/2` contains `t`.  The tail first moment of such
zeros in a Littlewood window is at most `(D/c)(T₂ - T₁) + K log² U` with `c = √δ log U`
(`exists_offLineTailMoment_window_le`).  So the depth-`δ` shadow has relative measure
`O(1/(√δ log U)) + O(log² U / U) → 0`.

RH is the statement that every exponent is zero at every height.  This module gives the
unconditional density form: for each fixed `δ > 0`, exponents above `δ` occur only on a set of
heights of density zero.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The depth-`δ` amplified shadow: heights whose light cone contains a zero copy of depth `> δ`. -/
def criticalFeatureAmplifiedDeepShadow (δ : ℝ) : Set ℝ :=
  {t | ∃ q : XiZeroCopy,
    ((xiSpectralPoint q).re - t) ^ 2 < (xiSpectralPoint q).im ^ 2 - δ}

/-- **Exponent bound off the deep shadow.** -/
theorem norm_criticalFeatureGaussianAmplifiedTrace_le_exp_of_not_mem_deepShadow {δ t : ℝ}
    (ht : t ∉ criticalFeatureAmplifiedDeepShadow δ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
      Real.exp (σ * δ) * criticalFeatureHermitianEnergyTrace t := by
  have hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 - δ ≤ ((xiSpectralPoint q).re - t) ^ 2 := fun q => by
    by_contra h
    exact ht ⟨q, not_le.1 h⟩
  have hterm : ∀ q : XiZeroCopy,
      ‖criticalFeatureGaussianAmplifiedTerm t σ (xiSpectralPoint q)‖ ≤
        Real.exp (σ * δ) * Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) :=
    fun q => by
      rw [norm_criticalFeatureGaussianAmplifiedTerm, mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Complex.normSq_nonneg _)
      have := hcone q
      nlinarith
  rw [criticalFeatureHermitianEnergyTrace, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ)).trans
    ((summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ).tsum_le_tsum hterm
      ((criticalFeatureHermitianEnergy_summable t).mul_left _))

/-- A Xi zero copy's spectral point is a zero of the heat-flow function `Ξ = riemannHeat 0`. -/
theorem riemannHeat_zero_xiSpectralPoint (q : XiZeroCopy) :
    DeBruijn.riemannHeat 0 (xiSpectralPoint q) = 0 := by
  have hq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  rw [xiSpectralPoint_eq_support, xiSpectralPointSupport, DeBruijn.riemannHeat_zero]
  convert hq using 1
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- **Window bound for the deep shadow.** -/
theorem exists_volume_criticalFeatureAmplifiedDeepShadow_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        volume (criticalFeatureAmplifiedDeepShadow δ ∩ Icc (T₁ + 1) (T₂ - 1)) ≤
          ENNReal.ofReal
            (2 * (D / (Real.sqrt δ * Real.log U) * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, fun δ hδ => ?_⟩
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 / Real.sqrt δ))] with U hU hU100 hlogU
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  set c := Real.sqrt δ * Real.log U with hcdef
  have hc2 : 2 ≤ c := by
    rw [hcdef]
    have := mul_le_mul_of_nonneg_left hlogU hsδ.le
    rwa [mul_div_cancel₀ _ hsδ.ne'] at this
  have hy₀ : c / Real.log U = Real.sqrt δ := by rw [hcdef]; field_simp
  set Zc := Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re)
  have hsub : criticalFeatureAmplifiedDeepShadow δ ∩ Icc (T₁ + 1) (T₂ - 1) ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨⟨q, hq⟩, ht⟩
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hdeep : (Real.sqrt δ) ^ 2 < (xiSpectralPoint q).im ^ 2 := by
      rw [Real.sq_sqrt hδ.le]
      nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
    have hlt : ((xiSpectralPoint q).re - t) ^ 2 < (xiSpectralPoint q).im ^ 2 := by linarith
    obtain ⟨ρ, hρ0, hρ1, hρ2, hρx⟩ := DeBruijn.exists_xiZero_of_obstruct ht0
      (riemannHeat_zero_xiSpectralPoint q) hdeep hlt hsδ.le
    have hζρ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hρx' := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hζρ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, by rw [hy₀]; exact hρ1.le⟩,
      ⟨by linarith, by linarith⟩⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    have hcL : 0 ≤ c / Real.log U := by rw [hy₀]; exact hsδ.le
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  · have := hc Z hZ c hc2
    have hDc : D / c = D / (Real.sqrt δ * Real.log U) := by rw [hcdef]
    rw [← hDc]
    linarith

/-- **The amplification exponent is asymptotically zero at almost every height.**  For every
`δ > 0` and `η > 0`, for all large `U`, the heights `t ∈ [U/4 + 2, U/2 - 2]` at which the amplified
HCF trace is not dominated by `exp(σ δ) · H(t)` for all `σ ≥ 0` have measure at most `η U`. -/
theorem eventually_volume_amplifiedTrace_exceeds_exp_le {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ U in atTop,
      volume {t : ℝ | t ∈ Icc (U / 4 + 2) (U / 2 - 2) ∧
        ¬ ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
          Real.exp (σ * δ) * criticalFeatureHermitianEnergyTrace t} ≤ ENNReal.ofReal (η * U) := by
  obtain ⟨D, K, hD, hK, hwin⟩ := exists_volume_criticalFeatureAmplifiedDeepShadow_le
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  -- the normalized bound tends to zero
  have hlim : Tendsto (fun U : ℝ =>
      D / (Real.sqrt δ * Real.log U) + K * (Real.log U ^ 2 / (1 * U + 0)))
      atTop (𝓝 (0 + K * 0)) := by
    refine Tendsto.add ?_ ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul _)
    have h0 : Tendsto (fun U : ℝ => Real.sqrt δ * Real.log U) atTop atTop :=
      Real.tendsto_log_atTop.const_mul_atTop hsδ
    have h1 := (h0.inv_tendsto_atTop).const_mul D
    rw [mul_zero] at h1
    exact h1.congr fun U => by rw [div_eq_mul_inv]; rfl
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) + K * 0 < η / 2 by simpa using hη))
  filter_upwards [hwin δ hδ, hsmall, eventually_ge_atTop (100 : ℝ)] with U hU hsm hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hvol⟩ := hU
  have hsub : {t : ℝ | t ∈ Icc (U / 4 + 2) (U / 2 - 2) ∧
      ¬ ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
        Real.exp (σ * δ) * criticalFeatureHermitianEnergyTrace t} ⊆
      criticalFeatureAmplifiedDeepShadow δ ∩ Icc (T₁ + 1) (T₂ - 1) := by
    rintro t ⟨ht, hfail⟩
    refine ⟨?_, ⟨by linarith [ht.1, hT₁.2], by linarith [ht.2, hT₂.1]⟩⟩
    by_contra hns
    exact hfail fun σ hσ =>
      norm_criticalFeatureGaussianAmplifiedTrace_le_exp_of_not_mem_deepShadow hns hσ
  refine (measure_mono hsub).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  have hU0 : 0 < U := by linarith
  have hT : T₂ - T₁ ≤ U := by linarith [hT₁.1, hT₂.2]
  have h1 : D / (Real.sqrt δ * Real.log U) * (T₂ - T₁) ≤ D / (Real.sqrt δ * Real.log U) * U :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have h2 : K * Real.log U ^ 2 = K * (Real.log U ^ 2 / (1 * U + 0)) * U := by
    rw [one_mul, add_zero]; field_simp
  have h3 := mul_lt_mul_of_pos_right hsm hU0
  have h4 : (D / (Real.sqrt δ * Real.log U) + K * (Real.log U ^ 2 / (1 * U + 0))) * U =
      D / (Real.sqrt δ * Real.log U) * U + K * (Real.log U ^ 2 / (1 * U + 0)) * U := by ring
  rw [h2]
  linarith

end

end RHTower
