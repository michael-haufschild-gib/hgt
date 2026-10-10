import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureAmplifiedExponentDensity
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley

/-!
# Deep HCF amplification has Ingham–Huxley density

At height `t` the Gaussian-amplified HCF diagonal `𝒜(t, σ)` grows at the rate of the deepest zero
cone over `t`.  Depth `> κ` at `t` needs a zero copy `z = γ − i(β − ½)` with
`(γ − t)² < (β − ½)² − κ`, hence a zero with `β ≥ ½ + √κ` at height within `½` of `t`.

**Theorem** (`eventually_volume_amplifiedTrace_exceeds_exp_le_inghamHuxley`).  For `0 < κ < ¼` and
`0 < ε ≤ 1` there are `D, B, T₀` such that for `T ≥ T₀` the heights `t ∈ [T + ½, 2T − ½]` at which
`𝒜(t, ·)` is not dominated by `e^{σκ} H(t)` have measure at most
`D (1 + log T)^B T^{1 − (4/3)√κ + ε}`.

The exponent comes from `A(σ)(1 − σ) ≤ 1 − (4/3)(σ − ½)` for the Ingham–Huxley exponent `A`
(`inghamHuxleyExponent_mul_le`), and improves the power saving `U^{1 − √κ/40}`
of `eventually_volume_criticalFeatureAmplifiedDeepShadow_le_powerSaving`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The Ingham–Huxley density exponent at `½ + s` saves at least `(4/3) s`. -/
theorem inghamHuxleyExponent_mul_le {s : ℝ} (hs : 0 < s) (hs2 : s < 1 / 2) :
    inghamHuxleyExponent (1 / 2 + s) * (1 - (1 / 2 + s)) ≤ 1 - 4 / 3 * s := by
  unfold inghamHuxleyExponent
  split_ifs with h1 h2
  · have hd : 0 < 2 - (1 / 2 + s) := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith
  · have hd : 0 < 3 * (1 / 2 + s) - 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    push Not at h1
    nlinarith
  · linarith

theorem re_xiZeroCopy_eq (q : XiZeroCopy) : ((q.1 : ℂ)).re = 1 / 2 - (xiSpectralPoint q).im := by
  simp [xiSpectralPoint]

/-- **The deep shadow is covered by Ingham–Huxley boxes.**  Heights in `[T + ½, 2T − ½]` of depth
`> κ` lie within `½` of the ordinate of a copy with `Re ρ ≥ ½ + √κ` and `T ≤ Im ρ ≤ 2T`. -/
theorem deepShadow_subset_box {κ T : ℝ} (hκ : 0 < κ) :
    criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T + 1 / 2) (2 * T - 1 / 2) ⊆
      ⋃ q ∈ (zeroHeightBox_finite (1 / 2 + Real.sqrt κ) T).toFinset,
        Ioo ((q.1 : ℂ).im - 1 / 2) ((q.1 : ℂ).im + 1 / 2) := by
  rintro t ⟨⟨q, hq⟩, ht⟩
  have hq4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  have hη2 : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by rw [him, neg_sq]; exact hq4
  have hdeep : κ < (xiSpectralPoint q).im ^ 2 := by nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
  have hnear : |(xiSpectralPoint q).re - t| < 1 / 2 := by
    have h1 : ((xiSpectralPoint q).re - t) ^ 2 < (1 / 2) ^ 2 := by nlinarith
    exact abs_lt_of_sq_lt_sq' h1 (by norm_num) |> fun h => abs_lt.2 h
  have hsq : Real.sqrt κ < |(xiSpectralPoint q).im| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt hκ.le hdeep
  -- the copy on the right of the critical line
  obtain ⟨q', hre', him'⟩ : ∃ q' : XiZeroCopy, (xiSpectralPoint q').re = (xiSpectralPoint q).re ∧
      (xiSpectralPoint q').im = -|(xiSpectralPoint q).im| := by
    by_cases h0 : (xiSpectralPoint q).im ≤ 0
    · exact ⟨q, rfl, by rw [abs_of_nonpos h0, neg_neg]⟩
    · push Not at h0
      refine ⟨xiZeroCopyLineConjEquiv q, ?_, ?_⟩
      · rw [xiSpectralPoint_lineConj, Complex.conj_re]
      · rw [xiSpectralPoint_lineConj, Complex.conj_im, abs_of_pos h0]
  have hγ : ((q'.1 : ℂ)).im = (xiSpectralPoint q).re := by rw [← xiSpectralPoint_re_eq, hre']
  have hbox : q' ∈ (zeroHeightBox_finite (1 / 2 + Real.sqrt κ) T).toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, ?_, ?_⟩
    · rw [re_xiZeroCopy_eq, him']; linarith
    · rw [hγ]; linarith [(abs_lt.1 hnear).1, ht.1]
    · rw [hγ]; linarith [(abs_lt.1 hnear).2, ht.2]
  refine mem_iUnion₂.2 ⟨q', hbox, ?_⟩
  rw [hγ]
  constructor <;> linarith [(abs_lt.1 hnear).1, (abs_lt.1 hnear).2]

/-- **Ingham–Huxley density of the deep shadow.** -/
theorem eventually_volume_deepShadow_le_inghamHuxley {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ < 1 / 4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      volume (criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T + 1 / 2) (2 * T - 1 / 2)) ≤
        ENNReal.ofReal (D * (1 + Real.log T) ^ B * T ^ (1 - 4 / 3 * Real.sqrt κ + ε)) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hs2 : Real.sqrt κ < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ := exists_zeroHeightBox_ncard_le_ingham_huxley
    (σ := 1 / 2 + Real.sqrt κ) (ε := ε) (by linarith) (by linarith) hε hε1
  refine ⟨D, hD, B, T₀, hT₀, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := hT₀.trans hT
  set F := (zeroHeightBox_finite (1 / 2 + Real.sqrt κ) T).toFinset with hF
  have hvol : volume (criticalFeatureAmplifiedDeepShadow κ ∩ Icc (T + 1 / 2) (2 * T - 1 / 2)) ≤
      F.card := by
    refine (measure_mono (deepShadow_subset_box hκ)).trans ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    have h1 : ∀ q ∈ F, volume (Ioo ((q.1 : ℂ).im - 1 / 2) ((q.1 : ℂ).im + 1 / 2)) = 1 := by
      intro q _
      rw [Real.volume_Ioo]; norm_num
    rw [Finset.sum_congr rfl h1]
    simp
  refine hvol.trans ?_
  have hcard : (F.card : ℝ) = ((zeroHeightBox (1 / 2 + Real.sqrt κ) T).ncard : ℝ) := by
    rw [hF, Set.ncard_eq_toFinset_card _ (zeroHeightBox_finite _ _)]
  have h1 := hcount T hT
  rw [← hcard] at h1
  have hexp : (inghamHuxleyExponent (1 / 2 + Real.sqrt κ) + ε) * (1 - (1 / 2 + Real.sqrt κ)) ≤
      1 - 4 / 3 * Real.sqrt κ + ε := by
    have := inghamHuxleyExponent_mul_le hs hs2
    have h2 : ε * (1 - (1 / 2 + Real.sqrt κ)) ≤ ε := by nlinarith
    nlinarith
  have hpow : T ^ ((inghamHuxleyExponent (1 / 2 + Real.sqrt κ) + ε) * (1 - (1 / 2 + Real.sqrt κ))) ≤
      T ^ (1 - 4 / 3 * Real.sqrt κ + ε) := Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have h3 : (F.card : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (1 - 4 / 3 * Real.sqrt κ + ε) := by
    refine h1.trans (mul_le_mul_of_nonneg_left hpow ?_)
    have : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h3

/-- **Deep HCF amplification is Ingham–Huxley rare.**  For `0 < κ < ¼` and `0 < ε ≤ 1`, for all large
`T` the heights `t ∈ [T + ½, 2T − ½]` at which the amplified HCF trace is not dominated by
`e^{σκ} H(t)` for all `σ ≥ 0` have measure at most `D (1 + log T)^B T^{1 − (4/3)√κ + ε}`. -/
theorem eventually_volume_amplifiedTrace_exceeds_exp_le_inghamHuxley {κ ε : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 1 / 4) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      volume {t : ℝ | t ∈ Icc (T + 1 / 2) (2 * T - 1 / 2) ∧
        ¬ ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
          Real.exp (σ * κ) * criticalFeatureHermitianEnergyTrace t} ≤
        ENNReal.ofReal (D * (1 + Real.log T) ^ B * T ^ (1 - 4 / 3 * Real.sqrt κ + ε)) := by
  obtain ⟨D, hD, B, T₀, hT₀, h⟩ := eventually_volume_deepShadow_le_inghamHuxley hκ hκ4 hε hε1
  refine ⟨D, hD, B, T₀, hT₀, fun T hT => (measure_mono ?_).trans (h T hT)⟩
  rintro t ⟨ht, hfail⟩
  refine ⟨?_, ht⟩
  by_contra hns
  exact hfail fun σ hσ => norm_criticalFeatureGaussianAmplifiedTrace_le_exp_of_not_mem_deepShadow hns hσ

end

end RHTower
