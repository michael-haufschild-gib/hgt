import GaloisForLFunctions.RHTower.GaussianCentralGapLargeHeightFiniteOffLine
import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionInghamHuxley

/-!
# The Gaussian central gap has every positive rate off a power-saving set of heights

Let `F(ε, τ)` be the Gaussian-filtered central prime gap at scale `ε` and height `2τ`
(`gaussianFilteredCentralGap`).  Its large-height growth rate is `Θ∞ + Θ∞²/8`, where `Θ∞` is the
limit superior of `Re ρ − ½` (`eventualFilteredCentralGapRate_iff`), and "every rate `s > 0` at all
large heights" is "zeros approach the line", which implies the Lindelöf hypothesis.

**Theorem** (`exists_volume_filteredCentralGapRateFailure_le_inghamHuxley`).  Fix `0 < s ≤ 17/32`
and put `σ = ½ + 16s/17`.  For every `0 < ε ≤ 1` there are `C, B, T₀` such that for `T ≥ T₀` the
heights `τ ∈ [T, 2T]` at which `F(·, τ)` is not `O(e^{sε}√ε)` have Lebesgue measure at most
`C (1 + log T)^B T^{(A(σ) + ε)(1 − σ)}`, where `A` is the Ingham–Huxley exponent.

**Corollary** (`exists_volume_filteredCentralGapRateFailure_le_rpow_lt_one`).  For every `s > 0`
there is `θ < 1` such that the failure heights in `[T, 2T]` have measure at most `T^θ` for large
`T`.  So the zeros-approach-the-line rung of route TG holds unconditionally at all heights outside a
power-saving exceptional set, for every rate.

**Proof.**  At height `τ` a zero `ρ` with `b = Re ρ − ½` has light-cone exponent
`Re w_ρ(τ) = (γ/2 − τ)²/2 − b − b²/8`.  If every zero has `Re w_ρ(τ) ≥ −s`, the gap is
`O(e^{sε}√ε)` (`exists_filteredCentralGap_le_exp_of_re_ge`).  So a failure height has a zero with
`b + b²/8 > s`, hence `b > 16s/17`, and `|γ/2 − τ| < 2`, since `b + b²/8 < 17/32`.  The failure
heights in `[T, 2T]` lie in the intervals of length `4` around `γ/2` for the zero copies with
`Re ρ ≥ σ` and ordinate in `[2T − 4, 4T + 4]`, which the cumulative Ingham–Huxley count bounds
(`exists_ncard_zeroCopyRange_le`).
-/

noncomputable section

open Complex MeasureTheory Filter

namespace RHTower

open XiAtlasFinitePart

/-- Heights `τ` at which the filtered central gap is not `O(e^{sε}√ε)`. -/
def filteredCentralGapRateFailureHeights (s : ℝ) : Set ℝ :=
  {τ | ¬ ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
    ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε}

/-- A failure height lies within `2` of half the ordinate of a zero with `b + b²/8 > s`. -/
theorem exists_copy_of_mem_filteredCentralGapRateFailureHeights {s τ : ℝ} (hs : 0 ≤ s)
    (hτ : τ ∈ filteredCentralGapRateFailureHeights s) :
    ∃ q : XiZeroCopy, s < ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8 ∧
      |(xiZero q).im / 2 - τ| < 2 := by
  by_contra hno
  push Not at hno
  apply hτ
  refine exists_filteredCentralGap_le_exp_of_re_ge hs fun q => ?_
  rw [re_zeroLightConeExponent]
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  by_cases hq : s < ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8
  · have hfar := hno q hq
    have hsq : 4 ≤ ((xiZero q).im / 2 - τ) ^ 2 := by
      nlinarith [sq_abs ((xiZero q).im / 2 - τ), abs_nonneg ((xiZero q).im / 2 - τ)]
    nlinarith
  · push Not at hq
    nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]

/-- **The failure heights of rate `s` have Ingham–Huxley size.** -/
theorem exists_volume_filteredCentralGapRateFailure_le_inghamHuxley {s ε : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 17 / 32) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ, ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      volume (filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T)) ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent (1 / 2 + 16 * s / 17) + ε) *
            (1 - (1 / 2 + 16 * s / 17)))) := by
  classical
  set σ : ℝ := 1 / 2 + 16 * s / 17 with hσdef
  have hσ : 1 / 2 < σ := by rw [hσdef]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ := exists_ncard_zeroCopyRange_le hσ hσ1 hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by
    have hA := (inghamHuxleyExponent_mem hσ).1
    rw [hE]; exact mul_nonneg (by linarith) (by linarith)
  have hEle : E ≤ 2 := by
    have hA := (inghamHuxleyExponent_mem hσ).2
    rw [hE]; nlinarith
  refine ⟨4 * (2 * D * 6 ^ (B + 1) * 64), by positivity, B + 1, T₀ + 4, by linarith,
    fun T hT => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  set Y : ℝ := 4 * T + 4 with hY
  have hfin := zeroCopyRange_finite σ T₀ Y hT₀0
  set F : Finset XiZeroCopy := hfin.toFinset with hF
  -- the failure set lies in the intervals of length `4` around half the ordinates of `F`
  have hsub : filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T) ⊆
      ⋃ q ∈ F, Set.Icc (((q.1 : ℂ)).im / 2 - 2) (((q.1 : ℂ)).im / 2 + 2) := by
    rintro τ ⟨hτ, hτT⟩
    obtain ⟨q, hqs, hqim⟩ := exists_copy_of_mem_filteredCentralGapRateFailureHeights hs.le hτ
    have hzq : xiZero q = (q.1 : ℂ) := rfl
    rw [hzq] at hqs hqim
    have habs := abs_lt.mp hqim
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    rw [hzq] at hb
    have hre : σ ≤ ((q.1 : ℂ)).re := by
      rw [hσdef]
      have hbpos : 0 < ((q.1 : ℂ)).re - 1 / 2 := by nlinarith
      nlinarith
    refine Set.mem_iUnion₂.mpr ⟨q, hfin.mem_toFinset.mpr ⟨hre, ?_, ?_⟩, ?_, ?_⟩
    · linarith [hτT.1]
    · rw [hY]; linarith [hτT.2]
    · linarith
    · linarith
  have hvol : volume (filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T)) ≤
      4 * F.card := by
    calc volume (filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T))
        ≤ volume (⋃ q ∈ F, Set.Icc (((q.1 : ℂ)).im / 2 - 2) (((q.1 : ℂ)).im / 2 + 2)) :=
          measure_mono hsub
      _ ≤ ∑ q ∈ F, volume (Set.Icc (((q.1 : ℂ)).im / 2 - 2) (((q.1 : ℂ)).im / 2 + 2)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ _q ∈ F, (4 : ENNReal) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Real.volume_Icc]
          rw [show ((q.1 : ℂ)).im / 2 + 2 - (((q.1 : ℂ)).im / 2 - 2) = 4 by ring]
          norm_num
      _ = 4 * F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : (F.card : ℝ) = (zeroCopyRange σ T₀ Y).ncard := by
    rw [hF, Set.ncard_eq_toFinset_card _ hfin]
  have hYT : T₀ ≤ Y := by rw [hY]; linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hYpos : (0 : ℝ) < Y := by rw [hY]; linarith
  have hlogY : 1 + Real.log Y ≤ 6 * (1 + Real.log T) := by
    have h8T : Y ≤ 8 * T := by rw [hY]; linarith
    have := Real.log_le_log hYpos h8T
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have hl8 : Real.log 8 ≤ 5 := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hpowY : Y ^ E ≤ 64 * T ^ E := by
    calc Y ^ E ≤ (8 * T) ^ E := Real.rpow_le_rpow hYpos.le (by rw [hY]; linarith) hE0
      _ = 8 ^ E * T ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 64 * T ^ E := by
          gcongr
          calc (8 : ℝ) ^ E ≤ 8 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEle
            _ = 64 := by norm_num
  have hlogY0 : 0 ≤ 1 + Real.log Y := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Y by rw [hY]; linarith); linarith
  have hreal : (F.card : ℝ) ≤ 2 * D * 6 ^ (B + 1) * 64 * (1 + Real.log T) ^ (B + 1) * T ^ E := by
    rw [hcard]
    calc ((zeroCopyRange σ T₀ Y).ncard : ℝ)
        ≤ 2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E := hcount Y hYT
      _ ≤ 2 * D * (6 * (1 + Real.log T)) ^ (B + 1) * (64 * T ^ E) := by gcongr
      _ = 2 * D * 6 ^ (B + 1) * 64 * (1 + Real.log T) ^ (B + 1) * T ^ E := by
          rw [mul_pow]; ring
  calc volume (filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T)) ≤ 4 * F.card := hvol
    _ = ENNReal.ofReal (4 * (F.card : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (4 * (2 * D * 6 ^ (B + 1) * 64) * (1 + Real.log T) ^ (B + 1) * T ^ E) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

/-- A larger rate fails on fewer heights. -/
theorem filteredCentralGapRateFailureHeights_mono {s s' : ℝ} (hss' : s ≤ s') :
    filteredCentralGapRateFailureHeights s' ⊆ filteredCentralGapRateFailureHeights s := by
  intro τ hτ hgood
  apply hτ
  obtain ⟨C, hC⟩ := hgood
  refine ⟨max C 0, fun ε hε => ?_⟩
  have hexp : Real.exp (s * ε) ≤ Real.exp (s' * ε) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hss' (by linarith))
  calc ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε := hC ε hε
    _ ≤ max C 0 * Real.exp (s * ε) * Real.sqrt ε := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * Real.exp (s' * ε) * Real.sqrt ε := by gcongr

/-- **Power saving.**  For every rate `s > 0` there is `θ < 1` such that for large `T` the heights
in `[T, 2T]` at which the filtered central gap is not `O(e^{sε}√ε)` have measure at most `T^θ`. -/
theorem exists_volume_filteredCentralGapRateFailure_le_rpow_lt_one {s : ℝ} (hs : 0 < s) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (filteredCentralGapRateFailureHeights s ∩ Set.Icc T (2 * T)) ≤
        ENNReal.ofReal (T ^ θ) := by
  set s₀ : ℝ := min s (17 / 32) with hs₀
  have hs₀0 : 0 < s₀ := lt_min hs (by norm_num)
  have hs₀1 : s₀ ≤ 17 / 32 := min_le_right _ _
  have hmono := filteredCentralGapRateFailureHeights_mono (min_le_left s (17 / 32))
  set σ : ℝ := 1 / 2 + 16 * s₀ / 17 with hσdef
  have hσ : 1 / 2 < σ := by rw [hσdef]; linarith
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ]
  set ε : ℝ := min 1 g with hε
  have hε0 : 0 < ε := lt_min one_pos hg0
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨C, hC, B, T₁, hT₁, hbound⟩ :=
    exists_volume_filteredCentralGapRateFailure_le_inghamHuxley hs₀0 hs₀1 hε0 hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ 1 - σ := by rw [hσdef]; linarith
    rw [hE]
    have : ε * (1 - σ) ≤ g / 2 := by nlinarith
    nlinarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) C)
  refine ⟨1 - g / 4, by linarith, max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := hT₁.trans hTT₁
  refine (measure_mono (Set.inter_subset_inter_left _ hmono)).trans
    ((hbound T hTT₁).trans (ENNReal.ofReal_le_ofReal ?_))
  calc C * (1 + Real.log T) ^ B * T ^ E ≤ T ^ (g / 4) * T ^ (1 - g / 2) :=
        mul_le_mul (hT₂ T hTT₂) (Real.rpow_le_rpow_of_exponent_le hT1 hEg) (by positivity)
          (by positivity)
    _ = T ^ (1 - g / 4) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

end RHTower

end
