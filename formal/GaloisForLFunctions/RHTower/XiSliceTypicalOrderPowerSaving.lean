import GaloisForLFunctions.RHTower.XiSliceTypicalOrderPositivity
import GaloisForLFunctions.RHTower.XiLogDerivRePositivePowerSaving
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Slice positivity at fixed-ratio orders off a power-saving set of heights

Let `c_n(t)` be the Taylor coefficients at `x = 0` of the slice product
`ξ(½ + x + it) ξ(½ − x + it)`. RH is equivalent to `c_{2k}(t) ≥ 0` for every order and height.

**Theorem** (`exists_volume_xiSliceCoeff_nonpos_le_rpow`). For every `η > 0` there is `θ < 1` such
that for all large `T`, the heights `t ∈ [T, 2T]` at which `c_{2k}(t)` is not positive for some
order `k ≥ η log t` have measure at most `T^θ`.

At a typical height (`zetaTypicalHeight`: no zero with `Re ≥ ½ + η/4` within height `2`, and
`|ζ| ≤ T^ε` on `½ ≤ Re ≤ 2`, `|Im − t| ≤ 2`) the strip saddle method gives positivity at these
orders (`exists_xiSliceCoeff_pos_of_typical`). Both kinds of atypical heights are power-saving rare
(`exists_volume_not_zetaTypicalHeight_le_rpow`):

* **zero shadows** (`exists_volume_zetaZeroShadow_le_inghamHuxley`): each zero copy with
  `Re ≥ σ` and ordinate in `[T₀, 2T + 2]` shadows an interval of length `4`, and the cumulative
  Ingham–Huxley count bounds the copies by `(1 + log T)^B T^{(A(σ)+ε)(1−σ)}`, with
  `A(σ)(1 − σ) < 1`;
* **large values** (`exists_volume_zetaLargeNear_le_rpow`): the mean square over unit cells against
  the threshold `T^ε` gives measure `O(T^{1−ε})`.

So, off a set of heights of measure `T^θ`, the RH content of the slice route at height `t` lies in
the orders `k < η log t`, for every fixed `η > 0`; previously the exceptional set was only `o(T)`
(`eventually_volume_xiSliceCoeff_nonpos_le`).
-/

open Complex MeasureTheory Filter Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## Large values: power saving -/

/-- **Large values near the line are power-saving rare.** The heights `t ∈ [T, 2T]` near which `ζ`
exceeds `T^ε` on `½ ≤ Re ≤ 2`, `|Im − t| ≤ 2` have measure `O(T^{1−ε})`. -/
theorem exists_volume_zetaLargeNear_le_rpow {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 6 ≤ T →
      volume (zetaLargeNear T (T ^ ε)) ≤ ENNReal.ofReal (C * T ^ (1 - ε)) := by
  obtain ⟨C, hC, hA1⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨K, hK0, hχ⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow (d₀ := 1 / 4) (by norm_num) (by norm_num)
  set c₁ := 100 * C * (K ^ 2 + 1) * (1 + 12 / ε) ^ 3 with hc₁
  set c₂ := Real.pi * ε ^ 2 / 1024 with hc₂
  have hc₂0 : 0 < c₂ := by rw [hc₂]; have := Real.pi_pos; positivity
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; have := hC.le; positivity
  refine ⟨21 * c₁ / c₂, by positivity, fun T hT => ?_⟩
  obtain ⟨hu1, hr3, hlog, hM⟩ := zetaLargeNear_scale_bounds hε hε1 (by linarith : (1 : ℝ) ≤ T)
  set u := (4 * T) ^ (ε / 12) with hudef
  have hT0 : 0 < T := by linarith
  have hTε : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 ε
  have hvol := volume_zetaLargeNear_le hC hK0 (by positivity : 0 < ε / 4) (by linarith) hA1
    (fun d hd0 hd t => hχ d hd0 hd t) hT hTε
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA : 0 < Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2 := by
    have := Real.pi_pos; positivity
  rw [div_le_iff₀ hA, hr3]
  have hlog0 : 0 ≤ 1 + Real.log (4 * T) := by
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
  have hK' : (K * u ^ 3) ^ 2 + 1 ≤ (K ^ 2 + 1) * u ^ 6 := by
    have : 1 ≤ u ^ 6 := one_le_pow₀ hu1
    nlinarith [sq_nonneg K]
  have hL : (1 + Real.log (4 * T)) ^ 3 ≤ (1 + 12 / ε) ^ 3 * u ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hlog0 hlog 3
  have hQ : (4 * T + 2) ^ 2 * ((K * u ^ 3) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3)
      ≤ c₁ * T ^ 3 * u ^ 9 := by
    have h1 : (4 * T + 2) ^ 2 ≤ 25 * T ^ 2 := by nlinarith
    calc _ ≤ (25 * T ^ 2) * ((K ^ 2 + 1) * u ^ 6) * (4 * C * T * ((1 + 12 / ε) ^ 3 * u ^ 3)) := by
          gcongr
      _ = c₁ * T ^ 3 * u ^ 9 := by rw [hc₁]; ring
  have hAlow : c₂ * T ^ 2 * u ^ 24 ≤ Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2 := by
    have hM2 : (u ^ 12 / 4) ^ 2 ≤ (T ^ ε) ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
    calc c₂ * T ^ 2 * u ^ 24 = Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (u ^ 12 / 4) ^ 2 := by
          rw [hc₂]; ring
      _ ≤ _ := by gcongr
  -- `u^15 = (4T)^{5ε/4} ≥ T^ε`
  have hu15 : T ^ ε ≤ u ^ 15 := by
    have e : u ^ 15 = (4 * T) ^ (ε / 12 * 15) := by
      rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [e]
    calc T ^ ε ≤ (4 * T) ^ ε := Real.rpow_le_rpow hT0.le (by linarith) hε.le
      _ ≤ (4 * T) ^ (ε / 12 * 15) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hTsplit : T ^ (1 - ε) * T ^ ε = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have hu0 : 0 < u := by linarith
  calc 21 * ((4 * T + 2) ^ 2 * ((K * u ^ 3) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3))
      ≤ 21 * (c₁ * T ^ 3 * u ^ 9) := by gcongr
    _ = 21 * c₁ / c₂ * T ^ (1 - ε) * (T ^ ε * (c₂ * T ^ 2 * u ^ 9)) := by
        have e3 : T ^ 3 = T ^ (1 - ε) * T ^ ε * T ^ 2 := by rw [hTsplit]; ring
        rw [e3]; field_simp
    _ ≤ 21 * c₁ / c₂ * T ^ (1 - ε) * (u ^ 15 * (c₂ * T ^ 2 * u ^ 9)) := by gcongr
    _ = 21 * c₁ / c₂ * T ^ (1 - ε) * (c₂ * T ^ 2 * u ^ 24) := by ring
    _ ≤ 21 * c₁ / c₂ * T ^ (1 - ε) * (Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2) := by
        gcongr

/-! ## Zero shadows: power saving -/

/-- **Zero shadows at fixed distance are power-saving rare.** For `½ < σ ≤ 1`, the heights
`t ∈ [T, 2T]` within `2` of a zero of `ζ` with `Re ≥ σ` have measure
`O((1 + log T)^B T^{(A(σ)+ε)(1−σ)})`, with `A` the Ingham–Huxley exponent. -/
theorem exists_volume_zetaZeroShadow_le_inghamHuxley {σ ε : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ, ∃ T₁ : ℝ, 2 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent σ + ε) * (1 - σ))) := by
  classical
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ := exists_ncard_zeroCopyRange_le hσ hσ1 hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by
    have hA := (inghamHuxleyExponent_mem hσ).1
    rw [hE]; exact mul_nonneg (by linarith) (by linarith)
  have hEle : E ≤ 2 := by
    have hA := (inghamHuxleyExponent_mem hσ).2
    rw [hE]; nlinarith
  refine ⟨4 * (2 * D * 3 ^ (B + 1) * 9), by positivity, B + 1, T₀ + 2, by linarith,
    fun T hT => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  set Y : ℝ := 2 * T + 2 with hY
  have hfin := zeroCopyRange_finite σ T₀ Y hT₀0
  set F : Finset XiZeroCopy := hfin.toFinset with hF
  have hsub : zetaZeroShadow σ 2 ∩ Icc T (2 * T) ⊆
      ⋃ q ∈ F, Icc (((q.1 : ℂ)).im - 2) (((q.1 : ℂ)).im + 2) := by
    rintro t ⟨⟨w, hw0, hwre, hwim⟩, htT⟩
    have hxi : xi w = 0 := by
      rcases riemannZeta_eq_zero_iff_xi_or_trivial.mp hw0 with h | ⟨n, rfl⟩
      · exact h
      · exfalso
        have : (-(2 * ((n : ℂ) + 1))).re = -(2 * ((n : ℝ) + 1)) := by simp
        rw [this] at hwre
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have habs := abs_le.mp hwim
    refine mem_iUnion₂.mpr ⟨q, hfin.mem_toFinset.mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hq]; exact hwre
    · rw [hq]; linarith [htT.1]
    · rw [hq, hY]; linarith [htT.2]
    · rw [hq]; linarith
    · rw [hq]; linarith
  have hvol : volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ≤ 4 * F.card := by
    calc volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T))
        ≤ volume (⋃ q ∈ F, Icc (((q.1 : ℂ)).im - 2) (((q.1 : ℂ)).im + 2)) := measure_mono hsub
      _ ≤ ∑ q ∈ F, volume (Icc (((q.1 : ℂ)).im - 2) (((q.1 : ℂ)).im + 2)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ _q ∈ F, (4 : ENNReal) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Real.volume_Icc]; norm_num
      _ = 4 * F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : (F.card : ℝ) = (zeroCopyRange σ T₀ Y).ncard := by
    rw [hF, Set.ncard_eq_toFinset_card _ hfin]
  have hYT : T₀ ≤ Y := by rw [hY]; linarith
  have hYpos : (0 : ℝ) < Y := by rw [hY]; linarith
  have hlogY : 1 + Real.log Y ≤ 3 * (1 + Real.log T) := by
    have h3T : Y ≤ 3 * T := by rw [hY]; linarith
    have := Real.log_le_log hYpos h3T
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    have := Real.log_nonneg hT1
    linarith
  have hpowY : Y ^ E ≤ 9 * T ^ E := by
    calc Y ^ E ≤ (3 * T) ^ E := Real.rpow_le_rpow hYpos.le (by rw [hY]; linarith) hE0
      _ = 3 ^ E * T ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 9 * T ^ E := by
          gcongr
          calc (3 : ℝ) ^ E ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEle
            _ = 9 := by norm_num
  have hlogY0 : 0 ≤ 1 + Real.log Y := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Y by rw [hY]; linarith); linarith
  have hreal : 4 * (F.card : ℝ) ≤
      4 * (2 * D * 3 ^ (B + 1) * 9) * (1 + Real.log T) ^ (B + 1) * T ^ E := by
    rw [hcard]
    have h := hcount Y hYT
    calc 4 * ((zeroCopyRange σ T₀ Y).ncard : ℝ)
        ≤ 4 * (2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E) := by linarith
      _ ≤ 4 * (2 * D * (3 * (1 + Real.log T)) ^ (B + 1) * (9 * T ^ E)) := by
          have hlT : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
          gcongr
      _ = 4 * (2 * D * 3 ^ (B + 1) * 9) * (1 + Real.log T) ^ (B + 1) * T ^ E := by
          rw [mul_pow]; ring
  calc volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ≤ 4 * F.card := hvol
    _ = ENNReal.ofReal (4 * (F.card : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]; norm_num
    _ ≤ ENNReal.ofReal (4 * (2 * D * 3 ^ (B + 1) * 9) * (1 + Real.log T) ^ (B + 1) * T ^ E) :=
        ENNReal.ofReal_le_ofReal hreal

/-! ## Typical heights: power saving -/

/-- **Atypical heights are power-saving rare.** For `0 < η ≤ 2` and `0 < ε ≤ 1` there is `θ < 1`
such that for large `T` the heights `t ∈ [T, 2T]` that are not typical (a zero with
`Re ≥ ½ + η/4` within height `2`, or `|ζ| > T^ε` on `½ ≤ Re ≤ 2`, `|Im − t| ≤ 2`) have measure
at most `T^θ`. -/
theorem exists_volume_not_zetaTypicalHeight_le_rpow {η ε : ℝ} (hη : 0 < η) (hη2 : η ≤ 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ≤
        ENNReal.ofReal (T ^ θ) := by
  set σ : ℝ := 1 / 2 + η / 4 with hσdef
  have hσ : 1 / 2 < σ := by rw [hσdef]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ]
  set ε' : ℝ := min 1 g with hε'
  have hε'0 : 0 < ε' := lt_min one_pos hg0
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  obtain ⟨C₁, hC₁, B, T₁, hT₁, hshadow⟩ :=
    exists_volume_zetaZeroShadow_le_inghamHuxley hσ hσ1 hε'0 hε'1
  obtain ⟨C₂, hC₂, hlarge⟩ := exists_volume_zetaLargeNear_le_rpow hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε') * (1 - σ) with hE
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε' ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ 1 - σ := by linarith
    rw [hE]
    have : ε' * (1 - σ) ≤ g / 2 := by nlinarith
    nlinarith
  set d : ℝ := min (g / 2) ε with hd
  have hd0 : 0 < d := lt_min (by linarith) hε
  have hdg : d ≤ g / 2 := min_le_left _ _
  have hdε : d ≤ ε := min_le_right _ _
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := d / 2) (by positivity) (C₁ + C₂))
  refine ⟨1 - d / 2, by linarith, max (max T₁ T₂) 6, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT6 : 6 ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := by linarith
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ⊆
      (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ∪ zetaLargeNear T (T ^ ε) := by
    rintro t ⟨ht, hnt⟩
    by_contra hno
    simp only [mem_union, mem_inter_iff, not_or, not_and] at hno
    exact hnt ⟨ht, fun hs => hno.1 hs ht, hno.2⟩
  have hlog0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hpoly1 : 1 ≤ (1 + Real.log T) ^ B := one_le_pow₀ (by linarith [Real.log_nonneg hT1])
  have hTE : T ^ E ≤ T ^ (1 - d) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTε : T ^ (1 - ε) ≤ T ^ (1 - d) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hsum : C₁ * (1 + Real.log T) ^ B * T ^ E + C₂ * T ^ (1 - ε) ≤ T ^ (1 - d / 2) := by
    have hTd : 0 ≤ T ^ (1 - d) := by positivity
    have h1 : C₁ * (1 + Real.log T) ^ B * T ^ E ≤ C₁ * (1 + Real.log T) ^ B * T ^ (1 - d) := by
      gcongr
    have h2 : C₂ * T ^ (1 - ε) ≤ C₂ * (1 + Real.log T) ^ B * T ^ (1 - d) := by
      calc C₂ * T ^ (1 - ε) ≤ C₂ * T ^ (1 - d) := by gcongr
        _ = C₂ * 1 * T ^ (1 - d) := by ring
        _ ≤ C₂ * (1 + Real.log T) ^ B * T ^ (1 - d) := by gcongr
    have h3 : (C₁ + C₂) * (1 + Real.log T) ^ B * T ^ (1 - d) ≤ T ^ (d / 2) * T ^ (1 - d) := by
      gcongr; exact hT₂ T hTT₂
    have h4 : T ^ (d / 2) * T ^ (1 - d) = T ^ (1 - d / 2) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    nlinarith
  calc volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t}
      ≤ volume ((zetaZeroShadow σ 2 ∩ Icc T (2 * T)) ∪ zetaLargeNear T (T ^ ε)) := measure_mono hsub
    _ ≤ volume (zetaZeroShadow σ 2 ∩ Icc T (2 * T)) + volume (zetaLargeNear T (T ^ ε)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * (1 + Real.log T) ^ B * T ^ E) + ENNReal.ofReal (C₂ * T ^ (1 - ε)) :=
        add_le_add (hshadow T hTT₁) (hlarge T hT6)
    _ = ENNReal.ofReal (C₁ * (1 + Real.log T) ^ B * T ^ E + C₂ * T ^ (1 - ε)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (T ^ (1 - d / 2)) := ENNReal.ofReal_le_ofReal hsum

/-! ## Slice positivity at fixed-ratio orders -/

/-- **Slice positivity at orders `≥ η log t` off a power-saving set of heights.** For every
`η > 0` there is `θ < 1` such that for large `T`, the heights `t ∈ [T, 2T]` at which `c_{2k}(t)` fails
to be positive for some order `k ≥ η log t` have measure at most `T^θ`. -/
theorem exists_volume_xiSliceCoeff_nonpos_le_rpow {η : ℝ} (hη : 0 < η) :
    ∃ θ : ℝ, θ < 1 ∧ ∀ᶠ T : ℝ in atTop,
      volume {t : ℝ | t ∈ Icc T (2 * T) ∧
        ∃ k : ℕ, η * Real.log t ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤ ENNReal.ofReal (T ^ θ) := by
  set η' := min (η / 2) (1 / 8) with hη'def
  have hη'0 : 0 < η' := lt_min (by linarith) (by norm_num)
  have hη'8 : η' ≤ 1 / 8 := min_le_right _ _
  have hη'η : 2 * η' ≤ η := by have := min_le_left (η / 2) (1 / 8); linarith
  have hε0 : 0 < η' ^ 4 / 10 ^ 8 := by positivity
  have hε1 : η' ^ 4 / 10 ^ 8 ≤ 1 := by
    have : η' ^ 4 ≤ 1 := pow_le_one₀ hη'0.le (by linarith)
    rw [div_le_one (by norm_num)]; linarith
  obtain ⟨θ, hθ, T₃, hvol⟩ :=
    exists_volume_not_zetaTypicalHeight_le_rpow hη'0 (by linarith) hε0 hε1
  obtain ⟨T₀, -, hpos⟩ := exists_xiSliceCoeff_pos_of_typical hη'0 hη'8
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop T₃, Filter.eventually_ge_atTop T₀,
    Filter.eventually_ge_atTop (Real.exp (2 * |K₁|)), Filter.eventually_ge_atTop 1]
    with T hT₃ hT₀ hTK hT1
  refine le_trans (measure_mono ?_) (hvol T hT₃)
  rintro t ⟨ht, k, hk, hneg⟩
  refine ⟨ht, fun htyp => hneg ?_⟩
  have hTt : T ≤ t := ht.1
  have hlogt : 2 * |K₁| ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) (le_trans hTK hTt)
    rwa [Real.log_exp] at h
  have hlog0 : 0 ≤ Real.log t := by linarith [abs_nonneg K₁]
  rcases le_or_gt (k : ℝ) (Real.log t / 2) with hkhi | hkhi
  · refine hpos T t hT₀ htyp k ?_ hkhi
    have := mul_le_mul_of_nonneg_right hη'η hlog0
    linarith
  · refine hK₁ t (by linarith) k (max_le ?_ ?_)
    · linarith [le_abs_self K₁]
    · linarith

end

end RHTower
