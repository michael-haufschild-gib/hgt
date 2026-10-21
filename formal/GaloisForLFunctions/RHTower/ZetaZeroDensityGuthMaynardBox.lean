import GaloisForLFunctions.RHTower.ZetaZeroDensityGuthMaynardClassCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley

/-!
# Guth–Maynard's zero-density estimate at a fixed `σ ∈ [7/10, 8/10]`

Guth–Maynard, Theorem 1.2: `N(σ, T) ≤ T^{15(1-σ)/(3+5σ) + o(1)}`.  In the height-box form: under
the large values estimate `GuthMaynardLargeValuesBound`, for every `σ ∈ [7/10, 8/10]` and
`ε > 0` there are `D, T₀` with

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^{12} T^{15(1-σ)/(3+5σ) + ε}`   (`T ≥ T₀`),

counting zeros with multiplicity (`exists_zeroHeightBox_ncard_le_gm`).

The zero detector runs with the window `a = 10/(6 + 10σ)` (ratio `3/2`, the range (13.1) of the
paper), smoothing `T^{3a/4}` and mollifier `T^{1/64}`.  A separated class is either of Type I,
counted by `exists_gm_window_class_card_le` with the switching exponent
`α = 15(1-σ)/((3+5σ)(18/5-4σ))`, or of Type II, counted by the critical fourth moment
(`card_typeTwo_le_window`), whose exponent `1 + 4/64 + (3a/4)(2 - 4σ)` stays below the target
because `E₀ - 1 - (3a/4)(2 - 4σ) = (9 - 10σ)/(6 + 10σ) ≥ 1/14`.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve RHTower.GuthMaynard

/-- **Guth–Maynard's zero-density estimate at a fixed `σ ∈ [7/10, 8/10]`.**  Under the large
values estimate, for every `ε > 0` the height box `σ ≤ Re ρ`, `T ≤ Im ρ ≤ 2T` holds at most
`D (1 + log T)^{12} T^{15(1-σ)/(3+5σ) + ε}` zero copies for all large `T`. -/
theorem exists_zeroHeightBox_ncard_le_gm (hGM : GuthMaynardLargeValuesBound) {σ ε : ℝ}
    (hσ0 : 7 / 10 ≤ σ) (hσ1 : σ ≤ 8 / 10) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ 12 * T ^ (gmDensityExponent σ + ε) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = gmWindowExponent σ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = gmDensityExponent σ + ε := ⟨_, rfl⟩
  rw [← hE]
  have hσ0' : (0 : ℝ) ≤ σ := by linarith
  have ha0 : 0 < a := ha ▸ gmWindowExponent_pos hσ0'
  have ha1 : a ≤ 1 := ha ▸ gmWindowExponent_le_one (by linarith)
  have hδ0 : (0 : ℝ) < 1 / 64 := by norm_num
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈2 * a / (1 / 64)⌉₊ + 2 := ⟨_, rfl⟩
  have hM : 2 * a / (1 / 64) ≤ M := by
    rw [hMdef]; push_cast; linarith [Nat.le_ceil (2 * a / (1 / 64))]
  have hM2 : 2 ≤ M := by rw [hMdef]; omega
  -- the four exponents of the class count and the Type II exponent
  have hd : 3 * a * (1 - σ) ≤ gmDensityExponent σ :=
    (ha ▸ three_mul_gmWindowExponent_mul hσ0').le
  have hg2 : gmSwitchExponent σ * (18 / 5 - 4 * σ) ≤ gmDensityExponent σ :=
    (gmSwitchExponent_mul hσ0' (by linarith)).le
  have hg3 : 1 + a * (12 / 5 - 4 * σ) ≤ gmDensityExponent σ :=
    (ha ▸ one_add_gmWindowExponent_mul hσ0').le
  have hm : 1 + gmSwitchExponent σ * (1 - 2 * σ) ≤ gmDensityExponent σ :=
    one_add_gmSwitchExponent_mul_le hσ0' (by linarith)
  have hII : 1 + 4 * (1 / 64) + 3 * a / 4 * (2 - 4 * σ) ≤ E := by
    have h := typeTwo_le_gmDensityExponent hσ0' (by linarith) (δ := 1 / 64) le_rfl
    rw [← ha] at h
    linarith
  have hy0 : 0 < 3 * a / 4 := by positivity
  obtain ⟨K₀, c₀, T₁, hc₀, hK₀, hT₁, hdich⟩ :=
    exists_pDetector_dichotomy_of_gap hδ0 (by norm_num) hy0 (by linarith) (by linarith : 1 / 2 < σ)
  obtain ⟨K, hK, T₂, hcls⟩ := exists_gm_window_class_card_le hGM ha0 ha1 hδ0 hM hM2
    (by linarith) (by linarith) hε hd hg2 hg3 hm
  rw [← hE] at hcls
  obtain ⟨D₄, hD₄, h4⟩ := exists_integral_norm_riemannZeta_half_pow_four_le
  have hev : ∀ᶠ T : ℝ in atTop, T₁ ≤ T ∧ T₂ ≤ T ∧ 4 ≤ T ∧
      1 * (1 + Real.log T) ^ 2 ≤ T ^ (1 / 4 : ℝ) ∧ K₀ * (1 + Real.log T) ^ 1 ≤ T ^ (1 : ℝ) ∧
      2 ≤ T ^ (3 * a / 4) := by
    filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop T₂, eventually_ge_atTop (4 : ℝ),
      eventually_const_mul_polylog_le_rpow 2 (c := 1 / 4) (by norm_num) 1,
      eventually_const_mul_polylog_le_rpow 1 (c := 1) (by norm_num) K₀,
      (tendsto_rpow_atTop hy0).eventually_ge_atTop 2] with T h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp hev
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : ℝ, F₀ = 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 := ⟨_, rfl⟩
  have hF₀0 : 0 ≤ F₀ := by rw [hF₀]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨F₀ * (K + K₂), by positivity, max T₃ 4, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T hT
  obtain ⟨hTT₁, hTT₂, hT4, hTA, hTK, hTY⟩ := hT₃ T (le_trans (le_max_left _ _) hT)
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hTA' : Real.log T ^ 2 ≤ T ^ (1 / 4 : ℝ) := by
    rw [one_mul] at hTA
    exact le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) hTA
  have hZT : T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T := by
    calc T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T ^ (3 / 4 : ℝ) * T ^ (1 / 4 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hTA' (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hLT : K₀ * Real.log T ≤ T := by
    simp only [pow_one, Real.rpow_one] at hTK
    nlinarith only [hTK, hK₀]
  set Zc := pDetCut (3 * a / 4) T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 := Nat.floor_le (by positivity)
  have hZ2 : 2 ≤ Zc := by
    have h2 : (2 : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 :=
      le_trans hTY (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast h2)
  have hZTR : (Zc : ℝ) ≤ T := le_trans hZle hZT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log T := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hX1 : 1 ≤ pDetMoll (1 / 64) T := one_le_pDetMoll hδ0.le hT1
  have hY1 : 1 ≤ pDetSmooth (3 * a / 4) T := one_le_pDetSmooth hy0.le hT1
  obtain ⟨W, hWT, hWsep, hcase, hcount⟩ :=
    exists_separated_gDet_class (hdich T hTT₁) hc₀ hX1 hY1 hZ2 hT0 le_rfl (by linarith)
  have hpre := gDet_prefactor_le hT1 hZ2 hZTR
  rw [← hℓ, ← hF₀] at hpre
  have hTE : 0 ≤ T ^ E := Real.rpow_nonneg hT0.le _
  have hℓ8 : 1 ≤ ℓ ^ 8 := one_le_pow₀ hℓ1
  have hWcard : (W.card : ℝ) ≤ (K + K₂) * ℓ ^ 8 * T ^ E := by
    rcases hcase with h2 | ⟨j, -, i, -, m, -, h1⟩
    · -- Type II: the critical fourth moment
      have hc := card_typeTwo_le_window hK₀ hc₀ hD₄ hδ0.le hy0.le (by linarith) hLT hII
        (h4 (by linarith)) hWT hWsep h2
      rw [← hℓ, ← hK₂] at hc
      calc (W.card : ℝ) ≤ K₂ * ℓ ^ 8 * T ^ E := hc
        _ ≤ (K + K₂) * ℓ ^ 8 * T ^ E := by gcongr; linarith
    · -- Type I: the Guth–Maynard class count
      have hΛ0 : 0 ≤ gDetLog Zc := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zc))
      have hσσ' : σ ≤ σ + m / gDetLog Zc :=
        le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
      have hc := hcls T hTT₂ j i _ hσσ' W hWT hWsep h1
      calc (W.card : ℝ) ≤ K * T ^ E := hc
        _ ≤ (K + K₂) * ℓ ^ 8 * T ^ E := by
            have hKK : K ≤ (K + K₂) * ℓ ^ 8 :=
              le_trans (by linarith) (le_mul_of_one_le_right (by linarith) hℓ8)
            exact mul_le_mul_of_nonneg_right hKK hTE
  calc ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((gDetBlockCount Zc * (gDetBlockCount Zc + 8) * (⌊gDetLog Zc⌋₊ + 1) + 1 : ℕ) : ℝ) *
          densityWindowCapacity T * W.card := hcount
    _ ≤ (F₀ * ℓ ^ 4) * ((K + K₂) * ℓ ^ 8 * T ^ E) :=
        mul_le_mul hpre hWcard (Nat.cast_nonneg _) (by positivity)
    _ = F₀ * (K + K₂) * (1 + Real.log T) ^ 12 * T ^ E := by rw [hℓ]; ring

end RHTower

end
