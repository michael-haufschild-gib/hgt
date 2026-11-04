import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLogarithmicRowIsAnIntegralOfHorizons
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheGrowingShellCorrectionIsPolar

/-!
# The linear part of the near-Gram is polar

The exact shell identity and the finite arithmetic near-Gram estimate
leave a single linear conductor mean. The relative error is uniform
over every admissible subhorizon at fixed physical width.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory

/-- The raw near-Gram has the same signed shell mean before horizon normalization. -/
theorem exists_fixedWidthNearGram_shell_error {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m l N : ℕ} {c : ℝ},
      0 < m → 0 < l → max 2 (max m l) * max 2 (max m l) ≤ N →
      18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N →
      1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      |fixedWidthNearGram φ (c / N) N m l - (if m = l then shellCorrection φ c m else 0)| ≤
        C * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
  obtain ⟨C, hC, hng⟩ := exists_nearGram_mode_bilinear_approx hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro m l N c hm hl hQ hlog hc hrad
  have hL : 0 < Real.log N := by
    have := Real.log_natCast_nonneg (max 2 (max m l))
    linarith only [hlog, this]
  have hb := mul_le_mul_of_nonneg_left (hng hm hl hQ hlog hc hrad) hL.le
  rw [← log_mul_nearGramModeBilin_eq_fixedWidth φ c hL]
  calc
    _ = |Real.log N * (nearGramModeBilin φ c N m l -
        (if m = l then shellCorrection φ c m / Real.log N else 0))| := by
      congr 1
      split_ifs <;> field_simp [hL.ne'] <;> ring
    _ = Real.log N * |nearGramModeBilin φ c N m l -
        (if m = l then shellCorrection φ c m / Real.log N else 0)| := by
      rw [abs_mul, abs_of_pos hL]
    _ ≤ _ := hb.trans_eq (by ring)

/-- The quadratic radius budget vanishes under the fourth-order horizon error. -/
theorem eventually_nearGram_radius_budget {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, 4 * (2 * Real.exp 2 + 1) ^ 2 * c N ^ 2 ≤ N := by
  let D : ℝ := 4 * (2 * Real.exp 2 + 1) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlim : Tendsto (fun N : ℕ => D * (c N ^ 4 * Real.log N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul D
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop 1,
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)] with N hL hN hb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 ≤ c N := (zero_le_one.trans (hc N))
  have h24 : c N ^ 2 ≤ c N ^ 4 := pow_le_pow_right₀ (hc N) (by norm_num)
  have h4L : c N ^ 4 ≤ c N ^ 4 * Real.log N :=
    le_mul_of_one_le_right (pow_nonneg hc0 _) hL
  have hnum : D * (c N ^ 4 * Real.log N) ≤ N := by
    rw [← mul_div_assoc, div_le_one hN0] at hb
    exact hb
  exact (mul_le_mul_of_nonneg_left (h24.trans h4L) hD).trans hnum

/-- A vanishing fourth-order horizon error makes every fixed conductor pair admissible. -/
theorem eventually_nearGram_admissible {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) (m l : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      max 2 (max m l) * max 2 (max m l) ≤ N ∧
      18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N ∧
      4 * (linearNearRowRadius (c N) + 1) ^ 2 ≤ N := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 2 (max m l) * max 2 (max m l)),
    hlog.eventually_ge_atTop (18 * (1 + Real.log (max 2 (max m l) : ℕ))),
    eventually_nearGram_radius_budget hc he] with N hQ hlogQ hb
  refine ⟨hQ, hlogQ, ?_⟩
  have hc0 : 0 ≤ c N := zero_le_one.trans (hc N)
  have hr : linearNearRowRadius (c N) + 1 ≤ (2 * Real.exp 2 + 1) * c N := by
    unfold linearNearRowRadius
    nlinarith only [hc N]
  have hrad0 : 0 ≤ linearNearRowRadius (c N) + 1 := by
    unfold linearNearRowRadius
    positivity
  have h2 : 4 * (linearNearRowRadius (c N) + 1) ^ 2 ≤
      4 * (2 * Real.exp 2 + 1) ^ 2 * c N ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrad0 hr 2) (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [mul_pow, mul_assoc] using h
  exact h2.trans hb

/-- On growing overlap, only the conductor-one near-Gram retains a linear term. -/
theorem tendsto_fixedWidthNearGram_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => fixedWidthNearGram φ (c N / N) N m l / c N) atTop
      (𝓝 (if m = l then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0)) := by
  obtain ⟨C, hC, herr⟩ := exists_fixedWidthNearGram_shell_error hφ hsupp hM
  have hlim : Tendsto (fun N : ℕ => C * ((m : ℝ) * l) ^ 5 *
      (c N ^ 4 * Real.log N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (C * ((m : ℝ) * l) ^ 5)
  have hz : Tendsto (fun N : ℕ =>
      (fixedWidthNearGram φ (c N / N) N m l -
        (if m = l then shellCorrection φ (c N) m else 0)) / c N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_nearGram_admissible hc he m l] with N hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0]
    calc
      _ ≤ (C * ((m : ℝ) * l) ^ 5 * (c N ^ 5 * Real.log N / N)) / c N :=
        div_le_div_of_nonneg_right (herr hm hl hN.1 hN.2.1 (hc N) hN.2.2) hc0.le
      _ = _ := by field_simp [hc0.ne']
  have hs := (tendsto_shellCorrection_div_overlap hφ hsupp hM hm).comp hcinf
  by_cases hml : m = l
  · simp only [if_pos hml] at hz ⊢
    have h := hz.add hs
    simp only [zero_add] at h
    exact h.congr fun N => by dsimp only [Function.comp_apply]; ring
  · simp only [if_neg hml, sub_zero] at hz ⊢
    exact hz

/-- The relative near-Gram error has one common bound on every smaller admissible horizon. -/
theorem exists_fixedWidthNearGram_subhorizon_error {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m l N T : ℕ} {c : ℝ},
      0 < m → 0 < l → 0 < c → 2 ≤ T → T ≤ N →
      max 2 (max m l) * max 2 (max m l) ≤ T →
      18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log T →
      1 ≤ c * T / N → 4 * (linearNearRowRadius (c * T / N) + 1) ^ 2 ≤ T →
      |fixedWidthNearGram φ (c / N) T m l / (c * T / N) -
        (if m = l then shellCorrection φ (c * T / N) m / (c * T / N) else 0)| ≤
        C * ((m : ℝ) * l) ^ 5 * (c ^ 4 * Real.log N / N) := by
  obtain ⟨C, hC, herr⟩ := exists_fixedWidthNearGram_shell_error hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro m l N T c hm hl hc hT hTN hQ hlog hu hrad
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hTN' : (T : ℝ) ≤ N := by exact_mod_cast hTN
  have hN0 : (0 : ℝ) < N := hT0.trans_le hTN'
  let u : ℝ := c * T / N
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have huc : u ≤ c := (div_le_iff₀ hN0).mpr (mul_le_mul_of_nonneg_left hTN' hc.le)
  have hwidth : u / T = c / N := by dsimp [u]; field_simp [hT0.ne', hN0.ne']
  have hb := herr hm hl hQ hlog hu hrad
  change |fixedWidthNearGram φ (u / T) T m l -
      (if m = l then shellCorrection φ u m else 0)| ≤
    C * ((m : ℝ) * l) ^ 5 * (u ^ 5 * Real.log T / T) at hb
  rw [hwidth] at hb
  have herr' : |fixedWidthNearGram φ (c / N) T m l / u -
      (if m = l then shellCorrection φ u m / u else 0)| ≤
      C * ((m : ℝ) * l) ^ 5 * (u ^ 4 * Real.log T / T) := by
    have h := div_le_div_of_nonneg_right hb hu0.le
    have hleft : |fixedWidthNearGram φ (c / N) T m l / u -
        (if m = l then shellCorrection φ u m / u else 0)| =
        |fixedWidthNearGram φ (c / N) T m l -
          (if m = l then shellCorrection φ u m else 0)| / u := by
      calc
        _ = |(fixedWidthNearGram φ (c / N) T m l -
            (if m = l then shellCorrection φ u m else 0)) / u| := by
          congr 1
          split_ifs <;> ring
        _ = _ := by rw [abs_div, abs_of_pos hu0]
    rw [hleft]
    exact h.trans_eq (by field_simp [hu0.ne'])
  have hscale : u ^ 4 * Real.log T / T ≤ c ^ 4 * Real.log N / N := by
    calc
      _ = (c / N) * u ^ 3 * Real.log T := by
        dsimp [u]
        field_simp [hT0.ne', hN0.ne']
      _ ≤ (c / N) * c ^ 3 * Real.log N :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0.le huc 3)
            (div_nonneg hc.le hN0.le))
          (Real.log_le_log hT0 hTN') (Real.log_natCast_nonneg T) (by positivity)
      _ = _ := by ring
  exact herr'.trans (mul_le_mul_of_nonneg_left hscale (by positivity))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_fixedWidthNearGram_div_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_fixedWidthNearGram_subhorizon_error
