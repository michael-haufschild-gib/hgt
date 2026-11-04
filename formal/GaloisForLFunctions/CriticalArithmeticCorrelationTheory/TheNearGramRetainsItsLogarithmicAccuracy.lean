import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramRetainsOnlyThePolarConductor

/-!
# The near Gram retains its logarithmic accuracy

The shell approximation remains valid after multiplying its relative
error by log c. A squared logarithmic horizon budget pays the finite
horizon error; the signed shell remainder costs only O((1 + log c)/c).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A squared logarithmic horizon budget also pays a single logarithm. -/
theorem tendsto_fourth_overlap_log_error_of_sq {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => by
    have := Real.log_natCast_nonneg N
    positivity) _ he
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  change 1 ≤ Real.log (N : ℝ) at hL
  have hLL : Real.log N ≤ Real.log N ^ 2 := by nlinarith only [hL]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLL (pow_nonneg (zero_le_one.trans (hc N)) 4)) (Nat.cast_nonneg N)

/-- The fourth-order horizon budget forces the physical width to vanish. -/
theorem tendsto_overlap_width_of_fourth_log_error {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (zero_le_one.trans (hc N)) (Nat.cast_nonneg N)) _ he
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  have h14 : c N ≤ c N ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (hc N) (by norm_num : 1 ≤ 4)
  exact div_le_div_of_nonneg_right
    (h14.trans (le_mul_of_one_le_right (by positivity) hL)) (Nat.cast_nonneg N)

private theorem eventually_overlap_le_horizon {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, c N ≤ N := by
  have hw := tendsto_overlap_width_of_fourth_log_error hc he
  filter_upwards [eventually_ge_atTop 1,
    hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_one hN0).mp h.le

private theorem tendsto_log_mul_shell_relative_error {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun c : ℝ => Real.log c * (shellCorrection φ c m / c -
      (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0))) atTop (𝓝 0) := by
  let K : ℝ := |shellReferenceConstant φ m| + completedConductorEnergy φ 1 m
  have hlog : Tendsto (fun c : ℝ => Real.log c / c) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog2 : Tendsto (fun c : ℝ => Real.log c ^ 2 / c) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hlim := hlog2.add (hlog.mul_const K)
  simp only [zero_mul, zero_add] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg hc
  have heq : shellCorrection φ c m / c -
      (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) =
      (shellCorrection φ c m -
        (if m = 1 then c * ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) else 0)) / c := by
    split_ifs <;> (field_simp [hc0.ne'] <;> ring)
  rw [Real.norm_eq_abs, heq, abs_mul, abs_of_nonneg hlog0, abs_div, abs_of_pos hc0]
  exact (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (abs_shellCorrection_sub_polar_le hφ hsupp hM hc hm) hc0.le)
    hlog0).trans_eq (by dsimp only [K]; ring)

/-- The near-Gram approximation remains valid after multiplication by the overlap logarithm. -/
theorem tendsto_log_mul_fixedWidthNearGram_relative_error {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (fixedWidthNearGram φ (c N / N) N m l / c N -
        (if m = 1 ∧ l = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0)))
      atTop (𝓝 0) := by
  have he1 := tendsto_fourth_overlap_log_error_of_sq hc he
  obtain ⟨C, hC, herr⟩ := exists_fixedWidthNearGram_shell_error hφ hsupp hM
  have hlim := he.const_mul (C * ((m : ℝ) * l) ^ 5)
  simp only [mul_zero] at hlim
  have hz : Tendsto (fun N : ℕ => Real.log (c N) *
      ((fixedWidthNearGram φ (c N / N) N m l -
        (if m = l then shellCorrection φ (c N) m else 0)) / c N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_nearGram_admissible hc he1 m l,
      eventually_overlap_le_horizon hc he1] with N hN hcN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hlogc : 0 ≤ Real.log (c N) := Real.log_nonneg (hc N)
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hlogle : Real.log (c N) ≤ Real.log N := Real.log_le_log hc0 hcN
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlogc, abs_div, abs_of_pos hc0]
    calc
      _ ≤ Real.log (c N) *
          ((C * ((m : ℝ) * l) ^ 5 * (c N ^ 5 * Real.log N / N)) / c N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (herr hm hl hN.1 hN.2.1 (hc N) hN.2.2) hc0.le) hlogc
      _ = (C * ((m : ℝ) * l) ^ 5) *
          (c N ^ 4 * Real.log N * Real.log (c N) / N) := by
        field_simp [hc0.ne']
      _ ≤ (C * ((m : ℝ) * l) ^ 5) * (c N ^ 4 * Real.log N ^ 2 / N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        have h := mul_le_mul_of_nonneg_left hlogle
          (mul_nonneg (pow_nonneg hc0.le 4) hlogN)
        simpa only [pow_two, mul_assoc] using h
  by_cases hml : m = l
  · subst l
    have hs := (tendsto_log_mul_shell_relative_error hφ hsupp hM hm).comp hcinf
    have h := hz.add hs
    simp only [zero_add, if_true, and_self] at h ⊢
    exact h.congr fun N => by dsimp only [Function.comp_def]; ring
  · have hnot : ¬(m = 1 ∧ l = 1) := by rintro ⟨rfl, rfl⟩; exact hml rfl
    simpa only [if_neg hml, if_neg hnot, sub_zero] using hz

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_log_mul_fixedWidthNearGram_relative_error
