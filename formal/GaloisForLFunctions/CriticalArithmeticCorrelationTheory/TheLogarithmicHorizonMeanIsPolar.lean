import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramRetainsOnlyThePolarConductor

/-!
# The logarithmic horizon mean is polar

A fixed shell threshold removes a vanishing-density prefix of horizons.
The remaining near-Grams have a common relative error and converge to the
conductor-one mean. Exact horizon integration transfers that mean to the
receiving-index logarithmic row.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory HTGeometry

private theorem tendsto_overlap_div_horizon {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (by linarith [hc N])
    (Nat.cast_nonneg N)) _ he
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  have h14 : c N ≤ c N ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (hc N) (by norm_num : 1 ≤ 4)
  exact div_le_div_of_nonneg_right
    (h14.trans (le_mul_of_one_le_right (by positivity) hL)) (Nat.cast_nonneg N)

private theorem tendsto_horizon_threshold_density {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) (B : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    Tendsto (fun N : ℕ => ((max B ⌈U * N / c N⌉₊ : ℕ) : ℝ) / N) atTop (𝓝 0) := by
  have hUlim : Tendsto (fun N : ℕ => U / c N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hcinf).const_mul U
  have hlim : Tendsto (fun N : ℕ => (B : ℝ) / N + U / c N + 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero] using
      ((tendsto_const_div_atTop_nhds_zero_nat (B : ℝ)).add hUlim).add
        tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have harg : 0 ≤ U * N / c N := by positivity
  have hceil := (Nat.ceil_lt_add_one harg).le
  have hmax : ((max B ⌈U * N / c N⌉₊ : ℕ) : ℝ) ≤ B + U * N / c N + 1 := by
    rw [Nat.cast_max]
    apply max_le
    · linarith only [harg]
    · linarith only [hceil, Nat.cast_nonneg (α := ℝ) B]
  calc
    _ ≤ ((B : ℝ) + U * N / c N + 1) / N := div_le_div_of_nonneg_right hmax hN0.le
    _ = _ := by field_simp [hN0.ne', hc0.ne']

private theorem near_radius_le_subhorizon {c : ℝ} (hc : 0 < c) {N T : ℕ}
    (hT : 1 ≤ T) (hTN : T ≤ N) (hu : 1 ≤ c * T / N)
    (hbudget : 4 * (2 * Real.exp 2 + 1) ^ 2 * c ^ 2 ≤ N) :
    4 * (linearNearRowRadius (c * T / N) + 1) ^ 2 ≤ T := by
  let u : ℝ := c * T / N
  let D : ℝ := 4 * (2 * Real.exp 2 + 1) ^ 2
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTN' : (T : ℝ) ≤ N := by exact_mod_cast hTN
  have hN0 : (0 : ℝ) < N := hT0.trans_le hTN'
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hrad : linearNearRowRadius u + 1 ≤ (2 * Real.exp 2 + 1) * u := by
    unfold linearNearRowRadius
    nlinarith only [hu]
  have hrad0 : 0 ≤ linearNearRowRadius u + 1 := by unfold linearNearRowRadius; positivity
  have hfrac : D * c ^ 2 / N ≤ 1 := (div_le_one hN0).mpr hbudget
  have htfrac : (T : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hTN'
  calc
    _ ≤ D * u ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrad0 hrad 2) (by norm_num : (0 : ℝ) ≤ 4)
      simpa only [mul_pow, D, mul_assoc] using h
    _ = (D * c ^ 2 / N * ((T : ℝ) / N)) * T := by dsimp [u]; ring
    _ ≤ 1 * T := mul_le_mul_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul hfrac htfrac (by positivity) zero_le_one) hT0.le
    _ = T := one_mul _

private theorem log_horizon_weight_bounds (T : ℕ) :
    0 ≤ (T : ℝ) * (Real.log ((T : ℝ) + 1) - Real.log T) ∧
      (T : ℝ) * (Real.log ((T : ℝ) + 1) - Real.log T) ≤ 1 := by
  by_cases hT : T = 0
  · subst T
    simp
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  obtain ⟨hl, hu⟩ := log_horizon_increment_bounds hT1
  refine ⟨mul_nonneg hT0.le ((by positivity : 0 ≤ 1 / ((T : ℝ) + 1)).trans hl), ?_⟩
  have h := mul_le_mul_of_nonneg_left hu hT0.le
  have hcancel : (T : ℝ) * (1 / T) = 1 := by field_simp [hT0.ne']
  simpa only [hcancel] using h

private theorem abs_subhorizon_nearGram_div_overlap_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N T m l : ℕ} (hT : 1 ≤ T) (hTN : T ≤ N)
    (hm : 0 < m) (hl : 0 < l) (hw : c / N ≤ 1) :
    |fixedWidthNearGram φ (c / N) T m l / (c * T / N)| ≤
      4 * Real.exp 2 * ((m.totient : ℝ) + l.totient) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hN0 : (0 : ℝ) < N := hT0.trans_le (by exact_mod_cast hTN)
  let u : ℝ := c * T / N
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hwidth : u / T = c / N := by dsimp [u]; field_simp [hT0.ne', hN0.ne']
  have hb := abs_fixedWidthNearGram_le hφ hsupp hM hu0 hT hm hl (by rwa [hwidth])
  rw [hwidth] at hb
  rw [abs_div, abs_of_pos hu0]
  calc
    _ ≤ (2 * linearNearRowRadius u * ((m.totient : ℝ) + l.totient)) / u :=
      div_le_div_of_nonneg_right hb hu0.le
    _ = _ := by unfold linearNearRowRadius; field_simp [hu0.ne']; ring

/-- Logarithmic horizon integration preserves the unique linear conductor mean. -/
theorem tendsto_fixedWidthNearPair_log_max_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      fixedWidthNearPair φ (c N / N) m l n j * (Real.log N - Real.log (max n j))) / c N)
      atTop (𝓝 (if m = l then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0)) := by
  let a : ℝ := if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0
  let α : ℝ := if m = l then a else 0
  let w : ℕ → ℝ := fun T => (T : ℝ) * (Real.log ((T : ℝ) + 1) - Real.log T)
  let f : ℕ → ℕ → ℝ := fun N T =>
    (fixedWidthNearGram φ (c N / N) T m l / (c N * T / N) - α) * w T
  let C₀ : ℝ := 4 * Real.exp 2 * ((m.totient : ℝ) + l.totient)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hwidth : ∀ᶠ N : ℕ in atTop, c N / N ≤ 1 :=
    ((tendsto_overlap_div_horizon hc he).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ T < N, |f N T| ≤ C₀ + |α| := by
    filter_upwards [hwidth] with N hw T hTN
    by_cases hT : T = 0
    · subst T
      simp only [f, w, Nat.cast_zero, zero_mul, mul_zero, abs_zero]
      positivity
    have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
    have hb := abs_subhorizon_nearGram_div_overlap_le hφ hsupp hM
      (zero_lt_one.trans_le (hc N)) hT1 hTN.le hm hl hw
    have hsub : |fixedWidthNearGram φ (c N / N) T m l / (c N * T / N) - α| ≤ C₀ + |α| := by
      have h := abs_sub_le (fixedWidthNearGram φ (c N / N) T m l / (c N * T / N)) 0 α
      simp only [sub_zero, zero_sub, abs_neg] at h
      exact h.trans (add_le_add hb le_rfl)
    obtain ⟨hw0, hw1⟩ := log_horizon_weight_bounds T
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg hw0]
    exact (mul_le_mul hsub hw1 hw0 (by positivity)).trans_eq (mul_one _)
  obtain ⟨C, hC, herr⟩ := exists_fixedWidthNearGram_subhorizon_error hφ hsupp hM
  have htail : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ → ℕ,
      Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ T < N, M N ≤ T → |f N T| ≤ ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hs := tendsto_shellCorrection_div_overlap hφ hsupp hM hm
    obtain ⟨U₀, hU₀⟩ := (Metric.tendsto_atTop.1 hs) (ε / 2) hε2
    let U : ℝ := max 1 U₀
    have hU1 : 1 ≤ U := le_max_left _ _
    have hU0 : 0 ≤ U := zero_le_one.trans hU1
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨B₀, hB₀⟩ := eventually_atTop.1
      ((eventually_ge_atTop (max 2 (max m l) * max 2 (max m l))).and
        (hlog.eventually_ge_atTop (18 * (1 + Real.log (max 2 (max m l) : ℕ)))))
    let B : ℕ := max 2 B₀
    let M : ℕ → ℕ := fun N => max B ⌈U * N / c N⌉₊
    refine ⟨M, tendsto_horizon_threshold_density hc hcinf B hU0, ?_⟩
    have herror : ∀ᶠ N : ℕ in atTop,
        C * ((m : ℝ) * l) ^ 5 * (c N ^ 4 * Real.log N / N) ≤ ε / 2 := by
      have h := he.const_mul (C * ((m : ℝ) * l) ^ 5)
      simp only [mul_zero] at h
      exact (h.eventually (gt_mem_nhds hε2)).mono fun _ h => h.le
    filter_upwards [herror, eventually_nearGram_radius_budget hc he, eventually_ge_atTop 1]
      with N heN hrN hN T hTN hMT
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hBT : B ≤ T := (le_max_left B _).trans hMT
    have hT2 : 2 ≤ T := (le_max_left 2 B₀).trans hBT
    have hB₀T : B₀ ≤ T := (le_max_right 2 B₀).trans hBT
    obtain ⟨hQ, hlogT⟩ := hB₀ T hB₀T
    have hceilT : (⌈U * N / c N⌉₊ : ℕ) ≤ T := (le_max_right B _).trans hMT
    have hUle : U ≤ c N * T / N := by
      have hx : U * N / c N ≤ (T : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hceilT)
      have hy := (div_le_iff₀ hc0).mp hx
      apply (le_div_iff₀ hN0).mpr
      simpa only [mul_comm (T : ℝ) (c N)] using hy
    have hu1 : 1 ≤ c N * T / N := hU1.trans hUle
    have hr := near_radius_le_subhorizon hc0 (by omega : 1 ≤ T) hTN.le hu1 hrN
    have hg := (herr hm hl hc0 hT2 hTN.le hQ hlogT hu1 hr).trans heN
    have hshell := hU₀ (c N * T / N) ((le_max_right 1 U₀).trans hUle)
    rw [Real.dist_eq] at hshell
    have hdiag : |(if m = l then shellCorrection φ (c N * T / N) m / (c N * T / N) else 0) - α| ≤ ε / 2 := by
      by_cases hml : m = l
      · simpa only [α, a, if_pos hml] using hshell.le
      · simp only [α, if_neg hml, sub_self, abs_zero]
        exact hε2.le
    have hsub := (abs_sub_le
      (fixedWidthNearGram φ (c N / N) T m l / (c N * T / N))
      (if m = l then shellCorrection φ (c N * T / N) m / (c N * T / N) else 0) α).trans
        (add_le_add hg hdiag)
    have hsub' : |fixedWidthNearGram φ (c N / N) T m l / (c N * T / N) - α| ≤ ε := by
      linarith only [hsub]
    obtain ⟨hw0, hw1⟩ := log_horizon_weight_bounds T
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg hw0]
    exact (mul_le_mul hsub' hw1 hw0 hε.le).trans_eq (mul_one _)
  have hz := tendsto_triangular_mean_zero_of_sparse_prefixes f (add_nonneg hC₀ (abs_nonneg α)) hbound htail
  have hmass := tendsto_linear_log_horizon_mass.const_mul α
  have hlim := hz.add hmass
  simp only [zero_add, mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  rw [fixedWidthNearPair_log_max_eq, sum_range_eq_add_Ico (f N) (by omega : 0 < N)]
  have hf0 : f N 0 = 0 := by simp only [f, w, Nat.cast_zero, zero_mul, mul_zero]
  rw [hf0, zero_add]
  simp only [mul_sum, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro T hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (mem_Ico.mp hT).1
  dsimp only [f, w]
  field_simp [hN0.ne', hc0.ne', hT0.ne']
  ring

/-- The receiving-index logarithmic row has the same polar limit as its nested-horizon form. -/
theorem tendsto_fixedWidthNearPair_log_row_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      fixedWidthNearPair φ (c N / N) m l n j * (Real.log N - Real.log j)) / c N)
      atTop (𝓝 (if m = l then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0)) := by
  let Lrow : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    fixedWidthNearPair φ (c N / N) m l n j * (Real.log N - Real.log j)
  let Lmax : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    fixedWidthNearPair φ (c N / N) m l n j * (Real.log N - Real.log (max n j))
  have hcN := tendsto_overlap_div_horizon hc he
  have hlim : Tendsto (fun N : ℕ =>
      (8 * Real.exp 2 * ((m.totient : ℝ) + l.totient)) * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul (8 * Real.exp 2 * ((m.totient : ℝ) + l.totient))
  have hz : Tendsto (fun N : ℕ => (Lrow N - Lmax N) / c N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1,
      (hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ h => h.le)] with N hN hw
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hgap := abs_fixedWidthNearPair_log_row_sub_max_le φ (div_nonneg hc0.le hN0.le) N m l
    have hraw := sum_abs_fixedWidthNearPair_le hφ hsupp hM hc0 hN hm hl hw
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0]
    calc
      _ ≤ (2 * (c N / N) *
          (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |fixedWidthNearPair φ (c N / N) m l n j|)) / c N :=
        div_le_div_of_nonneg_right hgap hc0.le
      _ ≤ (2 * (c N / N) *
          (2 * linearNearRowRadius (c N) * ((m.totient : ℝ) + l.totient))) / c N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hraw (by positivity)) hc0.le
      _ = _ := by unfold linearNearRowRadius; field_simp [hc0.ne']; ring
  have h := hz.add (tendsto_fixedWidthNearPair_log_max_div_overlap hφ hsupp hM hc hcinf he hm hl)
  simp only [zero_add] at h
  exact h.congr fun N => by dsimp only [Lrow, Lmax]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_fixedWidthNearPair_log_max_div_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_fixedWidthNearPair_log_row_div_overlap
