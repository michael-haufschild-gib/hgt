import GaloisForLFunctions.RHTower.BurnolCoPoissonHeadConstant
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# The explicit indicator seed of the co-Poisson sum

The simplest seed supported in the multiplicative window `[b, 1/b]` is the indicator of that
window.  Its co-Poisson sum is a pure window sum of reciprocals,

`∑_{|t| b ≤ n ≤ |t| / b} 1 / n`,

and its correction constant is the logarithmic length `2 log (1/b)` of the window.  Writing the
window sum as a difference of harmonic numbers turns the co-Poisson value into a harmonic-versus-
logarithm comparison, which is the source of its decay.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The indicator seed of the multiplicative window `[b, 1/b]`. -/
def coPoissonIndicatorSeed (b : ℝ) : ℝ → ℂ :=
  Set.indicator (Icc b b⁻¹) (fun _ => 1)

theorem support_coPoissonIndicatorSeed (b : ℝ) :
    Function.support (coPoissonIndicatorSeed b) ⊆ Icc b b⁻¹ := by
  intro x hx
  by_contra h
  exact hx (by rw [coPoissonIndicatorSeed, Set.indicator_of_notMem h])

theorem measurable_coPoissonIndicatorSeed (b : ℝ) : Measurable (coPoissonIndicatorSeed b) :=
  measurable_const.indicator measurableSet_Icc

theorem norm_coPoissonIndicatorSeed_le (b x : ℝ) : ‖coPoissonIndicatorSeed b x‖ ≤ 1 := by
  by_cases h : x ∈ Icc b b⁻¹
  · rw [coPoissonIndicatorSeed, Set.indicator_of_mem h]
    simp
  · rw [coPoissonIndicatorSeed, Set.indicator_of_notMem h]
    simp

theorem integrable_coPoissonIndicatorSeed (b : ℝ) : Integrable (coPoissonIndicatorSeed b) :=
  (integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator measurableSet_Icc

theorem coPoissonIndicatorSeed_of_mem {b x : ℝ} (h : x ∈ Icc b b⁻¹) :
    coPoissonIndicatorSeed b x = 1 := by
  rw [coPoissonIndicatorSeed, Set.indicator_of_mem h]

theorem coPoissonIndicatorSeed_of_notMem {b x : ℝ} (h : x ∉ Icc b b⁻¹) :
    coPoissonIndicatorSeed b x = 0 := by
  rw [coPoissonIndicatorSeed, Set.indicator_of_notMem h]


/-! ## Reflection symmetry of the window -/

/-- The multiplicative window is stable under inversion. -/
theorem inv_mem_windowIcc_iff {b y : ℝ} (hb : 0 < b) (hy : 0 < y) :
    y⁻¹ ∈ Icc b b⁻¹ ↔ y ∈ Icc b b⁻¹ := by
  rw [mem_Icc, mem_Icc, le_inv_comm₀ hb hy, inv_le_inv₀ hy hb, and_comm]

theorem le_inv_self_of_le_one {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : b ≤ b⁻¹ := by
  have h1 : (1 : ℝ) ≤ b⁻¹ := by
    rw [le_inv_comm₀ one_pos hb]
    simpa using hb1
  linarith


/-! ## The correction constant -/

theorem integral_windowIcc_inv {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∫ y in Icc b b⁻¹, ((y : ℝ) : ℂ)⁻¹ = ((2 * Real.log b⁻¹ : ℝ) : ℂ) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_inv_self_of_le_one hb hb1)]
  have hcast : ∀ y : ℝ, ((y : ℝ) : ℂ)⁻¹ = ((y⁻¹ : ℝ) : ℂ) := fun y => (Complex.ofReal_inv y).symm
  simp_rw [hcast]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos hb (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_inv]
  push_cast
  ring

/-- **The correction constant of the indicator seed.**  It is the logarithmic length of the
multiplicative window. -/
theorem coPoissonIndicatorSeed_correction {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b y⁻¹ =
      ((2 * Real.log b⁻¹ : ℝ) : ℂ) := by
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b y⁻¹ =
      Set.indicator (Icc b b⁻¹) (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹) y := by
    intro y hy
    by_cases h : y ∈ Icc b b⁻¹
    · rw [Set.indicator_of_mem h,
        coPoissonIndicatorSeed_of_mem ((inv_mem_windowIcc_iff hb hy).mpr h), mul_one]
    · rw [Set.indicator_of_notMem h,
        coPoissonIndicatorSeed_of_notMem (fun hc => h ((inv_mem_windowIcc_iff hb hy).mp hc)),
        mul_zero]
  have hsub : Ioi (0 : ℝ) ∩ Icc b b⁻¹ = Icc b b⁻¹ := by
    rw [Set.inter_eq_right]
    intro y hy
    exact lt_of_lt_of_le hb hy.1
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Icc, hsub,
    integral_windowIcc_inv hb hb1]


/-! ## The window sum -/

/-- Membership of the contributing window: a scale `t / k` lies in `[b, 1/b]` exactly when the
index `k` lies between `t b` and `t / b`. -/
theorem coPoissonIndicatorSeed_scale_mem {b t : ℝ} (hb : 0 < b) {k : ℕ} (hk : 0 < k)
    (h1 : t * b ≤ (k : ℝ)) (h2 : (k : ℝ) ≤ t / b) :
    t / (k : ℝ) ∈ Icc b b⁻¹ := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hkpos, mul_comm]
    exact (le_div_iff₀ hb).mp h2
  · rw [div_le_iff₀ hkpos, inv_mul_eq_div, le_div_iff₀ hb]
    exact h1

/-- **The co-Poisson sum of the indicator seed is a window sum of reciprocals.** -/
theorem coPoissonIndicatorSum_eq_finset_sum {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊, (((k : ℕ) : ℝ) : ℂ)⁻¹ := by
  set m : ℕ := ⌈t * b⌉₊ with hm
  set N : ℕ := ⌊t / b⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  -- Every contributing index lies below `N`.
  have hvanish : ∀ n : ℕ, n ∉ Finset.range N →
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n hn
    by_cases hz : coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ)) = 0
    · rw [hz, mul_zero]
    · exfalso
      have hmem : t / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
        support_coPoissonIndicatorSeed b (Function.mem_support.mpr hz)
      have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlow : b ≤ t / ((n + 1 : ℕ) : ℝ) := hmem.1
      rw [le_div_iff₀ hnpos] at hlow
      have hle : ((n + 1 : ℕ) : ℝ) ≤ t / b := by
        rw [le_div_iff₀ hb, mul_comm]
        exact hlow
      have : n + 1 ≤ N := Nat.le_floor hle
      exact (Finset.mem_range.not.mp hn) (by omega)
  rw [tsum_eq_sum hvanish]
  -- Reindex `range N` as `Icc 1 N`.
  have hreindex : ∀ f : ℕ → ℂ, ∑ n ∈ Finset.range N, f (n + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc, zero_add]
  rw [hreindex (fun k => (((k : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b (t / ((k : ℕ) : ℝ)))]
  -- The window `Icc m N` carries the whole sum.
  have hsubset : Finset.Icc m N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left hmpos
  have houtside : ∀ k ∈ Finset.Icc 1 N, k ∉ Finset.Icc m N →
      (((k : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b (t / ((k : ℕ) : ℝ)) = 0 := by
    intro k hk hkn
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hklt : k < m := by
      by_contra hc
      exact hkn (Finset.mem_Icc.mpr ⟨not_lt.mp hc, hkN⟩)
    have hkreal : (k : ℝ) < t * b := Nat.lt_ceil.mp hklt
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hout : t / (k : ℝ) ∉ Icc b b⁻¹ := by
      rintro ⟨-, h2⟩
      rw [div_le_iff₀ hkpos, inv_mul_eq_div, le_div_iff₀ hb] at h2
      linarith
    rw [coPoissonIndicatorSeed_of_notMem hout, mul_zero]
  rw [← Finset.sum_subset hsubset houtside]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hkpos : 0 < k := lt_of_lt_of_le hmpos hk1
  have hlow : t * b ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
  have hhigh : (k : ℝ) ≤ t / b := le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
  rw [coPoissonIndicatorSeed_of_mem (coPoissonIndicatorSeed_scale_mem hb hkpos hlow hhigh), mul_one]



/-! ## Harmonic form -/

/-- **The window sum is a difference of harmonic numbers.** -/
theorem coPoissonIndicatorSum_eq_harmonic {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ))) =
      (((harmonic ⌊t / b⌋₊ : ℝ) - harmonic (⌈t * b⌉₊ - 1) : ℝ) : ℂ) := by
  set m : ℕ := ⌈t * b⌉₊ with hm
  set N : ℕ := ⌊t / b⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hMsucc : m - 1 + 1 = m := by omega
  have hMN : m - 1 ≤ N := by
    refine Nat.le_floor ?_
    have hlt : ((m - 1 : ℕ) : ℝ) < t * b := Nat.lt_ceil.mp (by omega)
    have hmono : t * b ≤ t * b⁻¹ :=
      mul_le_mul_of_nonneg_left (le_inv_self_of_le_one hb hb1) ht.le
    rw [← div_eq_mul_inv] at hmono
    linarith
  rw [coPoissonIndicatorSum_eq_finset_sum hb ht,
    show Finset.Icc m N = Finset.Ioc (m - 1) N from hMsucc ▸ Finset.Icc_add_one_left_eq_Ioc (m - 1) N,
    ← HTGeometry.sum_Ioc_inv_eq_harmonic_sub hMN, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => (Complex.ofReal_inv _).symm

/-- **The co-Poisson value of the indicator seed.**  It is the harmonic window sum minus the
logarithmic length of the window. -/
theorem burnolCoPoissonRightSum_coPoissonIndicatorSeed {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t =
      (((harmonic ⌊t / b⌋₊ : ℝ) - harmonic (⌈t * b⌉₊ - 1) - 2 * Real.log b⁻¹ : ℝ) : ℂ) := by
  rw [burnolCoPoissonRightSum, abs_of_pos ht, coPoissonIndicatorSum_eq_harmonic hb hb1 ht,
    coPoissonIndicatorSeed_correction hb hb1]
  push_cast
  ring


/-! ## Decay -/

/-- The logarithmic length of the window is the logarithm of the ratio of the two window ends at
any positive scale. -/
theorem two_log_inv_eq_log_div_sub_log_mul {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    2 * Real.log b⁻¹ = Real.log (t / b) - Real.log (t * b) := by
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hb), Real.log_mul (ne_of_gt ht) (ne_of_gt hb),
    Real.log_inv]
  ring

/-- **Decay of the co-Poisson value of the indicator seed.**  Beyond the scale `2 / b` the window
sum tracks the logarithmic window length with error `O(1/t)`.  The two endpoint corrections of the
harmonic comparison and the two floor/ceiling corrections each contribute one reciprocal endpoint,
and both endpoints are comparable to `t`. -/
theorem norm_burnolCoPoissonRightSum_coPoissonIndicatorSeed_le
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {t : ℝ} (ht : 2 / b ≤ t) :
    ‖burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t‖ ≤ (4 * b + 4 / b) / t := by
  have hb2 : b * b ≤ 1 := by nlinarith
  have h2b : (2 : ℝ) ≤ 2 / b := by
    rw [le_div_iff₀ hb]; nlinarith
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) (le_trans h2b ht)
  have htb : (2 : ℝ) ≤ t * b := by
    have := mul_le_mul_of_nonneg_right ht hb.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hb)] at this
  have hu : (2 : ℝ) ≤ t / b := by
    rw [le_div_iff₀ hb]
    nlinarith
  set m : ℕ := ⌈t * b⌉₊ with hm
  set N : ℕ := ⌊t / b⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast le_trans (by norm_num) hu)
  have hm2 : 2 ≤ m := by
    have h : (1 : ℕ) < m := Nat.lt_ceil.mpr (by push_cast; linarith)
    omega
  have hM1 : 1 ≤ m - 1 := by omega
  have hNle : ((N : ℕ) : ℝ) ≤ t / b := Nat.floor_le (by positivity)
  have hNlt : t / b < ((N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMlt : ((m - 1 : ℕ) : ℝ) < t * b := Nat.lt_ceil.mp (by omega)
  have hMle : t * b ≤ ((m - 1 : ℕ) : ℝ) + 1 := by
    have hcast : ((m : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
      have : m = (m - 1) + 1 := by omega
      rw [this]; push_cast; ring
    rw [← hcast]
    exact Nat.le_ceil _
  -- Both window ends are comparable to `t`.
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  have hMpos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hM1
  have hNbound : 1 / ((N : ℕ) : ℝ) ≤ 2 * b / t := by
    have hlow : t / (2 * b) ≤ ((N : ℕ) : ℝ) := by
      have hhalf : t / (2 * b) = (t / b) / 2 := by
        rw [div_div]; ring_nf
      rw [hhalf]
      linarith
    have hposlow : (0 : ℝ) < t / (2 * b) := by positivity
    have h := one_div_le_one_div_of_le hposlow hlow
    rwa [one_div_div] at h
  have hMbound : 1 / ((m - 1 : ℕ) : ℝ) ≤ 2 / (t * b) := by
    have hlow : t * b / 2 ≤ ((m - 1 : ℕ) : ℝ) := by linarith
    have hposlow : (0 : ℝ) < t * b / 2 := by positivity
    have h := one_div_le_one_div_of_le hposlow hlow
    rwa [one_div_div] at h
  -- The three comparisons.
  have hA := HTGeometry.abs_harmonic_window_sub_log_le hM1 hN1
  have hB := HTGeometry.abs_log_sub_log_le_inv hN1 hNle hNlt.le
  have hC := HTGeometry.abs_log_sub_log_le_inv hM1 hMlt.le hMle
  rw [burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1 htpos, Complex.norm_real,
    Real.norm_eq_abs, two_log_inv_eq_log_div_sub_log_mul hb htpos]
  have hsplit : ((harmonic N : ℝ) - harmonic (m - 1) -
        (Real.log (t / b) - Real.log (t * b))) =
      (((harmonic N : ℝ) - harmonic (m - 1)) -
          (Real.log N - Real.log (m - 1))) -
        (Real.log (t / b) - Real.log N) + (Real.log (t * b) - Real.log (m - 1)) := by
    ring
  rw [hsplit]
  have hcombine : (4 * b + 4 / b) / t =
      2 * (2 * b / t) + 2 * (2 / (t * b)) := by
    field_simp
    ring
  rw [hcombine]
  rw [abs_le] at hA hB hC ⊢
  constructor <;> [linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2];
    linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]]

end RHTower

