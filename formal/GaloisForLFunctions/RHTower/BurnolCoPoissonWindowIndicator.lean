import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindow

/-!
# Indicator seeds of an arbitrary multiplicative window

The indicator of a window `[c,d]` is the reciprocal seed of the reciprocal function on the inverted
window, so the two form a co-Poisson pair.  Its co-Poisson sum is the harmonic window sum

`harmonic (floor (t/c)) - harmonic (ceil (t/d) - 1)`,

and its correction constant is the logarithmic length `log d - log c` of the window.  Taking
`d = 1/c` recovers the symmetric window.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The indicator seed of a multiplicative window. -/
def coPoissonWindowIndicatorSeed (c d : ℝ) : ℝ → ℂ :=
  Set.indicator (Icc c d) fun _ => 1

theorem support_coPoissonWindowIndicatorSeed (c d : ℝ) :
    Function.support (coPoissonWindowIndicatorSeed c d) ⊆ Icc c d := by
  intro x hx
  by_contra h
  exact hx (by rw [coPoissonWindowIndicatorSeed, Set.indicator_of_notMem h])

theorem coPoissonWindowIndicatorSeed_of_mem {c d x : ℝ} (h : x ∈ Icc c d) :
    coPoissonWindowIndicatorSeed c d x = 1 := by
  rw [coPoissonWindowIndicatorSeed, Set.indicator_of_mem h]

theorem coPoissonWindowIndicatorSeed_of_notMem {c d x : ℝ} (h : x ∉ Icc c d) :
    coPoissonWindowIndicatorSeed c d x = 0 := by
  rw [coPoissonWindowIndicatorSeed, Set.indicator_of_notMem h]

theorem measurable_coPoissonWindowIndicatorSeed (c d : ℝ) :
    Measurable (coPoissonWindowIndicatorSeed c d) :=
  measurable_const.indicator measurableSet_Icc

theorem integrable_coPoissonWindowIndicatorSeed (c d : ℝ) :
    Integrable (coPoissonWindowIndicatorSeed c d) :=
  (integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator measurableSet_Icc

/-- **The window indicator is the reciprocal seed of the inverted-window reciprocal.** -/
theorem coPoissonReciprocalSeed_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (v : ℝ) :
    coPoissonReciprocalSeed (coPoissonSubWindowSeed c d) v =
      coPoissonWindowIndicatorSeed d⁻¹ c⁻¹ v := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  rcases le_or_gt v 0 with hv | hv
  · have hout : v ∉ Icc d⁻¹ c⁻¹ := fun hcon =>
      absurd (lt_of_lt_of_le (inv_pos.mpr hd) hcon.1) (not_lt.mpr hv)
    have hout' : v⁻¹ ∉ Icc c d := fun hcon =>
      absurd (inv_pos.mp (lt_of_lt_of_le hc hcon.1)) (not_lt.mpr hv)
    rw [coPoissonWindowIndicatorSeed_of_notMem hout, coPoissonReciprocalSeed,
      coPoissonSubWindowSeed_of_notMem hout', mul_zero]
  · have hiff : v⁻¹ ∈ Icc c d ↔ v ∈ Icc d⁻¹ c⁻¹ := by
      rw [mem_Icc, mem_Icc, le_inv_comm₀ hc hv, inv_le_comm₀ hv hd, and_comm]
    have hvne : ((v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
    by_cases h : v ∈ Icc d⁻¹ c⁻¹
    · rw [coPoissonWindowIndicatorSeed_of_mem h, coPoissonReciprocalSeed,
        coPoissonSubWindowSeed_of_mem (hiff.mpr h), Complex.ofReal_inv, inv_inv,
        inv_mul_cancel₀ hvne]
    · rw [coPoissonWindowIndicatorSeed_of_notMem h, coPoissonReciprocalSeed,
        coPoissonSubWindowSeed_of_notMem (fun hcon => h (hiff.mp hcon)), mul_zero]

/-! ## The correction constant -/

theorem integral_Icc_inv_ofReal {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∫ y in Icc p q, ((y : ℝ) : ℂ)⁻¹) = ((Real.log q - Real.log p : ℝ) : ℂ) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpq]
  have hcast : ∀ y : ℝ, ((y : ℝ) : ℂ)⁻¹ = ((y⁻¹ : ℝ) : ℂ) := fun y => (Complex.ofReal_inv y).symm
  simp_rw [hcast]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos hp (lt_of_lt_of_le hp hpq),
    Real.log_div (ne_of_gt (lt_of_lt_of_le hp hpq)) (ne_of_gt hp)]

/-- **The correction constant of a window indicator seed is the logarithmic window length.** -/
theorem coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) :
    coPoissonCorrectionConstant (coPoissonWindowIndicatorSeed c d) =
      ((Real.log d - Real.log c : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hinv : d⁻¹ ≤ c⁻¹ := by
    rw [inv_le_inv₀ hd hc]
    exact hcd
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * coPoissonWindowIndicatorSeed c d y⁻¹ =
      Set.indicator (Icc d⁻¹ c⁻¹) (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹) y := by
    intro y hy
    have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
    have hiff : y⁻¹ ∈ Icc c d ↔ y ∈ Icc d⁻¹ c⁻¹ := by
      rw [mem_Icc, mem_Icc, le_inv_comm₀ hc hypos, inv_le_comm₀ hypos hd, and_comm]
    by_cases h : y ∈ Icc d⁻¹ c⁻¹
    · rw [Set.indicator_of_mem h, coPoissonWindowIndicatorSeed_of_mem (hiff.mpr h), mul_one]
    · rw [Set.indicator_of_notMem h,
        coPoissonWindowIndicatorSeed_of_notMem (fun hcon => h (hiff.mp hcon)), mul_zero]
  have hsub : Ioi (0 : ℝ) ∩ Icc d⁻¹ c⁻¹ = Icc d⁻¹ c⁻¹ := by
    rw [Set.inter_eq_right]
    intro y hy
    exact lt_of_lt_of_le (inv_pos.mpr hd) hy.1
  rw [coPoissonCorrectionConstant, setIntegral_congr_fun measurableSet_Ioi hpt,
    setIntegral_indicator measurableSet_Icc, hsub,
    integral_Icc_inv_ofReal (inv_pos.mpr hd) hinv, Real.log_inv, Real.log_inv]
  push_cast
  ring

/-! ## The harmonic form -/

/-- **The co-Poisson sum of a window indicator seed is a window sum of reciprocals.** -/
theorem coPoissonWindowIndicatorSum_eq_finset_sum {c d t : ℝ} (hc : 0 < c) (hd : 0 < d)
    (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed c d (t / ((n + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊, (((k : ℕ) : ℝ) : ℂ)⁻¹ := by
  rw [coPoissonSum_eq_subWindow_finset_sum hc hd ht (support_coPoissonWindowIndicatorSeed c d)]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hmpos : 1 ≤ ⌈t / d⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hkpos : 0 < k := lt_of_lt_of_le hmpos hk1
  have hlow : t / d ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
  have hhigh : (k : ℝ) ≤ t / c := le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
  rw [coPoissonWindowIndicatorSeed_of_mem (subWindow_scale_mem hc hkpos hlow hhigh hd), mul_one]

/-- **The window sum is a difference of harmonic numbers.** -/
theorem coPoissonWindowIndicatorSum_eq_harmonic {c d t : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed c d (t / ((n + 1 : ℕ) : ℝ))) =
      (((harmonic ⌊t / c⌋₊ : ℝ) - harmonic (⌈t / d⌉₊ - 1) : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  set m : ℕ := ⌈t / d⌉₊ with hm
  set N : ℕ := ⌊t / c⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hMsucc : m - 1 + 1 = m := by omega
  have hMN : m - 1 ≤ N := by
    refine Nat.le_floor ?_
    have hlt : ((m - 1 : ℕ) : ℝ) < t / d := Nat.lt_ceil.mp (by omega)
    have hmono : t / d ≤ t / c := div_le_div_of_nonneg_left ht.le hc hcd
    linarith
  rw [coPoissonWindowIndicatorSum_eq_finset_sum hc hd ht,
    show Finset.Icc m N = Finset.Ioc (m - 1) N from
      hMsucc ▸ Finset.Icc_add_one_left_eq_Ioc (m - 1) N,
    ← HTGeometry.sum_Ioc_inv_eq_harmonic_sub hMN, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => (Complex.ofReal_inv _).symm

/-- **The co-Poisson value of a window indicator seed.** -/
theorem burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {t : ℝ} (ht : 0 < t) :
    burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t =
      (((harmonic ⌊t / c⌋₊ : ℝ) - harmonic (⌈t / d⌉₊ - 1) -
        (Real.log d - Real.log c) : ℝ) : ℂ) := by
  rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos ht,
    coPoissonWindowIndicatorSum_eq_harmonic hc hcd ht,
    coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed hc hcd]
  push_cast
  ring



/-! ## Decay -/

/-- The logarithmic window length is the logarithm of the ratio of the two window ends at any
positive scale. -/
theorem log_window_eq_log_div_sub_log_div {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (ht : 0 < t) :
    Real.log d - Real.log c = Real.log (t / c) - Real.log (t / d) := by
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hc), Real.log_div (ne_of_gt ht) (ne_of_gt hd)]
  ring

/-- **Decay of the co-Poisson value of a window indicator seed.**  Beyond the scale `2 d` the
harmonic window sum tracks the logarithmic window length with error `O(1/t)`. -/
theorem norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) {t : ℝ} (ht : 2 * d ≤ t) :
    ‖burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t‖ ≤ 4 * (c + d) / t := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht
  have htd : (2 : ℝ) ≤ t / d := by
    rw [le_div_iff₀ hd]
    linarith
  have htc : (2 : ℝ) ≤ t / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  set m : ℕ := ⌈t / d⌉₊ with hm
  set N : ℕ := ⌊t / c⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast le_trans (by norm_num) htc)
  have hm2 : 2 ≤ m := by
    have h : (1 : ℕ) < m := Nat.lt_ceil.mpr (by push_cast; linarith)
    omega
  have hM1 : 1 ≤ m - 1 := by omega
  have hNle : ((N : ℕ) : ℝ) ≤ t / c := Nat.floor_le (by positivity)
  have hNlt : t / c < ((N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMlt : ((m - 1 : ℕ) : ℝ) < t / d := Nat.lt_ceil.mp (by omega)
  have hMle : t / d ≤ ((m - 1 : ℕ) : ℝ) + 1 := by
    have hcast : ((m : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
      have hms : m = (m - 1) + 1 := by omega
      rw [hms]
      push_cast
      ring
    rw [← hcast]
    exact Nat.le_ceil _
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  have hMpos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hM1
  have hNbound : 1 / ((N : ℕ) : ℝ) ≤ 2 * c / t := by
    have hlow : t / (2 * c) ≤ ((N : ℕ) : ℝ) := by
      have hhalf : t / (2 * c) = (t / c) / 2 := by
        rw [div_div]
        ring_nf
      rw [hhalf]
      linarith
    have hposlow : (0 : ℝ) < t / (2 * c) := by positivity
    have h := one_div_le_one_div_of_le hposlow hlow
    rwa [one_div_div] at h
  have hMbound : 1 / ((m - 1 : ℕ) : ℝ) ≤ 2 * d / t := by
    have hlow : t / (2 * d) ≤ ((m - 1 : ℕ) : ℝ) := by
      have hhalf : t / (2 * d) = (t / d) / 2 := by
        rw [div_div]
        ring_nf
      rw [hhalf]
      linarith
    have hposlow : (0 : ℝ) < t / (2 * d) := by positivity
    have h := one_div_le_one_div_of_le hposlow hlow
    rwa [one_div_div] at h
  have hA := HTGeometry.abs_harmonic_window_sub_log_le hM1 hN1
  have hB := HTGeometry.abs_log_sub_log_le_inv hN1 hNle hNlt.le
  have hC := HTGeometry.abs_log_sub_log_le_inv hM1 hMlt.le hMle
  rw [burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed hc hcd htpos, Complex.norm_real,
    Real.norm_eq_abs, log_window_eq_log_div_sub_log_div hc hd htpos]
  have hsplit : ((harmonic N : ℝ) - harmonic (m - 1) -
        (Real.log (t / c) - Real.log (t / d))) =
      (((harmonic N : ℝ) - harmonic (m - 1)) -
          (Real.log N - Real.log (m - 1))) -
        (Real.log (t / c) - Real.log N) + (Real.log (t / d) - Real.log (m - 1)) := by
    ring
  rw [hsplit]
  have hcombine : 4 * (c + d) / t = 2 * (2 * c / t) + 2 * (2 * d / t) := by
    field_simp
    ring
  rw [hcombine, abs_le] at *
  constructor <;> [linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2];
    linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]]



/-! ## Local bound, profile and square integrability -/

theorem log_window_nonneg {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    0 ≤ Real.log d - Real.log c := by
  have := Real.log_le_log hc hcd
  linarith

theorem coPoissonWindowIndicatorSeed_zero {c d : ℝ} (hc : 0 < c) :
    coPoissonWindowIndicatorSeed c d 0 = 0 := by
  refine coPoissonWindowIndicatorSeed_of_notMem ?_
  rintro ⟨h1, -⟩
  linarith

theorem norm_coPoissonWindowIndicatorSum_le_scale {c d t : ℝ} (hc : 0 < c) (hd : 0 < d)
    (ht : 0 ≤ t) :
    ‖∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed c d (t / ((n + 1 : ℕ) : ℝ))‖ ≤ t / c := by
  rcases eq_or_lt_of_le ht with h | h
  · have hz : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed c d (t / ((n + 1 : ℕ) : ℝ)) = 0 := by
      intro n
      rw [← h, zero_div, coPoissonWindowIndicatorSeed_zero hc, mul_zero]
    rw [tsum_congr hz, tsum_zero, norm_zero, ← h, zero_div]
  · rw [coPoissonWindowIndicatorSum_eq_finset_sum hc hd h]
    refine le_trans (norm_sum_le _ _) ?_
    have hmpos : 1 ≤ ⌈t / d⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    have hterm : ∀ k ∈ Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊, ‖(((k : ℕ) : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
      intro k hk
      have hk1 : 1 ≤ k := le_trans hmpos (Finset.mem_Icc.mp hk).1
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ hkreal
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
    rw [nsmul_eq_mul, mul_one, Nat.card_Icc]
    have hcard : (⌊t / c⌋₊ + 1 - ⌈t / d⌉₊ : ℕ) ≤ ⌊t / c⌋₊ := by omega
    calc ((⌊t / c⌋₊ + 1 - ⌈t / d⌉₊ : ℕ) : ℝ) ≤ ((⌊t / c⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ t / c := Nat.floor_le (by positivity)

theorem norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_local {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (t : ℝ) :
    ‖burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t‖ ≤
      |t| / c + (Real.log d - Real.log c) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  rw [burnolCoPoissonRightSum,
    show (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * coPoissonWindowIndicatorSeed c d y⁻¹)) =
      ((Real.log d - Real.log c : ℝ) : ℂ) from
        coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed hc hcd]
  refine le_trans (norm_sub_le _ _) (add_le_add
    (norm_coPoissonWindowIndicatorSum_le_scale hc hd (abs_nonneg t)) ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (log_window_nonneg hc hcd)]

/-- **A square-integrable decay profile for the window indicator co-Poisson value.** -/
theorem norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_profile {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) (t : ℝ) :
    ‖burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t‖ ≤
      (8 * (c + d) + (max (2 * d) 1 / c + (Real.log d - Real.log c)) * (1 + max (2 * d) 1)) *
        (1 + |t|)⁻¹ := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hL : (0 : ℝ) ≤ Real.log d - Real.log c := log_window_nonneg hc hcd
  have hT1 : (1 : ℝ) ≤ max (2 * d) 1 := le_max_right _ _
  have hT2 : 2 * d ≤ max (2 * d) 1 := le_max_left _ _
  have hden : (0 : ℝ) < 1 + |t| := by positivity
  have habs : burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t =
      burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) |t| := by
    simp only [burnolCoPoissonRightSum, abs_abs]
  have hC0 : (0 : ℝ) ≤ max (2 * d) 1 / c + (Real.log d - Real.log c) := by positivity
  have hCfar : (0 : ℝ) ≤ 8 * (c + d) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  rcases le_or_gt (max (2 * d) 1) |t| with hfar | hnear
  · have hpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos (le_trans hT1 hfar)
    have hA := norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le hc hcd
      (le_trans hT2 hfar)
    rw [← habs] at hA
    have ht1 : (1 : ℝ) ≤ |t| := le_trans hT1 hfar
    have hnn : (0 : ℝ) ≤ 4 * (c + d) / |t| := by positivity
    have hstep : ‖burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t‖ * (1 + |t|) ≤
        4 * (c + d) / |t| * (2 * |t|) := by
      have h1 : 1 + |t| ≤ 2 * |t| := by linarith
      nlinarith [norm_nonneg (burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t)]
    have hval : 4 * (c + d) / |t| * (2 * |t|) = 8 * (c + d) := by
      field_simp
      ring
    have hextra : (0 : ℝ) ≤
        (max (2 * d) 1 / c + (Real.log d - Real.log c)) * (1 + max (2 * d) 1) := by positivity
    linarith [hstep, hval.le, hval.ge]
  · have hB := norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_local hc hcd t
    have hle : |t| / c + (Real.log d - Real.log c) ≤
        max (2 * d) 1 / c + (Real.log d - Real.log c) := by
      have : |t| / c ≤ max (2 * d) 1 / c := by
        exact div_le_div_of_nonneg_right hnear.le hc.le
      linarith
    have h1t : 1 + |t| ≤ 1 + max (2 * d) 1 := by linarith
    have h1 : ‖burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t‖ * (1 + |t|) ≤
        (max (2 * d) 1 / c + (Real.log d - Real.log c)) * (1 + |t|) :=
      mul_le_mul_of_nonneg_right (le_trans hB hle) hden.le
    have h2 : (max (2 * d) 1 / c + (Real.log d - Real.log c)) * (1 + |t|) ≤
        (max (2 * d) 1 / c + (Real.log d - Real.log c)) * (1 + max (2 * d) 1) :=
      mul_le_mul_of_nonneg_left h1t hC0
    linarith

theorem support_coPoissonWindowIndicatorSeed_symmetric {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    Function.support (coPoissonWindowIndicatorSeed c d) ⊆ Icc (min c d⁻¹) (min c d⁻¹)⁻¹ := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hbpos : (0 : ℝ) < min c d⁻¹ := lt_min hc (inv_pos.mpr hd)
  refine (support_coPoissonWindowIndicatorSeed c d).trans ?_
  intro x hx
  refine ⟨le_trans (min_le_left _ _) hx.1, ?_⟩
  have h2 : d ≤ (min c d⁻¹)⁻¹ := by
    rw [le_inv_comm₀ hd hbpos]
    exact min_le_right _ _
  exact le_trans hx.2 h2

theorem measurable_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) : Measurable (burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d)) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  exact measurable_burnolCoPoissonRightSum (lt_min hc (inv_pos.mpr hd))
    (measurable_coPoissonWindowIndicatorSeed c d)
    (support_coPoissonWindowIndicatorSeed_symmetric hc hcd)

/-- **The window indicator co-Poisson value is square integrable.** -/
theorem memLp_two_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) :
    MemLp (burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d)) 2 volume :=
  HTGeometry.memLp_two_of_decayProfile
    (measurable_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed hc hcd).aestronglyMeasurable
    (norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_profile hc hcd)

/-- **The window indicator co-Poisson value is real.** -/
theorem star_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (t : ℝ) :
    (starRingEnd ℂ) (burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t) =
      burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have habs : burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t =
      burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) |t| := by
    simp only [burnolCoPoissonRightSum, abs_abs]
  rcases eq_or_lt_of_le (abs_nonneg t) with hz | hpos
  · have hzero : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed c d (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
      intro n
      rw [← hz, zero_div, coPoissonWindowIndicatorSeed_zero hc, mul_zero]
    rw [habs, burnolCoPoissonRightSum, abs_abs, tsum_congr hzero, tsum_zero, zero_sub,
      show (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * coPoissonWindowIndicatorSeed c d y⁻¹)) =
        ((Real.log d - Real.log c : ℝ) : ℂ) from
          coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed hc hcd,
      map_neg, Complex.conj_ofReal]
  · rw [habs, burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed hc hcd hpos]
    exact Complex.conj_ofReal _

end RHTower
