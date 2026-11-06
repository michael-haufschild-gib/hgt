import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheFourthMomentOfTheDepths
import GaloisForLFunctions.RHTower.KiKimLeeTwoThirdsHorizon

/-!
# Nonreal time is rare on almost all windows

Let `nonrealTimes j` be the set of heats `s > 0` at which `H_s` has a nonreal zero with `|Re z − j| ≤ ½`. Dissipation of
the depth moments and Selberg's near-line density give, on a block of `≍ U` windows at heights `≍ U`,

`Σ_j ∫_{τ₀}^{1/log U} N_j ≤ C (1/τ₀ + log U) U/log³U`   (`exists_sum_nonrealTime_le_selberg`),

for every `τ₀ ≤ 1/log U`. So for each `ε > 0` all but `O_ε(U/log U)` windows spend total heat time at most
`ε/log U` nonreal (`exists_card_nonrealTime_gt_le`). This is the heat-flow form of near-line clustering in time
measure, with a rate in the exceptional count; the proof uses no value of `ζ` beyond the near-line density.

It complements the pointwise statement for the local Newman constant on typical heights: it bounds the time
spent nonreal, not the last time. A nonreal zero could enter a window laterally at tiny depth after the
window has been real; vertical dissipation cannot see this.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The budget on a Selberg block -/

theorem pow_four_le_two_pow {n : ℕ} (hn : 20 ≤ n) : ((n : ℝ) + 1) ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
    rw [pow_succ 2 n]
    push_cast
    set m : ℝ := (n : ℝ) + 1 with hm
    have hm21 : 21 ≤ m := by rw [hm]; linarith only [hn']
    have h1 : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
      have hm3 : 0 ≤ m ^ 3 := by positivity
      have hm2 : 0 ≤ m ^ 2 := by positivity
      have h2 : 21 * m ^ 3 ≤ m ^ 4 := by
        have := mul_le_mul_of_nonneg_right hm21 hm3
        nlinarith only [this]
      have h3 : 21 * m ^ 2 ≤ m ^ 3 := by
        have := mul_le_mul_of_nonneg_right hm21 hm2
        nlinarith only [this]
      have h4 : 21 * m ≤ m ^ 2 := by nlinarith only [hm21]
      nlinarith only [h2, h3, h4, hm21]
    have : (m + 1) = (n : ℝ) + 1 + 1 := by rw [hm]
    rw [← this]
    nlinarith only [h1, ih]

/-- **The nonreal-time budget at height `U`.** A block of `≍ U` windows spends time `≪ (1/τ₀ + log U) U/log³U` above
`τ₀`. -/
theorem exists_sum_nonrealTime_le_selberg :
    ∃ C > 0, ∀ᶠ U : ℝ in atTop, ∃ A B : ℤ, U / 4 ≤ A ∧ (A : ℝ) ≤ U / 4 + 8 * Real.log U ∧
      U / 2 - 8 * Real.log U ≤ B ∧ (B : ℝ) ≤ U / 2 ∧ A ≤ B ∧ ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 / Real.log U →
        ∑ j ∈ Finset.Icc A B, ∫ s in τ₀..(1 / Real.log U), windowObs uNonreal j s ≤
          C * (1 / τ₀ + Real.log U) * (U / Real.log U ^ 3) := by
  obtain ⟨C₀, hC₀, X₀, hX₀, hbudget⟩ := exists_sum_nonrealTime_le
  obtain ⟨C₁, hC₁, hmoment⟩ := exists_blockObs_quartic_zero_le
  refine ⟨C₀ * (C₁ + 1), by positivity, ?_⟩
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hsmall : ∀ᶠ U : ℝ in atTop, Real.log U ≤ U / 1000 := by
    have := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 1000)
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with U hU hU1
    simp only [Real.norm_eq_abs, id_eq] at hU
    rw [abs_of_nonneg (Real.log_nonneg hU1), abs_of_nonneg (by linarith only [hU1] : 0 ≤ U)] at hU
    linarith only [hU]
  filter_upwards [hmoment, hsmall, hlog.eventually_ge_atTop 21, eventually_ge_atTop (4 * X₀ + 4),
    eventually_ge_atTop (1000 : ℝ)] with U hU hsm hL21 hUX hU1000
  obtain ⟨T₁, hT₁, T₂, hT₂, hblock⟩ := hU
  set L := Real.log U with hLdef
  have hLpos : 0 < L := by linarith only [hL21]
  have hUpos : 0 < U := by linarith only [hU1000]
  set K : ℕ := ⌊L⌋₊ with hK
  have hKL : (K : ℝ) ≤ L := Nat.floor_le hLpos.le
  have hLK : L < (K : ℝ) + 1 := Nat.lt_floor_add_one L
  have hK20 : 20 ≤ K := by
    have : (20 : ℝ) < (K : ℝ) := by linarith only [hL21, hLK]
    exact_mod_cast this.le
  set A : ℤ := ⌈T₁⌉ + 4 * ((K : ℤ) + 3) + 1 with hA
  set B : ℤ := ⌊T₂⌋ - 4 * ((K : ℤ) + 3) - 1 with hB
  have hc1 := Int.le_ceil T₁
  have hc2 := Int.ceil_lt_add_one T₁
  have hf1 := Int.floor_le T₂
  have hf2 := Int.lt_floor_add_one T₂
  have hAcast : (A : ℝ) = ((⌈T₁⌉ : ℤ) : ℝ) + 4 * ((K : ℝ) + 3) + 1 := by
    rw [hA]; push_cast; ring
  have hBcast : (B : ℝ) = ((⌊T₂⌋ : ℤ) : ℝ) - 4 * ((K : ℝ) + 3) - 1 := by
    rw [hB]; push_cast; ring
  have hKbig : (K : ℝ) ≤ U / 1000 := hKL.trans hsm
  have hAB : A ≤ B := by
    have : (A : ℝ) ≤ B := by
      rw [hAcast, hBcast]
      linarith only [hc2, hf2, hT₁.2, hT₂.1, hKbig, hU1000]
    exact_mod_cast this
  refine ⟨A, B, ?_, ?_, ?_, ?_, hAB, fun τ₀ hτ₀ hτ₀le => ?_⟩
  · rw [hAcast]
    linarith only [hc1, hT₁.1, Nat.cast_nonneg (α := ℝ) K]
  · rw [hAcast]
    linarith only [hc2, hT₁.2, hKL, hL21]
  · rw [hBcast]
    linarith only [hf2, hT₂.1, hKL, hL21]
  · rw [hBcast]
    linarith only [hf1, hT₂.2, Nat.cast_nonneg (α := ℝ) K]
  · have hL8 : 8 ≤ L := by linarith only [hL21]
    have hAlow : X₀ ≤ ((A - 4 * ((K : ℤ) + 3) : ℤ) : ℝ) := by
      have : ((A - 4 * ((K : ℤ) + 3) : ℤ) : ℝ) = ((⌈T₁⌉ : ℤ) : ℝ) + 1 := by
        rw [hA]; push_cast; ring
      rw [this]
      linarith only [hc1, hT₁.1, hUX]
    have hBup : ((B + 4 * ((K : ℤ) + 3) : ℤ) : ℝ) ≤ U := by
      have : ((B + 4 * ((K : ℤ) + 3) : ℤ) : ℝ) = ((⌊T₂⌋ : ℤ) : ℝ) - 1 := by
        rw [hB]; push_cast; ring
      rw [this]
      linarith only [hf1, hT₂.2, hUpos]
    have hb := hbudget U A B K hL8 hAB hAlow hBup τ₀ hτ₀ hτ₀le
    have hA₂ : T₁ + 1 ≤ ((A - 4 * ((K : ℤ) + 2) : ℤ) : ℝ) := by
      have : ((A - 4 * ((K : ℤ) + 2) : ℤ) : ℝ) = ((⌈T₁⌉ : ℤ) : ℝ) + 5 := by
        rw [hA]; push_cast; ring
      rw [this]
      linarith only [hc1]
    have hB₂ : ((B + 4 * ((K : ℤ) + 2) : ℤ) : ℝ) ≤ T₂ - 1 := by
      have : ((B + 4 * ((K : ℤ) + 2) : ℤ) : ℝ) = ((⌊T₂⌋ : ℤ) : ℝ) - 5 := by
        rw [hB]; push_cast; ring
      rw [this]
      linarith only [hf1]
    have hmom := hblock _ _ hA₂ hB₂
    -- the size term
    set c : ℝ := ((B - A + 8 * ((K : ℤ) + 3) + 1 : ℤ) : ℝ) with hc
    have hcU : c ≤ U := by
      have : c = ((⌊T₂⌋ : ℤ) : ℝ) - ((⌈T₁⌉ : ℤ) : ℝ) - 1 := by
        rw [hc, hA, hB]; push_cast; ring
      rw [this]
      linarith only [hf1, hc1, hT₁.1, hT₂.2, hUpos]
    have hpow : (1 / 2 : ℝ) ^ K * L ^ 4 ≤ 1 := by
      have h1 : L ^ 4 ≤ ((K : ℝ) + 1) ^ 4 := pow_le_pow_left₀ hLpos.le hLK.le 4
      have h2 := pow_four_le_two_pow hK20
      have h3 : (1 / 2 : ℝ) ^ K * 2 ^ K = 1 := by
        rw [← mul_pow]
        norm_num
      have h4 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left (h1.trans h2) h4, h3]
    have hsize : (1 / 2 : ℝ) ^ K * (c * L) ≤ U / L ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      have h5 : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
      have h6 : (1 / 2 : ℝ) ^ K * (c * L) * L ^ 3 = c * ((1 / 2 : ℝ) ^ K * L ^ 4) := by ring
      rw [h6]
      by_cases hcn : 0 ≤ c
      · calc c * ((1 / 2 : ℝ) ^ K * L ^ 4) ≤ c * 1 := mul_le_mul_of_nonneg_left hpow hcn
          _ = c := mul_one c
          _ ≤ U := hcU
      · have : c * ((1 / 2 : ℝ) ^ K * L ^ 4) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_le.mp hcn).le (by positivity)
        linarith only [this, hUpos]
    have hP : 0 ≤ 1 / τ₀ + L := by positivity
    have hsum : blockObs uQuartic (A - 4 * ((K : ℤ) + 2)) (B + 4 * ((K : ℤ) + 2)) 0 +
        (1 / 2 : ℝ) ^ K * (c * L) ≤ (C₁ + 1) * (U / L ^ 3) := by
      have : C₁ * U / L ^ 3 = C₁ * (U / L ^ 3) := by ring
      rw [this] at hmom
      linarith only [hmom, hsize]
    have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC₀.le hP)
    calc _ ≤ _ := hb
      _ ≤ C₀ * (1 / τ₀ + L) * ((C₁ + 1) * (U / L ^ 3)) := hmul
      _ = _ := by ring

/-! ## Nonreal time -/

/-- The heats at which `H_s` has a nonreal zero over the core of the window at height `j`. -/
def nonrealTimes (j : ℤ) : Set ℝ :=
  {s | 0 < s ∧ ∃ z : ℂ, riemannHeat s z = 0 ∧ z.im ≠ 0 ∧ |z.re - j| ≤ 1 / 2}

/-- A nonreal zero over the core gives `N_j ≥ 2`: the zero and its conjugate each count once. -/
theorem two_le_windowObs_of_mem {j : ℤ} {s : ℝ} (hs : s ∈ nonrealTimes j) :
    2 ≤ windowObs uNonreal j s := by
  classical
  obtain ⟨hs0, z, hz, him, hre⟩ := hs
  have hsum := summable_heatLocalizedZeroObservable (t := s) hasCompactSupport_w₀ uNonreal j hs0.le
  have hconj : riemannHeat s ((starRingEnd ℂ) z) = 0 := by
    rw [riemannHeat_conj hs0.le, hz, map_zero]
  have hne : z ≠ (starRingEnd ℂ) z := fun h => him (Complex.conj_eq_iff_im.mp h.symm)
  have hterm (w : ℂ) (hw : riemannHeat s w = 0) (hwim : w.im ≠ 0) (hwre : |w.re - j| ≤ 1 / 2) :
      1 ≤ (zeroMult (riemannHeat s) w : ℝ) * (w₀ (w.re - j) * uNonreal w.im) := by
    have hm : (1 : ℝ) ≤ zeroMult (riemannHeat s) w := by
      exact_mod_cast one_le_zeroMult_riemannHeat hs0.le hw
    rw [w₀_eq_one hwre]
    simp only [uNonreal, if_neg hwim, mul_one]
    exact hm
  have hle := hsum.sum_le_tsum {z, (starRingEnd ℂ) z} (fun w _ =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (w₀_nonneg _) (uNonreal_nonneg _)))
  rw [Finset.sum_pair hne] at hle
  have h1 := hterm z hz him hre
  have h2 := hterm _ hconj (by simpa using him) (by simpa using hre)
  have hdef : windowObs uNonreal j s = ∑' w : ℂ, (zeroMult (riemannHeat s) w : ℝ) *
      (w₀ (w.re - j) * uNonreal w.im) := rfl
  rw [hdef]
  linarith only [hle, h1, h2]

/-- Markov: the time spent nonreal in `(τ₀, τ₁]` is at most half the integrated count. -/
theorem volume_nonrealTimes_inter_le {j : ℤ} {τ₀ τ₁ : ℝ} (hτ : τ₀ ≤ τ₁)
    (hI : IntervalIntegrable (windowObs uNonreal j) volume τ₀ τ₁) :
    volume (nonrealTimes j ∩ Ioc τ₀ τ₁) ≤
      ENNReal.ofReal ((1 / 2) * ∫ s in τ₀..τ₁, windowObs uNonreal j s) := by
  set μ : Measure ℝ := volume.restrict (Ioc τ₀ τ₁) with hμ
  have hint : Integrable (windowObs uNonreal j) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ).mp hI
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun s => windowObs_nonneg uNonreal_nonneg j s) hint 2
  rw [← intervalIntegral.integral_of_le hτ] at hmarkov
  have hsub : nonrealTimes j ∩ Ioc τ₀ τ₁ ⊆ {s | 2 ≤ windowObs uNonreal j s} ∩ Ioc τ₀ τ₁ :=
    fun s hs => ⟨two_le_windowObs_of_mem hs.1, hs.2⟩
  have hμS : μ {s | 2 ≤ windowObs uNonreal j s} = volume ({s | 2 ≤ windowObs uNonreal j s} ∩ Ioc τ₀ τ₁) :=
    Measure.restrict_apply' measurableSet_Ioc
  refine (measure_mono hsub).trans ?_
  rw [← hμS]
  have hfin : μ {s | 2 ≤ windowObs uNonreal j s} ≠ ⊤ := by
    have : IsFiniteMeasure μ := by
      rw [hμ]
      exact ⟨by simp⟩
    exact measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have : μ.real {s | 2 ≤ windowObs uNonreal j s} = (μ {s | 2 ≤ windowObs uNonreal j s}).toReal := rfl
  rw [← this]
  linarith only [hmarkov]

/-- Above the two-thirds horizon a window at height `≍ U` is real: all nonreal time lies below `1/log U`. -/
theorem eventually_nonrealTimes_subset :
    ∀ᶠ U : ℝ in atTop, ∀ j : ℤ, U / 8 ≤ j → nonrealTimes j ⊆ Ioo 0 (1 / Real.log U) := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_twoThirds (ε := 1 / 12) (by norm_num)
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hgrow : ∀ᶠ U : ℝ in atTop, 3 / 4 * Real.log U + Real.log (32 * Real.pi) ≤ Real.log U := by
    filter_upwards [hlog.eventually_ge_atTop (4 * Real.log (32 * Real.pi))] with U hU
    linarith only [hU]
  filter_upwards [hgrow, hlog.eventually_ge_atTop 8, eventually_ge_atTop (8 * (|X₀| + 2)),
    eventually_gt_atTop (0 : ℝ)] with U hg hL hUX hU0 j hj s hs
  obtain ⟨hs0, z, hz, him, hre⟩ := hs
  refine ⟨hs0, ?_⟩
  by_contra hge
  have hsge : 1 / Real.log U ≤ s := not_lt.mp hge
  have hLpos : 0 < Real.log U := by linarith only [hL]
  apply him
  rcases le_or_gt (1 / 8) s with h8 | h8
  · exact riemannHeat_zeros_real h8 hz
  · have hzre := abs_le.mp hre
    have hzlow : U / 8 - 1 / 2 ≤ z.re := by linarith only [hj, hzre.1]
    have hzabs : |z.re| = z.re := abs_of_nonneg (by linarith only [hzlow, hUX, abs_nonneg X₀])
    refine hX₀ s hs0 h8.le z hz ?_ ?_
    · rw [hzabs]
      linarith only [hzlow, hUX, le_abs_self X₀, abs_nonneg X₀]
    · rw [hzabs]
      have hexp : (2 / 3 + 1 / 12) / s ≤ 3 / 4 * Real.log U := by
        rw [div_le_iff₀ hs0]
        have h1 : 1 ≤ s * Real.log U := by
          have := mul_le_mul_of_nonneg_right hsge hLpos.le
          rwa [div_mul_cancel₀ _ hLpos.ne'] at this
        nlinarith only [h1]
      have hpi : 0 < 32 * Real.pi := by positivity
      have hbound : 2 * Real.pi * Real.exp ((2 / 3 + 1 / 12) / s) ≤ U / 16 := by
        have h2 : Real.exp ((2 / 3 + 1 / 12) / s) * (32 * Real.pi) ≤ U := by
          calc _ ≤ Real.exp (3 / 4 * Real.log U) * Real.exp (Real.log (32 * Real.pi)) := by
                rw [Real.exp_log hpi]
                gcongr
            _ = Real.exp (3 / 4 * Real.log U + Real.log (32 * Real.pi)) := by rw [Real.exp_add]
            _ ≤ Real.exp (Real.log U) := Real.exp_le_exp.mpr hg
            _ = U := Real.exp_log hU0
        nlinarith only [h2]
      linarith only [hbound, hzlow, hUX, abs_nonneg X₀]

/-- **Near-line clustering in heat time.** For each `ε > 0`, among `≍ U` unit windows at heights `≍ U` at most `C_ε U/log U`
spend total heat time more than `ε/log U` with a nonreal zero over their core. -/
theorem exists_card_nonrealTime_gt_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ᶠ U : ℝ in atTop, ∃ A B : ℤ, U / 4 ≤ A ∧ (A : ℝ) ≤ U / 4 + 8 * Real.log U ∧
      U / 2 - 8 * Real.log U ≤ B ∧ (B : ℝ) ≤ U / 2 ∧ A ≤ B ∧ ∀ Bad : Finset ℤ, Bad ⊆ Finset.Icc A B →
        (∀ j ∈ Bad, ENNReal.ofReal (ε / Real.log U) < volume (nonrealTimes j)) →
        (Bad.card : ℝ) ≤ C * (U / Real.log U) := by
  obtain ⟨C₀, hC₀, hbudget⟩ := exists_sum_nonrealTime_le_selberg
  obtain ⟨K₀, -, X₁, hX₁, hlaws⟩ := exists_window_laws
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  refine ⟨C₀ * (2 / ε' + 1) / ε, by positivity, ?_⟩
  filter_upwards [hbudget, eventually_nonrealTimes_subset, Real.tendsto_log_atTop.eventually_ge_atTop 8,
    eventually_ge_atTop (8 * (X₁ + 1)), eventually_gt_atTop (0 : ℝ)] with U hU hsub hL8 hUX hU0
  obtain ⟨A, B, hA1, hA2, hB1, hB2, hAB, hsum⟩ := hU
  refine ⟨A, B, hA1, hA2, hB1, hB2, hAB, fun Bad hBad hbig => ?_⟩
  set L := Real.log U with hLdef
  have hL : 0 < L := by linarith only [hL8]
  set τ₁ : ℝ := 1 / L with hτ₁
  set τ₀ : ℝ := ε' / (2 * L) with hτ₀
  have hτ₀pos : 0 < τ₀ := by positivity
  have hτ₀le : τ₀ ≤ τ₁ := by
    rw [hτ₀, hτ₁, div_le_div_iff₀ (by positivity) hL]
    nlinarith only [hε'1, hL]
  have hτ₁8 : τ₁ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hL8
  have hτ₁L : τ₁ * L = 1 := by rw [hτ₁]; field_simp
  have hS := hsum τ₀ hτ₀pos hτ₀le
  have hP : 1 / τ₀ + L = L * (2 / ε' + 1) := by
    rw [hτ₀]
    field_simp
  rw [hP] at hS
  -- each bad window has large integrated count
  have hone (j : ℤ) (hj : j ∈ Bad) : ε / L ≤ ∫ s in τ₀..τ₁, windowObs uNonreal j s := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hBad hj)
    have hj1 : (A : ℝ) ≤ j := by exact_mod_cast h1
    have hj2 : (j : ℝ) ≤ B := by exact_mod_cast h2
    have hjpos : (0 : ℝ) < j := by linarith only [hA1, hj1, hU0]
    have hlog : Real.log j ≤ L := Real.log_le_log hjpos (by linarith only [hj2, hB2, hU0])
    have hX : X₁ ≤ j := by linarith only [hA1, hj1, hUX, hX₁]
    obtain ⟨hI, -, -⟩ := hlaws j hX τ₀ τ₁ hτ₀pos.le hτ₀le hτ₁8
      ((mul_le_mul_of_nonneg_left hlog (by positivity)).trans hτ₁L.le)
    have hsplit : nonrealTimes j ⊆ Ioc 0 τ₀ ∪ (nonrealTimes j ∩ Ioc τ₀ τ₁) := by
      intro s hs
      have hs' := hsub j (by linarith only [hA1, hj1, hU0]) hs
      rcases le_or_gt s τ₀ with h | h
      · exact Or.inl ⟨hs'.1, h⟩
      · exact Or.inr ⟨hs, h, hs'.2.le⟩
    have hvol := (measure_mono (μ := (volume : Measure ℝ)) hsplit).trans (measure_union_le _ _)
    have hM := volume_nonrealTimes_inter_le (j := j) hτ₀le hI
    have hIoc : volume (Ioc 0 τ₀) = ENNReal.ofReal τ₀ := by
      rw [Real.volume_Ioc, sub_zero]
    have hb := (hbig j hj).trans_le hvol
    rw [hIoc] at hb
    have hb2 := hb.trans_le (add_le_add_right hM _)
    have hnn : 0 ≤ (1 / 2) * ∫ s in τ₀..τ₁, windowObs uNonreal j s := by
      refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hτ₀le fun s _ => ?_)
      exact windowObs_nonneg uNonreal_nonneg j s
    rw [← ENNReal.ofReal_add hτ₀pos.le hnn] at hb2
    have hb3 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hb2
    have hτ₀ε : τ₀ ≤ ε / (2 * L) := by
      rw [hτ₀]
      exact div_le_div_of_nonneg_right hε'le (by positivity)
    have heq : ε / L = 2 * (ε / (2 * L)) := by
      field_simp
    linarith only [hb3, hτ₀ε, heq]
  have hsumBad : (Bad.card : ℝ) * (ε / L) ≤ ∑ j ∈ Bad, ∫ s in τ₀..τ₁, windowObs uNonreal j s := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hone
  have hsumBad2 : ∑ j ∈ Bad, ∫ s in τ₀..τ₁, windowObs uNonreal j s ≤
      ∑ j ∈ Finset.Icc A B, ∫ s in τ₀..τ₁, windowObs uNonreal j s :=
    Finset.sum_le_sum_of_subset_of_nonneg hBad fun j _ _ =>
      intervalIntegral.integral_nonneg hτ₀le fun s _ => windowObs_nonneg uNonreal_nonneg j s
  have htot := hsumBad.trans (hsumBad2.trans hS)
  have heq : C₀ * (L * (2 / ε' + 1)) * (U / L ^ 3) =
      (C₀ * (2 / ε' + 1) / ε * (U / L)) * (ε / L) := by
    field_simp
  rw [heq] at htot
  exact le_of_mul_le_mul_right htot (by positivity)

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
