import GaloisForLFunctions.RHTower.Sieve.HarmanWindowTupleCounts
import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardPrimePairSum

/-!
# The prime-cofactor and unit-cofactor parts of the discarded pair tail

Over the window `(y, y(1+θ)]`, the discarded pair tail `D₂` counts `n = q₁q₂m`; the parts with
`m` prime (`≥ q₂`) and `m = 1` are prime counts in cofactor windows over the discarded pairs.
The prime part is at most `(1+η)(θy/log y)(0.8896 + η)` (the pairs lie in the discarded region of
`harmanDiscardPrimeDensity`), and the unit part is at most `(1+η)(θy/log y) · 3(5κ + η)` (then
`q₁, q₂` are both within `y^{±κ}` of `√y`).
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- Logarithmic coordinates of a discarded pair whose cofactor window reaches `q₂`. -/
theorem harmanDiscardPair_logScale {κ y θ : ℝ} {z Q D E q₁ q₂ : ℕ} (hy : 1 < y)
    (hθ1 : θ ≤ 1) (hyκ : 2 ≤ y ^ κ) (hP : HarmanWindowScale κ y z Q D E)
    (hq : (q₁, q₂) ∈ harmanDiscardPairSet z Q D E)
    (hdr : ((q₁ * q₂ : ℕ) : ℝ) * q₂ ≤ y * (1 + θ)) :
    2 / 11 < log q₂ / log y ∧ log q₂ / log y < log q₁ / log y ∧
      log q₁ / log y ≤ 1 / 2 + κ ∧ log q₁ / log y + 2 * (log q₂ / log y) ≤ 1 + κ ∧
      (1 / 4 - κ < log q₁ / log y ∨ 1 - κ < log q₁ / log y + 4 * (log q₂ / log y)) := by
  simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hq
  obtain ⟨⟨⟨hz1, hQ1⟩, hz2, hQ2⟩, hp1, hp2, h21, hdisc⟩ := hq
  have hly : 0 < log y := Real.log_pos hy
  have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
  have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
  have hy0 : 0 < y := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lt_logScale_of_rpow_lt hy (lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz2))
  · exact div_lt_div_of_pos_right (Real.log_lt_log hq2 (by exact_mod_cast h21)) hly
  · exact logScale_le_of_le_rpow hy hq1 ((by exact_mod_cast hQ1.le : (q₁ : ℝ) ≤ Q).trans hP.Q_le)
  · have h2y : y * (1 + θ) ≤ y ^ (1 + κ) := by
      rw [Real.rpow_add hy0, Real.rpow_one]; nlinarith
    have hm : (q₁ : ℝ) * q₂ ^ 2 ≤ y ^ (1 + κ) := by
      have : ((q₁ * q₂ : ℕ) : ℝ) * q₂ = (q₁ : ℝ) * q₂ ^ 2 := by push_cast; ring
      linarith
    have := logScale_le_of_le_rpow hy (by positivity) hm
    rw [Real.log_mul hq1.ne' (by positivity), Real.log_pow, add_div] at this
    push_cast at this
    linarith [show (2 : ℝ) * log q₂ / log y = 2 * (log q₂ / log y) by ring]
  · by_cases hD : q₁ < D
    · have hE : E ≤ q₁ * q₂ ^ (4 : ℕ) := by
        by_contra h; exact hdisc ⟨hD, by omega⟩
      right
      have hE' : y ^ (1 - κ) < (q₁ : ℝ) * q₂ ^ 4 :=
        lt_of_lt_of_le hP.E_gt (by exact_mod_cast hE)
      have := lt_logScale_of_rpow_lt hy hE'
      rw [Real.log_mul hq1.ne' (by positivity), Real.log_pow, add_div] at this
      push_cast at this
      linarith [show (4 : ℝ) * log q₂ / log y = 4 * (log q₂ / log y) by ring]
    · left
      exact lt_logScale_of_rpow_lt hy (lt_of_lt_of_le hP.D_gt (by exact_mod_cast not_lt.mp hD))

/-- **The prime-cofactor part of the discarded pair tail.** -/
theorem eventually_sum_harmanDiscardPair_primeCount_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
          (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2)) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)) qq.2 : ℝ)
        ≤ (1 + η) * (θ * y / log y) * (8896 / 10000 + η) := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2, eventually_harmanPrimePairSum_le hη,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000000)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 11)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hsum hyκ hy211 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  set S₂ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + κ) / 3 : ℝ)⌋₊).filter Nat.Prime with hS₂
  set S₁ : ℕ → Finset ℕ := fun q₂ => (Finset.Ioc ⌊y ^ harmanDiscardLow κ (log q₂ / log y)⌋₊
    ⌊y ^ harmanDiscardHigh κ (log q₂ / log y)⌋₊).filter Nat.Prime with hS₁
  set G : ℕ × ℕ → ℝ := fun t => C * (1 / (t.2 : ℝ) *
    ((1 / (1 - log t.1 / log y - log t.2 / log y)) / t.1)) with hG
  have key : ∑ qq ∈ harmanDiscardPairSet z Q D E,
      (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2)) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)) qq.2 : ℝ)
      ≤ ∑ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, G (q₁, q₂) := by
    refine sum_pairs_le_nested (fun q₂ hq₂ q₁ hq₁ => ?_) (fun t ht => ?_)
    · -- nonnegativity on the region
      have hq₂p := (Finset.mem_filter.1 hq₂).2
      have hq₁p := (Finset.mem_filter.1 hq₁).2
      have h2 := (mem_Ioc_floor_rpow_iff hy1 hq₂p.pos).1 (Finset.mem_filter.1 hq₂).1
      have h1 := (mem_Ioc_floor_rpow_iff hy1 hq₁p.pos).1 (Finset.mem_filter.1 hq₁).1
      have hhi : harmanDiscardHigh κ (log q₂ / log y) ≤ 1 + κ - 2 * (log q₂ / log y) :=
        min_le_right _ _
      have hpos : 0 < 1 - log q₁ / log y - log q₂ / log y := by
        simp only [hκ] at h1 h2 hhi ⊢; linarith [h1.2, h2.1]
      have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hq₁p.pos
      have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hq₂p.pos
      simp only [hG]
      positivity
    · obtain ⟨q₁, q₂⟩ := t
      simp only
      have hmem := ht
      simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ico] at ht
      have hp1 := ht.2.1
      have hp2 := ht.2.2.1
      have hd : 0 < q₁ * q₂ := Nat.mul_pos hp1.pos hp2.pos
      by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂)) (⌊y * (1 + θ)⌋₊ / (q₁ * q₂)) q₂ = 0
      · rw [h0, Nat.cast_zero]
        split_ifs with hreg
        · exact (by
            obtain ⟨hq₂, hq₁⟩ := hreg
            have h2 := (mem_Ioc_floor_rpow_iff hy1 hp2.pos).1 (Finset.mem_filter.1 hq₂).1
            have h1 := (mem_Ioc_floor_rpow_iff hy1 hp1.pos).1 (Finset.mem_filter.1 hq₁).1
            have hhi : harmanDiscardHigh κ (log q₂ / log y) ≤ 1 + κ - 2 * (log q₂ / log y) :=
              min_le_right _ _
            have hpos : 0 < 1 - log q₁ / log y - log q₂ / log y := by
              simp only [hκ] at h1 h2 hhi ⊢; linarith [h1.2, h2.1]
            have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
            have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
            simp only [hG]
            positivity)
        · exact le_rfl
      · have hdrN := mul_le_of_primeCountAbove_ne_zero hd h0
        have hb : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
        have hdr : ((q₁ * q₂ : ℕ) : ℝ) * q₂ ≤ y * (1 + θ) := by
          have : (((q₁ * q₂) * q₂ : ℕ) : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hdrN
          push_cast at this ⊢; linarith
        obtain ⟨hα2, h21, hα1Q, hα12, hdisc⟩ :=
          harmanDiscardPair_logScale hy1 hθ1 hyκ hP hmem hdr
        have hreg : q₂ ∈ S₂ ∧ q₁ ∈ S₁ q₂ := by
          refine ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp2.pos).2 ⟨hα2, ?_⟩, hp2⟩,
            Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp1.pos).2 ⟨?_, ?_⟩, hp1⟩⟩
          · linarith
          · refine max_lt h21 ?_
            rcases hdisc with h | h
            · exact lt_of_le_of_lt (min_le_left _ _) h
            · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
          · exact le_min hα1Q (by linarith)
        rw [if_pos hreg]
        have hz2 : y ^ (1 / 6 : ℝ) ≤ (q₂ : ℝ) := by
          have h611 : y ^ (1 / 6 : ℝ) ≤ y ^ (2 / 11 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num)
          have := hP.z_gt
          have hz := ht.1.2.1
          have : (z : ℝ) ≤ q₂ := by exact_mod_cast hz
          linarith
        have hcount := hwin θ hθ hθ1 (q₁ * q₂) q₂ hd hz2 hdr
        have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
        have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
        have hdy : ((q₁ * q₂ : ℕ) : ℝ) < y := by
          have h2 : (2 : ℝ) < q₂ := by
            have : (z : ℝ) ≤ q₂ := by exact_mod_cast ht.1.2.1
            linarith [hP.z_gt]
          have hd0 : (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) := by exact_mod_cast hd
          have : ((q₁ * q₂ : ℕ) : ℝ) * 2 < y * (1 + θ) :=
            lt_of_lt_of_le (mul_lt_mul_of_pos_left h2 hd0) hdr
          nlinarith
        rw [div_log_div_eq hy1 hd hdy] at hcount
        refine hcount.trans (le_of_eq ?_)
        simp only [hG, hC]
        rw [Nat.cast_mul, Real.log_mul hq1.ne' hq2.ne']
        ring
  refine key.trans ?_
  have hinner : ∀ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, G (q₁, q₂) =
      C * (1 / (q₂ : ℝ) * harmanPrimeInnerSum y κ (log q₂ / log y)) := by
    intro q₂ _
    simp only [hG, hS₁, harmanPrimeInnerSum, primeScaleSum]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum hC0

/-- **The unit-cofactor part of the discarded pair tail**: `n = q₁q₂` itself lies in the window. -/
theorem eventually_sum_harmanDiscardPair_unit_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
          (if 1 ∈ Finset.Ioc (⌊y⌋₊ / (qq.1 * qq.2)) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))
            then (1 : ℝ) else 0)
        ≤ (1 + η) * (θ * y / log y) * (3 * (5 / 1000000 + η)) := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2,
    eventually_sum_prime_inv_rpow_le (a := 1 / 2 - 1 / 1000000) (b := 1 / 2 + 1 / 1000000)
      (by norm_num) (by norm_num) hη,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2 - 1 / 1000000)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hmert hy2 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  set a := ⌊y⌋₊ with ha
  set b := ⌊y * (1 + θ)⌋₊ with hb
  set S₂ := (Finset.Ioc ⌊y ^ (1 / 2 - κ)⌋₊ ⌊y ^ (1 / 2 + κ)⌋₊).filter Nat.Prime with hS₂
  set S₁ : ℕ → Finset ℕ := fun q₂ =>
    (Finset.Ioc (a / q₂) (b / q₂)).filter (fun r => r.Prime ∧ q₂ ≤ r) with hS₁
  have key : ∑ qq ∈ harmanDiscardPairSet z Q D E,
      (if 1 ∈ Finset.Ioc (a / (qq.1 * qq.2)) (b / (qq.1 * qq.2)) then (1 : ℝ) else 0)
      ≤ ∑ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, (fun _ : ℕ × ℕ => (1 : ℝ)) (q₁, q₂) := by
    refine sum_pairs_le_nested (G := fun _ : ℕ × ℕ => (1 : ℝ)) (fun _ _ _ _ => zero_le_one)
      (fun t ht => ?_)
    obtain ⟨q₁, q₂⟩ := t
    simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at ht
    obtain ⟨⟨⟨_, hQ1⟩, hz2, _⟩, hp1, hp2, h21, _⟩ := ht
    have hd : 0 < q₁ * q₂ := Nat.mul_pos hp1.pos hp2.pos
    split_ifs with h1 hreg hreg
    · exact le_rfl
    · exfalso; apply hreg
      rw [Finset.mem_Ioc] at h1
      have had : a < q₁ * q₂ := by
        have := (Nat.div_lt_iff_lt_mul hd).1 h1.1; omega
      have hdb : q₁ * q₂ ≤ b := by
        have := (Nat.le_div_iff_mul_le hd).1 h1.2; omega
      have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
      have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
      refine ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp2.pos).2 ⟨?_, ?_⟩, hp2⟩, ?_⟩
      · -- `q₁ q₂ > y` and `q₁ ≤ y^{1/2+κ}`
        have hyd : y < (q₁ : ℝ) * q₂ := by
          have h' : a + 1 ≤ q₁ * q₂ := had
          have : y < (a : ℝ) + 1 := Nat.lt_floor_add_one y
          have h'' : ((a + 1 : ℕ) : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by exact_mod_cast h'
          push_cast at h''; linarith
        have h1' : log q₁ / log y ≤ 1 / 2 + κ :=
          logScale_le_of_le_rpow hy1 hq1
            ((by exact_mod_cast hQ1.le : (q₁ : ℝ) ≤ Q).trans hP.Q_le)
        have h2' : 1 < log ((q₁ : ℝ) * q₂) / log y := by
          rw [lt_div_iff₀ hly, one_mul]; exact Real.log_lt_log hy0 hyd
        rw [Real.log_mul hq1.ne' hq2.ne', add_div] at h2'
        linarith
      · exact logScale_le_of_le_rpow hy1 hq2
          ((by exact_mod_cast (h21.trans hQ1).le : (q₂ : ℝ) ≤ Q).trans hP.Q_le)
      · refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, hp1, h21.le⟩
        · exact (Nat.div_lt_iff_lt_mul hp2.pos).2 had
        · exact (Nat.le_div_iff_mul_le hp2.pos).2 hdb
    · exact zero_le_one
    · exact le_rfl
  refine key.trans ?_
  have hcount : ∀ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, (fun _ : ℕ × ℕ => (1 : ℝ)) (q₁, q₂) ≤
      C * 3 * (1 / (q₂ : ℝ)) := by
    intro q₂ hq₂
    have hp2 := (Finset.mem_filter.1 hq₂).2
    have hα := (mem_Ioc_floor_rpow_iff hy1 hp2.pos).1 (Finset.mem_filter.1 hq₂).1
    have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
    have hsum1 : ∑ q₁ ∈ S₁ q₂, (fun _ : ℕ × ℕ => (1 : ℝ)) (q₁, q₂) =
        (primeCountAbove (a / q₂) (b / q₂) q₂ : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hS₁, primeCountAbove]
    rw [hsum1]
    by_cases h0 : primeCountAbove (a / q₂) (b / q₂) q₂ = 0
    · rw [h0, Nat.cast_zero]; positivity
    have hdrN := mul_le_of_primeCountAbove_ne_zero hp2.pos h0
    have hbr : (b : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
    have hdr : (q₂ : ℝ) * q₂ ≤ y * (1 + θ) := by
      have : ((q₂ * q₂ : ℕ) : ℝ) ≤ b := by exact_mod_cast hdrN
      push_cast at this; linarith
    have hlow : y ^ (1 / 2 - κ) < q₂ := by
      have := hα.1
      rw [lt_div_iff₀ hly] at this
      rw [← Real.exp_log hq2, Real.rpow_def_of_pos hy0, Real.exp_lt_exp]; linarith
    have h6 : y ^ (1 / 6 : ℝ) ≤ q₂ :=
      (Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num)).trans hlow.le
    have hc1 := hwin θ hθ hθ1 q₂ q₂ hp2.pos h6 hdr
    have hqy : (q₂ : ℝ) < y := by
      have : (2 : ℝ) < q₂ := lt_of_le_of_lt hy2 hlow
      nlinarith
    rw [div_log_div_eq hy1 hp2.pos hqy] at hc1
    refine hc1.trans ?_
    have hden : 1 / 2 - κ ≤ 1 - log q₂ / log y := by linarith [hα.2]
    have hinv : 1 / (1 - log q₂ / log y) ≤ 3 := by
      rw [div_le_iff₀ (by simp only [hκ] at hden ⊢; linarith)]
      simp only [hκ] at hden ⊢; linarith
    have : 1 / (q₂ : ℝ) * (1 / (1 - log q₂ / log y)) ≤ 1 / q₂ * 3 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    calc (1 + η) * (θ * y / log y * (1 / q₂ * (1 / (1 - log q₂ / log y))))
        = C * (1 / q₂ * (1 / (1 - log q₂ / log y))) := by rw [hC]; ring
      _ ≤ C * (1 / q₂ * 3) := mul_le_mul_of_nonneg_left this hC0
      _ = C * 3 * (1 / (q₂ : ℝ)) := by ring
  refine (Finset.sum_le_sum hcount).trans ?_
  rw [← Finset.mul_sum]
  have hlog : log ((1 / 2 + 1 / 1000000) / (1 / 2 - 1 / 1000000) : ℝ) ≤ 5 / 1000000 := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (1 / 2 + 1 / 1000000) / (1 / 2 - 1 / 1000000) by norm_num)
    norm_num at this ⊢; linarith
  have hm : ∑ p ∈ S₂, 1 / (p : ℝ) ≤ 5 / 1000000 + η := by
    have := hmert; simp only [hS₂, hκ] at this ⊢; linarith
  calc C * 3 * ∑ p ∈ S₂, 1 / (p : ℝ) ≤ C * 3 * (5 / 1000000 + η) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (3 * (5 / 1000000 + η)) := by ring

end

end RHTower.Sieve
