import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge
import GaloisForLFunctions.RHTower.XiCriticalZeroSeparatedNodes

/-!
# Separated critical zeros at linear height

**Theorem** (`exists_separated_Xi_zeros_linear`).  There is `K ≥ 1` such that for every `d` there
are `d + 1` real zeros `t_0, …, t_d` of `Ξ` with `1 ≤ t_i ≤ K (d + 1)` and `|t_i − t_j| ≥ 1` for
`i ≠ j`.

Proof.  The unconditional Montgomery–Taylor proportion (pinned `Zeta23`, transported as
`lamzouri_montgomeryTaylor_simpleCritical_epsilon`) gives at least `(H − ε) N(T)` simple critical
zeros in `(0, T]`, with `H = 3/2 − cot(1/√2)/√2 > 1/2` (`HD_one_gt_half`).  With the
Riemann–von Mangoldt asymptotic `N(T) ∼ T log T/(2π)` this leaves `≥ c₀ T log T` simple critical
zeros in `(T, 2T]`.  A unit interval holds at most `≍ log T` of them (`card_filter_floor_eq_le`), so
`≳ T` unit bins are occupied.  One zero per occupied bin of one parity gives a `1`-separated
family (`exists_separated_of_card_image_floor`).  `T ≍ d` suffices.
-/

open Complex Finset

namespace RHTower

noncomputable section

/-- The Montgomery–Taylor proportion exceeds `1/2`: `3/2 − cot(1/√2)/√2 > 1/2`. -/
theorem HD_one_gt_half : (1 : ℝ) / 2 < Zeta23.ThmD.HD 1 := by
  rw [Zeta23.ThmD.HD_one]
  set x := (Real.sqrt 2)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hx1 : x < 1 := by rw [hx]; exact inv_lt_one_of_one_lt₀ hs2
  have hpi := Real.pi_gt_three
  have hxpi : x < Real.pi / 2 := by linarith
  have htan := Real.lt_tan hx0 hxpi
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  have h : x * (Real.cos x / Real.sin x) < 1 := by
    rw [← mul_div_assoc, div_lt_one hsin]
    exact htan
  linarith

/-- A critical zero `z` of `ξ` gives the real zero `Im z` of `Ξ`. -/
theorem Xi_im_eq_zero_of_xi_eq_zero {z : ℂ} (hre : z.re = 1 / 2) (hz : xi z = 0) : Xi z.im = 0 := by
  have h : XiC (z.im : ℂ) = xi z := by
    unfold XiC
    congr 1
    apply Complex.ext <;> simp [hre]
  rw [hz, XiC_ofReal] at h
  exact_mod_cast h

/-- **Many critical ordinates in dyadic windows.**  There are `c₀ > 0` and `T₀` such that for
`T ≥ T₀` at least `c₀ T log T` distinct ordinates `τ ∈ (T, 2T]` carry a zero of `Ξ`. -/
theorem exists_many_critical_ordinates_dyadic :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ Xi τ = 0) ∧
        c₀ * (T * Real.log T) ≤ (τS.card : ℝ) := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 2 * Zeta23.ThmD.HD 1 - 1 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by have := HD_one_gt_half; rw [hθ]; linarith
  obtain ⟨T₁, hT₁⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon (θ / 8) (by positivity)
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = θ / (8 * Real.pi * (2 + θ)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨T₂, hT₂4, hT₂⟩ := exists_xiZeroCount_close ε' hε'0
  refine ⟨θ / (4 * Real.pi), by positivity, max T₁ T₂ + 1, ?_, fun T hT => ?_⟩
  · have := le_max_right T₁ T₂; linarith
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans (by linarith)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans (by linarith)
  have hT0 : 4 ≤ T := hT₂4.trans hT2
  have h2T1 : T₁ ≤ 2 * T := by linarith
  have h2T2 : T₂ ≤ 2 * T := by linarith
  -- the simple critical zeros in `(T, 2T]`
  set A := (stripFinsetPos (2 * T)).filter
    (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) with hA
  set Sz := A.filter (fun z => T < z.im) with hSz
  have hsplit : A.card = Sz.card + (A.filter fun z => ¬ T < z.im).card :=
    (Finset.card_filter_add_card_filter_not (s := A) (fun z => T < z.im)).symm
  have hlowpart : (A.filter fun z => ¬ T < z.im) = (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) := by
    ext z
    simp only [hA, Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨hz, hc⟩, hle⟩
      obtain ⟨h1, h2, h3, -, h5⟩ := mem_stripFinsetPos.1 hz
      exact ⟨mem_stripFinsetPos.2 ⟨h1, h2, h3, hle, h5⟩, hc⟩
    · rintro ⟨hz, hc⟩
      have hzT := (mem_stripFinsetPos.1 hz)
      refine ⟨⟨mem_stripFinsetPos.2 ⟨hzT.1, hzT.2.1, hzT.2.2.1, by linarith [hzT.2.2.2.1],
        hzT.2.2.2.2⟩, hc⟩, hzT.2.2.2.1⟩
  have hAcard : (A.card : ℝ) = xiSimpleCriticalZeroCount (2 * T) := by
    rw [hA]; rfl
  have hlowcard : ((A.filter fun z => ¬ T < z.im).card : ℝ) = xiSimpleCriticalZeroCount T := by
    rw [hlowpart]; rfl
  -- the counts
  have hN1 := hT₁ (2 * T) h2T1
  have hsimple_le : (xiSimpleCriticalZeroCount T : ℝ) ≤ xiPosZeroCount T := by
    have : xiSimpleCriticalZeroCount T ≤ xiPosZeroCount T := by
      unfold xiSimpleCriticalZeroCount xiPosZeroCount
      calc ((stripFinsetPos T).filter
            (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card
          = ∑ z ∈ (stripFinsetPos T).filter
              (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1),
              (analyticOrderAt xi z).toNat := by
            rw [Finset.card_eq_sum_ones]
            exact Finset.sum_congr rfl fun z hz => (Finset.mem_filter.1 hz).2.2.symm
        _ ≤ ∑ z ∈ stripFinsetPos T, (analyticOrderAt xi z).toNat :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => Nat.zero_le _
    exact_mod_cast this
  have hNT := hT₂ T hT2
  have hN2T := hT₂ (2 * T) h2T2
  rw [← (by exact_mod_cast xiPosZeroCount_eq_xiZeroCount (by linarith : (0 : ℝ) ≤ T) :
    ((xiPosZeroCount T : ℤ) : ℝ) = (xiZeroCount T : ℝ))] at hNT
  rw [← (by exact_mod_cast xiPosZeroCount_eq_xiZeroCount (by linarith : (0 : ℝ) ≤ 2 * T) :
    ((xiPosZeroCount (2 * T) : ℤ) : ℝ) = (xiZeroCount (2 * T) : ℝ))] at hN2T
  push_cast at hNT hN2T
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlog2T : Real.log T ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have hTlog : 0 < T * Real.log T := by positivity
  have hHD : 1 / 2 + 3 * θ / 8 ≤ Zeta23.ThmD.HD 1 - θ / 8 := by rw [hθ]; linarith
  -- lower bound for `N(2T)` and upper bound for `N(T)`
  have hN2low : (1 / (2 * Real.pi) - ε') * (2 * T * Real.log T) ≤ xiPosZeroCount (2 * T) := by
    have h := (abs_le.1 hN2T).1
    have hm : (1 / (2 * Real.pi) - ε') * (2 * T * Real.log T) ≤
        (1 / (2 * Real.pi) - ε') * (2 * T * Real.log (2 * T)) := by
      have hc : 0 ≤ 1 / (2 * Real.pi) - ε' := by
        rw [hε']
        rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
        have := Real.pi_pos
        nlinarith
      exact mul_le_mul_of_nonneg_left (by nlinarith) hc
    nlinarith
  have hNup : (xiPosZeroCount T : ℝ) ≤ (1 / (2 * Real.pi) + ε') * (T * Real.log T) := by
    have h := (abs_le.1 hNT).2
    linarith
  have hSzlow : (Zeta23.ThmD.HD 1 - θ / 8) * xiPosZeroCount (2 * T) - xiPosZeroCount T ≤
      (Sz.card : ℝ) := by
    have h1 : (A.card : ℝ) = Sz.card + (A.filter fun z => ¬ T < z.im).card := by
      exact_mod_cast hsplit
    rw [hAcard, hlowcard] at h1
    linarith
  have hpi := Real.pi_pos
  have hSz : θ / (4 * Real.pi) * (T * Real.log T) ≤ (Sz.card : ℝ) := by
    refine le_trans ?_ hSzlow
    have hN2' : 0 ≤ (xiPosZeroCount (2 * T) : ℝ) := Nat.cast_nonneg _
    have hstep : (1 / 2 + 3 * θ / 8) * ((1 / (2 * Real.pi) - ε') * (2 * T * Real.log T)) ≤
        (Zeta23.ThmD.HD 1 - θ / 8) * xiPosZeroCount (2 * T) := by
      have hc0 : 0 ≤ (1 / 2 + 3 * θ / 8) := by positivity
      have hHD0 : 0 ≤ Zeta23.ThmD.HD 1 - θ / 8 := by linarith
      calc (1 / 2 + 3 * θ / 8) * ((1 / (2 * Real.pi) - ε') * (2 * T * Real.log T))
          ≤ (1 / 2 + 3 * θ / 8) * xiPosZeroCount (2 * T) :=
            mul_le_mul_of_nonneg_left hN2low hc0
        _ ≤ (Zeta23.ThmD.HD 1 - θ / 8) * xiPosZeroCount (2 * T) :=
            mul_le_mul_of_nonneg_right hHD hN2'
    have hval : (1 / 2 + 3 * θ / 8) * ((1 / (2 * Real.pi) - ε') * (2 * T * Real.log T)) -
        (1 / (2 * Real.pi) + ε') * (T * Real.log T) =
        (3 * θ / (8 * Real.pi) - ε' * (2 + 3 * θ / 4)) * (T * Real.log T) := by
      field_simp
      ring
    have hε'val : ε' * (2 + θ) = θ / (8 * Real.pi) := by rw [hε']; field_simp
    have hcoef : θ / (4 * Real.pi) ≤ 3 * θ / (8 * Real.pi) - ε' * (2 + 3 * θ / 4) := by
      have h1 : ε' * (2 + 3 * θ / 4) ≤ ε' * (2 + θ) :=
        mul_le_mul_of_nonneg_left (by linarith) hε'0.le
      have h2 : 3 * θ / (8 * Real.pi) - θ / (8 * Real.pi) = θ / (4 * Real.pi) := by
        field_simp; ring
      linarith
    have := mul_le_mul_of_nonneg_right hcoef hTlog.le
    linarith
  -- ordinates
  have himinj : Set.InjOn Complex.im ↑Sz := by
    intro z hz w hw h
    have hz' := (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2.1
    have hw' := (Finset.mem_filter.1 (Finset.mem_filter.1 hw).1).2.1
    exact Complex.ext (by rw [hz', hw']) h
  refine ⟨Sz.image Complex.im, fun τ hτ => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hτ
    have hzS := Finset.mem_filter.1 hz
    have hzA := Finset.mem_filter.1 hzS.1
    have hzs := mem_stripFinsetPos.1 hzA.1
    exact ⟨hzS.2, hzs.2.2.2.1, Xi_im_eq_zero_of_xi_eq_zero hzA.2.1 hzs.2.2.2.2⟩
  · rw [Finset.card_image_of_injOn himinj]
    exact hSz

/-- **Separated critical zeros at linear height.** -/
theorem exists_separated_Xi_zeros_linear :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, ∃ t : Fin (d + 1) → ℝ, (∀ i, Xi (t i) = 0) ∧ (∀ i, 1 ≤ t i) ∧
      (∀ i, t i ≤ K * (d + 1)) ∧ ∀ i j, i ≠ j → 1 ≤ |t i - t j| := by
  classical
  obtain ⟨c₀, hc₀, T₀, hT₀, hmany⟩ := exists_many_critical_ordinates_dyadic
  obtain ⟨A, hA⟩ : ∃ A, A = xiLineTwoLogDerivConstant := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 10 * |A| + 41 := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = T₀ + 3 + 2 * C₂ / c₀ := ⟨_, rfl⟩
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; have : 0 ≤ 2 * C₂ / c₀ := by positivity
                           linarith
  refine ⟨2 * K₀, by linarith, fun d => ?_⟩
  have hd1 : (1 : ℝ) ≤ d + 1 := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = K₀ * (d + 1) := ⟨_, rfl⟩
  have hTK : T₀ + 3 ≤ T := by
    rw [hT, hK₀]
    have : 0 ≤ 2 * C₂ / c₀ := by positivity
    nlinarith
  have hT₀T : T₀ ≤ T := by linarith
  have hT3 : 3 ≤ T := by linarith
  obtain ⟨τS, hτS, hcard⟩ := hmany T hT₀T
  have hτpos : ∀ τ ∈ τS, 0 ≤ τ ∧ Xi τ = 0 := fun τ hτ =>
    ⟨by linarith [(hτS τ hτ).1], (hτS τ hτ).2.2⟩
  -- fiber bound
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈10 * (|A| + Real.log (2 * T + 5))⌉₊ := ⟨_, rfl⟩
  have hfib : ∀ k ∈ τS.image (fun τ => ⌊τ⌋₊), (τS.filter fun τ => ⌊τ⌋₊ = k).card ≤ n := by
    intro k hk
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hk
    have h1 := card_filter_floor_eq_le hτpos ⌊τ⌋₊
    rw [← hA] at h1
    have hkle : (⌊τ⌋₊ : ℝ) ≤ 2 * T := (Nat.floor_le (hτpos τ hτ).1).trans (hτS τ hτ).2.1
    have hlog : Real.log ((⌊τ⌋₊ : ℝ) + 5) ≤ Real.log (2 * T + 5) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : ((τS.filter fun τ' => ⌊τ'⌋₊ = ⌊τ⌋₊).card : ℝ) ≤
        10 * (|A| + Real.log (2 * T + 5)) := by
      have := le_abs_self A
      linarith
    have h3 := h2.trans (Nat.le_ceil _)
    rw [← hn] at h3
    exact_mod_cast h3
  have hcardB := Finset.card_le_mul_card_image τS n hfib
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hnle : (n : ℝ) ≤ C₂ * Real.log T := by
    have hl : Real.log (2 * T + 5) ≤ 3 + Real.log T := by
      have h7 : 2 * T + 5 ≤ Real.exp 2 * T := by
        have : (7.3 : ℝ) < Real.exp 2 := by
          have := Real.add_one_le_exp 2
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          have he := Real.exp_one_gt_d9
          rw [h2]; nlinarith
        nlinarith
      calc Real.log (2 * T + 5) ≤ Real.log (Real.exp 2 * T) := Real.log_le_log (by positivity) h7
        _ = 2 + Real.log T := by rw [Real.log_mul (by positivity) (by linarith), Real.log_exp]
        _ ≤ 3 + Real.log T := by linarith
    have hceil : (n : ℝ) ≤ 10 * (|A| + Real.log (2 * T + 5)) + 1 := by
      rw [hn]
      exact (Nat.ceil_lt_add_one (by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T + 5)
        positivity)).le
    rw [hC₂]
    have hA0 := abs_nonneg A
    have hprod := mul_nonneg (by positivity : (0 : ℝ) ≤ 10 * |A| + 31) (sub_nonneg.2 hlogT)
    linarith
  have hB : 2 * (d + 1) ≤ (τS.image fun τ => ⌊τ⌋₊).card := by
    have hn1 : 1 ≤ n := by
      by_contra h0
      push Not at h0
      have : n = 0 := by omega
      rw [this, zero_mul] at hcardB
      have h0' : (τS.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.1 hcardB
      have : 0 < c₀ * (T * Real.log T) := by positivity
      linarith
    have hτc : (τS.card : ℝ) ≥ 2 * (d + 1) * n := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 2 * (d + 1) * (n : ℝ) ≤ 2 * (d + 1) * (C₂ * Real.log T) :=
        mul_le_mul_of_nonneg_left hnle (by positivity)
      have h2 : 2 * (d + 1) * (C₂ * Real.log T) ≤ c₀ * (T * Real.log T) := by
        have hTd : 2 * (d + 1) * C₂ ≤ c₀ * T := by
          rw [hT, hK₀]
          have : c₀ * ((T₀ + 3 + 2 * C₂ / c₀) * (d + 1)) =
              c₀ * (T₀ + 3) * (d + 1) + 2 * C₂ * (d + 1) := by field_simp
          rw [this]
          have : 0 ≤ c₀ * (T₀ + 3) * (d + 1) := by
            have : 0 ≤ T₀ + 3 := by linarith
            positivity
          linarith
        have := mul_le_mul_of_nonneg_right hTd (by linarith : (0 : ℝ) ≤ Real.log T)
        nlinarith
      linarith
    have h' : 2 * (d + 1) * n ≤ τS.card := by exact_mod_cast hτc
    have := Nat.le_of_mul_le_mul_left (by nlinarith : n * (2 * (d + 1)) ≤
      n * (τS.image fun τ => ⌊τ⌋₊).card) (by omega : 0 < n)
    exact this
  obtain ⟨t, htS, hsep⟩ := exists_separated_of_card_image_floor (fun τ hτ => (hτpos τ hτ).1) hB
  refine ⟨t, fun i => (hτpos _ (htS i)).2, fun i => by linarith [(hτS _ (htS i)).1],
    fun i => ?_, hsep⟩
  have := (hτS _ (htS i)).2.1
  rw [hT] at this
  linarith

end

end RHTower
