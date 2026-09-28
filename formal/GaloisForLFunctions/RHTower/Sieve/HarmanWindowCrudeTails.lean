import GaloisForLFunctions.RHTower.Sieve.HarmanWindowTwoPrimeCofactor

/-!
# The crude tails of the discarded sums over a window

Over the window `(y, y(1+θ)]`: the part of the discarded pair tail `D₂` with a three-prime cofactor
`m = p p' r` (`q₂ ≤ p ≤ p' ≤ r`), and the discarded quadruple tail `D₄`, are bounded crudely by
boxes: every cofactor window has `y/d ≥ y^{1/6}`, so each prime count is at most
`6(1+η)(θy/log y)/d`, and the prime tuples lie in products of fixed logarithmic ranges.  The unit
cofactor never occurs in `D₄` (the quadruple products stay below `y`).
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

theorem sum_product4_eq {s₁ s₂ s₃ s₄ : Finset ℕ} (K : ℝ) :
    ∑ qq ∈ s₁ ×ˢ s₂, ∑ pp ∈ s₃ ×ˢ s₄,
        K * (1 / (qq.1 : ℝ) * (1 / (qq.2 : ℝ) * (1 / (pp.1 : ℝ) * (1 / (pp.2 : ℝ)))))
      = K * ((∑ q ∈ s₁, 1 / (q : ℝ)) * (∑ q ∈ s₂, 1 / (q : ℝ)) *
          (∑ q ∈ s₃, 1 / (q : ℝ)) * (∑ q ∈ s₄, 1 / (q : ℝ))) := by
  have h12 : (∑ q ∈ s₁, 1 / (q : ℝ)) * (∑ q ∈ s₂, 1 / (q : ℝ)) =
      ∑ qq ∈ s₁ ×ˢ s₂, 1 / (qq.1 : ℝ) * (1 / (qq.2 : ℝ)) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  have h34 : (∑ q ∈ s₃, 1 / (q : ℝ)) * (∑ q ∈ s₄, 1 / (q : ℝ)) =
      ∑ pp ∈ s₃ ×ˢ s₄, 1 / (pp.1 : ℝ) * (1 / (pp.2 : ℝ)) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  rw [show (∑ q ∈ s₁, 1 / (q : ℝ)) * (∑ q ∈ s₂, 1 / (q : ℝ)) * (∑ q ∈ s₃, 1 / (q : ℝ)) *
      (∑ q ∈ s₄, 1 / (q : ℝ)) = ((∑ q ∈ s₁, 1 / (q : ℝ)) * (∑ q ∈ s₂, 1 / (q : ℝ))) *
      ((∑ q ∈ s₃, 1 / (q : ℝ)) * (∑ q ∈ s₄, 1 / (q : ℝ))) by ring, h12, h34,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun qq _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun pp _ => ?_)
  ring

theorem prod4_le {a b c d A B C D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) (hD : d ≤ D) : a * b * c * d ≤ A * B * C * D := by
  have hA0 : 0 ≤ A := ha.trans hA
  have hB0 : 0 ≤ B := hb.trans hB
  have hC0 : 0 ≤ C := hc.trans hC
  have h1 : a * b ≤ A * B := mul_le_mul hA hB hb hA0
  have h2 : a * b * c ≤ A * B * C := mul_le_mul h1 hC hc (mul_nonneg hA0 hB0)
  exact mul_le_mul h2 hD hd (mul_nonneg (mul_nonneg hA0 hB0) hC0)

/-- The window bound when `y/d ≥ y^{1/k}`. -/
theorem window_bound_of_rpow_le {y θ η d k : ℝ} (hy : 1 < y) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hd : 0 < d) (hk : 0 < k) (hyd : y ^ (1 / k) ≤ y / d) :
    (1 + η) * (θ * (y / d) / log (y / d)) ≤ (1 + η) * (θ * y / log y) * k * (1 / d) := by
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := Real.log_pos hy
  have hlog : log y / k ≤ log (y / d) := by
    have := Real.log_le_log (by positivity) hyd
    rw [Real.log_rpow hy0] at this
    calc log y / k = 1 / k * log y := by ring
      _ ≤ _ := this
  have hlk : 0 < log y / k := div_pos hly hk
  have hstep : θ * (y / d) / log (y / d) ≤ θ * (y / d) / (log y / k) :=
    div_le_div_of_nonneg_left (by positivity) hlk hlog
  calc (1 + η) * (θ * (y / d) / log (y / d)) ≤ (1 + η) * (θ * (y / d) / (log y / k)) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
    _ = (1 + η) * (θ * y / log y) * k * (1 / d) := by field_simp

/-- `y/d ≥ y^{1/6}` when the cofactor window reaches a prime `r > y^{2/11}`. -/
theorem rpow_sixth_le_div {y θ d r : ℝ} (hy : 1 < y) (hθ1 : θ ≤ 1) (hd : 0 < d)
    (hr : y ^ (2 / 11 : ℝ) < r) (h66 : 2 ≤ y ^ (1 / 66 : ℝ)) (hdr : d * r ≤ y * (1 + θ)) :
    y ^ (1 / 6 : ℝ) ≤ y / d := by
  have hy0 : 0 < y := by linarith
  have hsplit : y ^ (2 / 11 : ℝ) = y ^ (1 / 66 : ℝ) * y ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  have h6 : 0 ≤ y ^ (1 / 6 : ℝ) := Real.rpow_nonneg hy0.le _
  rw [le_div_iff₀ hd]
  have h1 : d * r ≤ y * 2 := hdr.trans (by nlinarith)
  have h2 : y ^ (1 / 6 : ℝ) * 2 ≤ r := by rw [hsplit] at hr; nlinarith
  nlinarith

/-- A nonzero count at a tuple of product `d` with top prime `r > y^{2/11}` is at most
`6(1+η)(θy/log y)/d`. -/
theorem window_count_le_six {c η y θ : ℝ} {d r : ℕ} (hy : 1 < y) (hη : 0 ≤ η)
    (hθ : exp (-(c / 4) * sqrt (log y)) ≤ θ) (hθ1 : θ ≤ 1)
    (hwin : ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ d r : ℕ, 0 < d → y ^ (1 / 6 : ℝ) ≤ r → (d : ℝ) * r ≤ y * (1 + θ) →
      (primeCountAbove (⌊y⌋₊ / d) (⌊y * (1 + θ)⌋₊ / d) r : ℝ)
        ≤ (1 + η) * (θ * (y / d) / log (y / d)))
    (h66 : 2 ≤ y ^ (1 / 66 : ℝ)) (hd : 0 < d) (hr : y ^ (2 / 11 : ℝ) < r)
    (hdr : (d : ℝ) * r ≤ y * (1 + θ)) :
    (primeCountAbove (⌊y⌋₊ / d) (⌊y * (1 + θ)⌋₊ / d) r : ℝ)
      ≤ (1 + η) * (θ * y / log y) * 6 * (1 / (d : ℝ)) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hy0 : 0 < y := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h6 : y ^ (1 / 6 : ℝ) ≤ (r : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)).trans hr.le
  have hyd := rpow_sixth_le_div hy hθ1 hd0 hr h66 hdr
  refine (hwin θ hθ hθ1 d r hd h6 hdr).trans ?_
  have := window_bound_of_rpow_le hy hθ0.le hη hd0 (by norm_num : (0 : ℝ) < 6)
    (by norm_num at hyd ⊢; exact hyd)
  exact this

/-- **The three-prime-cofactor part of the discarded pair tail**, crudely by a box. -/
theorem eventually_sum_harmanDiscardPair_threePrime_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
        ∑ pp ∈ ((Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))) ×ˢ
            (Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)))).filter
            (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
          (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2))
            (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2)) pp.2 : ℝ)
        ≤ (1 + η) * (θ * y / log y) * 6 *
          ((log ((3 / 11 + 1 / 1000000) / (2 / 11)) + η) *
            (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + η) *
            (log ((7 / 11 + 1 / 1000000) / 3 / (2 / 11)) + η) *
            (log ((5 / 11 + 1 / 1000000) / 2 / (2 / 11)) + η)) := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := 3 / 11 + 1 / 1000000)
      (by norm_num) (by norm_num) hη,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := (1 + 1 / 1000000) / 5)
      (by norm_num) (by norm_num) hη,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := (7 / 11 + 1 / 1000000) / 3)
      (by norm_num) (by norm_num) hη,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := (5 / 11 + 1 / 1000000) / 2)
      (by norm_num) (by norm_num) hη,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000000)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 66)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hm1 hm2 hm3 hm4 hyκ h66 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  set B₁ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ (3 / 11 + κ)⌋₊).filter Nat.Prime with hB₁
  set B₂ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + κ) / 5)⌋₊).filter Nat.Prime with hB₂
  set B₃ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((7 / 11 + κ) / 3)⌋₊).filter Nat.Prime with hB₃
  set B₄ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((5 / 11 + κ) / 2)⌋₊).filter Nat.Prime with hB₄
  set g : ℕ × ℕ → ℕ × ℕ → ℝ := fun qq pp =>
    C * 6 * (1 / (qq.1 : ℝ) * (1 / (qq.2 : ℝ) * (1 / (pp.1 : ℝ) * (1 / (pp.2 : ℝ))))) with hg
  have hg0 : ∀ qq pp, 0 ≤ g qq pp := fun qq pp => by simp only [hg]; positivity
  have key : ∑ qq ∈ harmanDiscardPairSet z Q D E,
        ∑ pp ∈ ((Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))) ×ˢ
            (Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)))).filter
            (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
          (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2))
            (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2)) pp.2 : ℝ)
      ≤ ∑ qq ∈ B₁ ×ˢ B₂, ∑ pp ∈ B₃ ×ˢ B₄, g qq pp := by
    refine sum_le_sum_of_le_ite (fun qq _ => Finset.sum_nonneg (fun pp _ => hg0 qq pp))
      (fun qq hqq => ?_)
    obtain ⟨q₁, q₂⟩ := qq
    simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at hqq
    obtain ⟨⟨_, hz2, _⟩, hp1, hp2, h21, _⟩ := hqq
    simp only
    have hd12 : 0 < q₁ * q₂ := Nat.mul_pos hp1.pos hp2.pos
    have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
    have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
    have hzq : y ^ (2 / 11 : ℝ) < q₂ := lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz2)
    have ha2 : 2 / 11 < log q₂ / log y := lt_logScale_of_rpow_lt hy1 hzq
    have ha21 : log q₂ / log y < log q₁ / log y :=
      div_lt_div_of_pos_right (Real.log_lt_log hq2 (by exact_mod_cast h21)) hly
    -- a nonzero count places the tuple in the box
    have hreg_of : ∀ pp ∈ ((Finset.Icc q₂ (⌊y * (1 + θ)⌋₊ / (q₁ * q₂))) ×ˢ
          (Finset.Icc q₂ (⌊y * (1 + θ)⌋₊ / (q₁ * q₂)))).filter
          (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
        primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / (pp.1 * pp.2))
          (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / (pp.1 * pp.2)) pp.2 ≠ 0 →
        ((q₁, q₂) ∈ B₁ ×ˢ B₂ ∧ pp ∈ B₃ ×ˢ B₄) ∧
          ((q₁ * q₂ * (pp.1 * pp.2) : ℕ) : ℝ) * pp.2 ≤ y * (1 + θ) := by
      intro pp hpp h0
      obtain ⟨p, p'⟩ := pp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpp
      obtain ⟨⟨⟨h2p, _⟩, _, _⟩, hpP, hp'P, hpp'⟩ := hpp
      simp only at h0 ⊢
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul] at h0
      have hdrN := mul_le_of_primeCountAbove_ne_zero
        (Nat.mul_pos hd12 (Nat.mul_pos hpP.pos hp'P.pos)) h0
      clear h0
      have hbr : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
      have hdr : ((q₁ * q₂ * (p * p') : ℕ) : ℝ) * p' ≤ y * (1 + θ) := by
        have : ((q₁ * q₂ * (p * p') * p' : ℕ) : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hdrN
        push_cast at this ⊢; linarith
      refine ⟨?_, hdr⟩
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      have hp'0 : (0 : ℝ) < p' := by exact_mod_cast hp'P.pos
      have ha3 : log q₂ / log y ≤ log p / log y :=
        div_le_div_of_nonneg_right (Real.log_le_log hq2 (by exact_mod_cast h2p)) hly.le
      have ha4 : log p / log y ≤ log p' / log y :=
        div_le_div_of_nonneg_right (Real.log_le_log hp0 (by exact_mod_cast hpp')) hly.le
      have hsum : log q₁ / log y + log q₂ / log y + log p / log y + 2 * (log p' / log y)
          ≤ 1 + κ := by
        have h2y : y * (1 + θ) ≤ y ^ (1 + κ) := by
          rw [Real.rpow_add hy0, Real.rpow_one]; nlinarith
        have hm : (q₁ : ℝ) * q₂ * (p * p') * p' ≤ y ^ (1 + κ) := by
          push_cast at hdr; linarith
        have := logScale_le_of_le_rpow hy1 (by positivity) hm
        rw [Real.log_mul (by positivity) hp'0.ne', Real.log_mul (by positivity) (by positivity),
          Real.log_mul hq1.ne' hq2.ne', Real.log_mul hp0.ne' hp'0.ne'] at this
        have e : (log q₁ + log q₂ + (log p + log p') + log p') / log y
            = log q₁ / log y + log q₂ / log y + log p / log y + 2 * (log p' / log y) := by ring
        linarith
      refine ⟨Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp1.pos).2
          ⟨by linarith, by linarith⟩, hp1⟩,
        Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp2.pos).2 ⟨ha2, by linarith⟩, hp2⟩⟩,
        Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hpP.pos).2
          ⟨by linarith, by linarith⟩, hpP⟩,
        Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp'P.pos).2
          ⟨by linarith, by linarith⟩, hp'P⟩⟩⟩
    by_cases hreg : (q₁, q₂) ∈ B₁ ×ˢ B₂
    · rw [if_pos hreg]
      refine sum_le_sum_of_le_ite (fun pp _ => hg0 _ pp) (fun pp hpp => ?_)
      by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / (pp.1 * pp.2))
          (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / (pp.1 * pp.2)) pp.2 = 0
      · rw [h0, Nat.cast_zero]
        split_ifs
        · exact hg0 _ _
        · exact le_rfl
      obtain ⟨⟨_, hpp'⟩, hdr⟩ := hreg_of pp hpp h0
      rw [if_pos hpp']
      obtain ⟨p, p'⟩ := pp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpp
      obtain ⟨⟨⟨h2p, _⟩, _, _⟩, hpP, hp'P, hpp''⟩ := hpp
      simp only at hdr ⊢
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      have hr : y ^ (2 / 11 : ℝ) < (p' : ℝ) := by
        have : (q₂ : ℝ) ≤ p' := by exact_mod_cast h2p.trans hpp''
        linarith
      refine (window_count_le_six hy1 hη.le hθ hθ1 hwin h66
        (Nat.mul_pos hd12 (Nat.mul_pos hpP.pos hp'P.pos)) hr hdr).trans_eq ?_
      simp only [hg, hC]
      push_cast
      ring
    · rw [if_neg hreg]
      refine Finset.sum_nonpos (fun pp hpp => ?_)
      by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / (pp.1 * pp.2))
          (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / (pp.1 * pp.2)) pp.2 = 0
      · rw [h0, Nat.cast_zero]
      · exact absurd (hreg_of pp hpp h0).1.1 hreg
  refine key.trans ?_
  simp only [hg]
  rw [sum_product4_eq]
  have hs : ∀ s : Finset ℕ, 0 ≤ ∑ q ∈ s, 1 / (q : ℝ) :=
    fun s => Finset.sum_nonneg (fun _ _ => by positivity)
  have := prod4_le (hs B₁) (hs B₂) (hs B₃) (hs B₄) hm1 hm2 hm3 hm4
  calc C * 6 * ((∑ q ∈ B₁, 1 / (q : ℝ)) * (∑ q ∈ B₂, 1 / (q : ℝ)) *
        (∑ q ∈ B₃, 1 / (q : ℝ)) * (∑ q ∈ B₄, 1 / (q : ℝ)))
      ≤ C * 6 * ((log ((3 / 11 + κ) / (2 / 11)) + η) * (log ((1 + κ) / 5 / (2 / 11)) + η) *
          (log ((7 / 11 + κ) / 3 / (2 / 11)) + η) * (log ((5 / 11 + κ) / 2 / (2 / 11)) + η)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by rw [hC]

/-- **The discarded quadruple tail over a window**, crudely by a box. -/
theorem eventually_sum_harmanDiscardQuad_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ t ∈ harmanDiscardQuadSet z D E,
          (harmanQuadTupleBound (⌊y⌋₊ / quadProd t) (⌊y * (1 + θ)⌋₊ / quadProd t) t.2.2 : ℝ)
        ≤ (1 + η) * (θ * y / log y) * 6 *
          ((log ((1 / 4 + 1 / 1000000) / (2 / 11)) + η) *
            (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + η) *
            (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + η) *
            (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + η)) := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := 1 / 4 + 1 / 1000000)
      (by norm_num) (by norm_num) hη,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := (1 + 1 / 1000000) / 5)
      (by norm_num) (by norm_num) hη,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 66)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hm1 hm2 h66 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  set B₁ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ (1 / 4 + κ)⌋₊).filter Nat.Prime with hB₁
  set B₂ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + κ) / 5)⌋₊).filter Nat.Prime with hB₂
  set g : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun t =>
    C * 6 * (1 / (t.1.1 : ℝ) * (1 / (t.1.2 : ℝ) * (1 / (t.2.1 : ℝ) * (1 / (t.2.2 : ℝ)))))
    with hg
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have key : ∑ t ∈ harmanDiscardQuadSet z D E,
        (harmanQuadTupleBound (⌊y⌋₊ / quadProd t) (⌊y * (1 + θ)⌋₊ / quadProd t) t.2.2 : ℝ)
      ≤ ∑ t ∈ (B₁ ×ˢ B₂) ×ˢ (B₂ ×ˢ B₂), g t := by
    refine sum_le_sum_of_le_ite (fun t _ => hg0 t) (fun t ht => ?_)
    obtain ⟨⟨q₁, q₂⟩, ⟨q₃, q₄⟩⟩ := t
    simp only [harmanDiscardQuadSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at ht
    obtain ⟨⟨⟨⟨_, hD1⟩, _⟩, _, hz4, _⟩, hp1, hp2, hp3, hp4, h21, h32, h43, hE⟩ := ht
    simp only [quadProd]
    have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
    have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
    have hq3 : (0 : ℝ) < q₃ := by exact_mod_cast hp3.pos
    have hq4 : (0 : ℝ) < q₄ := by exact_mod_cast hp4.pos
    have hzq : y ^ (2 / 11 : ℝ) < q₄ := lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz4)
    have h43' : (q₄ : ℝ) < q₃ := by exact_mod_cast h43
    have h32' : (q₃ : ℝ) < q₂ := by exact_mod_cast h32
    have h21' : (q₂ : ℝ) < q₁ := by exact_mod_cast h21
    have hEr : (q₁ : ℝ) * q₂ ^ 4 < y ^ (1 + κ) :=
      lt_of_lt_of_le (by exact_mod_cast hE) hP.E_le
    -- the tuple lies in the box
    have hbox : ((q₁, q₂), (q₃, q₄)) ∈ (B₁ ×ˢ B₂) ×ˢ (B₂ ×ˢ B₂) := by
      have ha2 : log q₂ / log y ≤ (1 + κ) / 5 := by
        have h5 : (q₂ : ℝ) ^ 5 ≤ y ^ (1 + κ) := by
          have : (q₂ : ℝ) ^ 5 ≤ q₁ * q₂ ^ 4 := by
            rw [pow_succ']; exact mul_le_mul_of_nonneg_right h21'.le (by positivity)
          linarith
        have := logScale_le_of_le_rpow hy1 (by positivity) h5
        rw [Real.log_pow] at this
        push_cast at this
        have e : 5 * log (q₂ : ℝ) / log y = 5 * (log q₂ / log y) := by ring
        linarith
      have hl4 : 2 / 11 < log q₄ / log y := lt_logScale_of_rpow_lt hy1 hzq
      have l34 : log q₄ / log y < log q₃ / log y :=
        div_lt_div_of_pos_right (Real.log_lt_log hq4 h43') hly
      have l23 : log q₃ / log y < log q₂ / log y :=
        div_lt_div_of_pos_right (Real.log_lt_log hq3 h32') hly
      have l12 : log q₂ / log y < log q₁ / log y :=
        div_lt_div_of_pos_right (Real.log_lt_log hq2 h21') hly
      have ha1 : log q₁ / log y ≤ 1 / 4 + κ :=
        logScale_le_of_le_rpow hy1 hq1 ((by exact_mod_cast hD1.le : (q₁ : ℝ) ≤ D).trans hP.D_le)
      exact Finset.mem_product.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp1.pos).2 ⟨by linarith, ha1⟩, hp1⟩,
          Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp2.pos).2 ⟨by linarith, ha2⟩, hp2⟩⟩,
        Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp3.pos).2
            ⟨by linarith, by linarith⟩, hp3⟩,
          Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy1 hp4.pos).2
            ⟨hl4, by linarith⟩, hp4⟩⟩⟩
    rw [if_pos hbox]
    have hd : 0 < q₁ * q₂ * q₃ * q₄ :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos
    -- the product stays below `y`, so the unit cofactor does not occur
    have hdy : q₁ * q₂ * q₃ * q₄ ≤ ⌊y⌋₊ := by
      have hκ2 : y ^ κ ≤ y ^ (2 / 11 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num [hκ])
      have hlt : (q₁ : ℝ) * q₂ * q₃ * q₄ < y := by
        have h1 : (q₁ : ℝ) * q₂ * q₃ * q₄ * q₂ ≤ q₁ * q₂ ^ 4 := by
          have h34 : (q₃ : ℝ) * q₄ ≤ q₂ * q₂ :=
            mul_le_mul h32'.le (h43'.trans h32').le hq4.le hq2.le
          calc (q₁ : ℝ) * q₂ * q₃ * q₄ * q₂ = (q₁ * q₂ * q₂) * (q₃ * q₄) := by ring
            _ ≤ (q₁ * q₂ * q₂) * (q₂ * q₂) := mul_le_mul_of_nonneg_left h34 (by positivity)
            _ = q₁ * q₂ ^ 4 := by ring
        have h2 : y ^ (1 + κ) = y * y ^ κ := by rw [Real.rpow_add hy0, Real.rpow_one]
        have h3 : (q₁ : ℝ) * q₂ * q₃ * q₄ * q₂ < y * q₂ := by
          have : y * y ^ κ ≤ y * q₂ := mul_le_mul_of_nonneg_left
            (hκ2.trans (hzq.trans (h43'.trans h32')).le) hy0.le
          linarith
        exact lt_of_mul_lt_mul_right h3 hq2.le
      have : ((q₁ * q₂ * q₃ * q₄ : ℕ) : ℝ) ≤ y := by push_cast; exact hlt.le
      exact (Nat.le_floor_iff hy0.le).2 this
    have hunit : 1 ∉ Finset.Ioc (⌊y⌋₊ / (q₁ * q₂ * q₃ * q₄))
        (⌊y * (1 + θ)⌋₊ / (q₁ * q₂ * q₃ * q₄)) := by
      rw [Finset.mem_Ioc, not_and_or]
      left
      have : 1 ≤ ⌊y⌋₊ / (q₁ * q₂ * q₃ * q₄) := (Nat.le_div_iff_mul_le hd).2 (by omega)
      omega
    rw [harmanQuadTupleBound, if_neg hunit, zero_add]
    by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂ * q₃ * q₄))
        (⌊y * (1 + θ)⌋₊ / (q₁ * q₂ * q₃ * q₄)) q₄ = 0
    · rw [h0, Nat.cast_zero]; exact hg0 _
    have hdrN := mul_le_of_primeCountAbove_ne_zero hd h0
    have hbr : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
    have hdr : ((q₁ * q₂ * q₃ * q₄ : ℕ) : ℝ) * q₄ ≤ y * (1 + θ) := by
      have : ((q₁ * q₂ * q₃ * q₄ * q₄ : ℕ) : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hdrN
      push_cast at this ⊢; linarith
    refine (window_count_le_six hy1 hη.le hθ hθ1 hwin h66 hd hzq hdr).trans_eq ?_
    simp only [hg, hC]
    push_cast
    ring
  refine key.trans ?_
  rw [Finset.sum_product]
  simp only [hg]
  rw [sum_product4_eq]
  have hs : ∀ s : Finset ℕ, 0 ≤ ∑ q ∈ s, 1 / (q : ℝ) :=
    fun s => Finset.sum_nonneg (fun _ _ => by positivity)
  have := prod4_le (hs B₁) (hs B₂) (hs B₂) (hs B₂) hm1 hm2 hm2 hm2
  calc C * 6 * ((∑ q ∈ B₁, 1 / (q : ℝ)) * (∑ q ∈ B₂, 1 / (q : ℝ)) *
        (∑ q ∈ B₂, 1 / (q : ℝ)) * (∑ q ∈ B₂, 1 / (q : ℝ)))
      ≤ C * 6 * ((log ((1 / 4 + κ) / (2 / 11)) + η) * (log ((1 + κ) / 5 / (2 / 11)) + η) *
          (log ((1 + κ) / 5 / (2 / 11)) + η) * (log ((1 + κ) / 5 / (2 / 11)) + η)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by rw [hC]

end

end RHTower.Sieve
