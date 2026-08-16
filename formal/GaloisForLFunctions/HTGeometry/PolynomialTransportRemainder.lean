import Mathlib

/-!
# The third remainder of a polynomially transported block

A transport family with slow exponent `p` and polynomial degree `κ` moves a source that has already
been differentiated three times, so the remaining integrand carries `t^{-3}`.  Splitting the
integration at half the frequency separates the two mechanisms: below `x/2` the polynomial factor is
frozen at its largest value and the surviving `t^{p-3}` is absolutely convergent because `p < 3/2`;
above `x/2` the transport factor is bounded by one and the cubic decay is frozen instead.  The two
halves give the exact majorants `x^{κ-p}` and `x^{κ-2}`.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The transported cubic-decay integrand. -/
def polynomialTransportIntegrand (p κ x t : ℝ) : ℝ :=
  (t / x) ^ p * (1 + x - t) ^ κ * t ^ (-(3 : ℝ))

theorem rpow_neg_three_eq {s : ℝ} (hs : 0 < s) : s ^ (-(3 : ℝ)) = (s ^ (3 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hs.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem continuousOn_polynomialTransportIntegrand {p κ x a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a)
    (hx : 0 < x) :
    ContinuousOn (polynomialTransportIntegrand p κ x) (Icc a b) := by
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact (continuousOn_id.div_const x).rpow_const
      (fun t ht => Or.inl (ne_of_gt (div_pos (lt_of_lt_of_le ha ht.1) hx)))
  · exact (continuousOn_const.sub continuousOn_id).rpow_const (fun t _ => Or.inr hκ)
  · exact continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))

theorem intervalIntegrable_polynomialTransportIntegrand {p κ x a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a)
    (hab : a ≤ b) (hx : 0 < x) :
    IntervalIntegrable (polynomialTransportIntegrand p κ x) volume a b := by
  have h : ContinuousOn (polynomialTransportIntegrand p κ x) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_polynomialTransportIntegrand hκ ha hx
  exact h.intervalIntegrable

/-- The absolutely convergent scalar tail `∫ t^{-3/2}` past height one. -/
theorem integral_rpow_neg_threeHalves_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, t ^ (-(3 : ℝ) / 2)) ≤ 2 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have hmem : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro hcon
    exact absurd hcon.1 (not_le.mpr ha0)
  have hne : (-(3 : ℝ) / 2) ≠ -1 := by norm_num
  rw [integral_rpow (Or.inr ⟨hne, hmem⟩)]
  have hexp : -(3 : ℝ) / 2 + 1 = -(1 / 2) := by norm_num
  rw [hexp, Real.rpow_neg hb0.le, Real.rpow_neg ha0.le]
  have hapos : (0 : ℝ) < a ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ha0 _
  have hbpos : (0 : ℝ) < b ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hb0 _
  have hage : (1 : ℝ) ≤ a ^ ((1 : ℝ) / 2) := Real.one_le_rpow ha (by norm_num)
  have h1 : (a ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hage
  have h2 : (0 : ℝ) < (b ^ ((1 : ℝ) / 2))⁻¹ := by positivity
  have hval : ((b ^ ((1 : ℝ) / 2))⁻¹ - (a ^ ((1 : ℝ) / 2))⁻¹) / (-(1 / 2) : ℝ)
      = 2 * ((a ^ ((1 : ℝ) / 2))⁻¹ - (b ^ ((1 : ℝ) / 2))⁻¹) := by ring
  rw [hval]
  linarith

set_option maxHeartbeats 1000000 in
/-- **`(16)`--`(18)`: the third remainder splits at half the frequency.** -/
theorem integral_polynomialTransportIntegrand_le {p κ X₀ x : ℝ} (hp0 : 0 < p) (hp : p ≤ 3 / 2)
    (hκ : 0 ≤ κ) (hX₀ : 1 ≤ X₀) (hx : 2 * X₀ ≤ x) (hx2 : 2 ≤ x) :
    (∫ t in X₀..x, polynomialTransportIntegrand p κ x t)
      ≤ 2 * 2 ^ κ * x ^ (κ - p) + 4 * x ^ (κ - 2) := by
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  have hx0 : (0 : ℝ) < x := by linarith
  have hhalf : X₀ ≤ x / 2 := by linarith
  have hhalfx : x / 2 ≤ x := by linarith
  have hhalf0 : (0 : ℝ) < x / 2 := by linarith
  have hsplit : (∫ t in X₀..x, polynomialTransportIntegrand p κ x t)
      = (∫ t in X₀..(x / 2), polynomialTransportIntegrand p κ x t)
        + ∫ t in (x / 2)..x, polynomialTransportIntegrand p κ x t := by
    rw [integral_add_adjacent_intervals
      (intervalIntegrable_polynomialTransportIntegrand hκ hX0 hhalf hx0)
      (intervalIntegrable_polynomialTransportIntegrand hκ hhalf0 hhalfx hx0)]
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- the far half
    have hbound : ∀ t ∈ Icc X₀ (x / 2),
        polynomialTransportIntegrand p κ x t ≤ 2 ^ κ * x ^ (κ - p) * t ^ (-(3 : ℝ) / 2) := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_trans hX₀ ht.1
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have htx : t ≤ x := le_trans ht.2 hhalfx
      have hdiv : (t / x) ^ p = t ^ p * x ^ (-p) := by
        rw [Real.div_rpow ht0.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
      have hpoly : (1 + x - t) ^ κ ≤ 2 ^ κ * x ^ κ := by
        refine le_trans (Real.rpow_le_rpow (by linarith) (by linarith : 1 + x - t ≤ 2 * x) hκ) ?_
        exact le_of_eq (Real.mul_rpow (by norm_num) hx0.le)
      have hcube : t ^ p * t ^ (-(3 : ℝ)) = t ^ (p - 3) := by
        rw [← Real.rpow_add ht0, show p + -(3 : ℝ) = p - 3 by ring]
      have hdecay : t ^ (p - 3) ≤ t ^ (-(3 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      have hxp : x ^ (-p) * x ^ κ = x ^ (κ - p) := by
        rw [← Real.rpow_add hx0, show -p + κ = κ - p by ring]
      have hstep1 : polynomialTransportIntegrand p κ x t
          = (t ^ p * t ^ (-(3 : ℝ))) * x ^ (-p) * (1 + x - t) ^ κ := by
        rw [polynomialTransportIntegrand, hdiv]
        ring
      rw [hstep1, hcube]
      have hnn : (0 : ℝ) ≤ t ^ (p - 3) * x ^ (-p) := by positivity
      have e1 : t ^ (p - 3) * x ^ (-p) * (2 ^ κ * x ^ κ)
          = 2 ^ κ * x ^ (κ - p) * t ^ (p - 3) := by
        rw [← hxp]; ring
      calc t ^ (p - 3) * x ^ (-p) * (1 + x - t) ^ κ
          ≤ t ^ (p - 3) * x ^ (-p) * (2 ^ κ * x ^ κ) := mul_le_mul_of_nonneg_left hpoly hnn
        _ = 2 ^ κ * x ^ (κ - p) * t ^ (p - 3) := e1
        _ ≤ 2 ^ κ * x ^ (κ - p) * t ^ (-(3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hdecay (by positivity)
    have hmajint : IntervalIntegrable
        (fun t : ℝ => 2 ^ κ * x ^ (κ - p) * t ^ (-(3 : ℝ) / 2)) volume X₀ (x / 2) := by
      have hc : ContinuousOn (fun t : ℝ => 2 ^ κ * x ^ (κ - p) * t ^ (-(3 : ℝ) / 2))
          (uIcc X₀ (x / 2)) := by
        rw [uIcc_of_le hhalf]
        exact continuousOn_const.mul (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hX0 ht.1))))
      exact hc.intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hhalf
      (intervalIntegrable_polynomialTransportIntegrand hκ hX0 hhalf hx0) hmajint hbound
    refine le_trans hmono ?_
    rw [intervalIntegral.integral_const_mul]
    have htail := integral_rpow_neg_threeHalves_le hX₀ hhalf
    have hpos : (0 : ℝ) ≤ 2 ^ κ * x ^ (κ - p) := by positivity
    nlinarith [htail, hpos]
  · -- the near half
    have hbound : ∀ t ∈ Icc (x / 2) x,
        polynomialTransportIntegrand p κ x t ≤ 8 * x ^ (κ - 3) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hhalf0 ht.1
      have ht1 : (1 : ℝ) ≤ t := by linarith [ht.1]
      have hone : (t / x) ^ p ≤ 1 := by
        refine Real.rpow_le_one (by positivity) ?_ hp0.le
        rw [div_le_one hx0]
        exact ht.2
      have hpoly : (1 + x - t) ^ κ ≤ x ^ κ :=
        Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hκ
      have hcube : t ^ (-(3 : ℝ)) ≤ 8 * x ^ (-(3 : ℝ)) := by
        rw [rpow_neg_three_eq ht0, rpow_neg_three_eq hx0]
        have hxt : x ^ (3 : ℕ) ≤ 8 * t ^ (3 : ℕ) := by
          have h1 : x ≤ 2 * t := by linarith [ht.1]
          have h2 : x ^ (3 : ℕ) ≤ (2 * t) ^ (3 : ℕ) :=
            pow_le_pow_left₀ hx0.le h1 3
          calc x ^ (3 : ℕ) ≤ (2 * t) ^ (3 : ℕ) := h2
            _ = 8 * t ^ (3 : ℕ) := by ring
        have hx3 : (0 : ℝ) < x ^ (3 : ℕ) := by positivity
        have ht3 : (0 : ℝ) < t ^ (3 : ℕ) := by positivity
        rw [inv_le_iff_one_le_mul₀ ht3]
        rw [show (8 : ℝ) * (x ^ (3 : ℕ))⁻¹ * t ^ (3 : ℕ) = 8 * t ^ (3 : ℕ) / x ^ (3 : ℕ) by
          field_simp]
        rw [le_div_iff₀ hx3]
        linarith
      have hxk : x ^ κ * (8 * x ^ (-(3 : ℝ))) = 8 * x ^ (κ - 3) := by
        rw [show x ^ κ * (8 * x ^ (-(3 : ℝ))) = 8 * (x ^ κ * x ^ (-(3 : ℝ))) by ring,
          ← Real.rpow_add hx0, show κ + -(3 : ℝ) = κ - 3 by ring]
      calc polynomialTransportIntegrand p κ x t
          = (t / x) ^ p * ((1 + x - t) ^ κ * t ^ (-(3 : ℝ))) := by
            rw [polynomialTransportIntegrand]; ring
        _ ≤ 1 * ((1 + x - t) ^ κ * t ^ (-(3 : ℝ))) := by
            refine mul_le_mul_of_nonneg_right hone ?_
            exact mul_nonneg (Real.rpow_nonneg (by linarith [ht.2]) κ)
              (Real.rpow_nonneg ht0.le _)
        _ = (1 + x - t) ^ κ * t ^ (-(3 : ℝ)) := by ring
        _ ≤ x ^ κ * (8 * x ^ (-(3 : ℝ))) := by
            refine mul_le_mul hpoly hcube (by positivity) (by positivity)
        _ = 8 * x ^ (κ - 3) := hxk
    have hmono := intervalIntegral.integral_mono_on hhalfx
      (intervalIntegrable_polynomialTransportIntegrand hκ hhalf0 hhalfx hx0)
      intervalIntegrable_const hbound
    refine le_trans hmono ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hxk : x ^ (κ - 3) * x = x ^ (κ - 2) := by
      nth_rewrite 2 [show x = x ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hx0, show κ - 3 + 1 = κ - 2 by ring]
    have hfin : (x - x / 2) * (8 * x ^ (κ - 3)) = 4 * x ^ (κ - 2) := by
      rw [show (x - x / 2) * (8 * x ^ (κ - 3)) = 4 * (x ^ (κ - 3) * x) by ring, hxk]
    rw [hfin]

end GaloisForLFunctions.HTGeometry
