import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.LagPairThresholdSharp

/-!
# The numeric core of the hyperbolic zero-free condition

With `u = 1/(29 log G)` the zero-free region of width `1/(58 log γ)` gives `b = β(1−β) ≥ u(1−u)`
at `G = γ²`.  The exact requirement is `1/4 ≤ b(G + 2 − 2b)`, and `b ↦ b(G + 2 − 2b)` is increasing
on `[0, 1/4]`, so only the lower bound matters.  Monotonicity in `G` reduces to
`log(41/2) ≥ 1 + 2K/41`, because `log G ≤ log(41/2) + 2G/41 − 1`.
-/

open Real

namespace RHTower

noncomputable section

/-- `log (41/2) ≥ 2.9921`. -/
theorem log_fortyOne_half_lower : (2.9921 : ℝ) ≤ Real.log (41 / 2) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsplit : Real.log (41 / 2) = Real.log 16 + Real.log (41 / 32) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hfrac : (1 : ℝ) - 32 / 41 ≤ Real.log (41 / 32) := by
    have h := Real.log_le_sub_one_of_pos (x := (32 : ℝ) / 41) (by norm_num)
    have hinv : Real.log ((32 : ℝ) / 41) = -Real.log (41 / 32) := by
      rw [← Real.log_inv]
      norm_num
    rw [hinv] at h
    linarith
  rw [hsplit, hlog16]
  linarith

/-- `log (41/2) ≤ 3.023`. -/
theorem log_fortyOne_half_upper : Real.log (41 / 2) ≤ (3.023 : ℝ) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hcube : Real.exp 1 ^ (3 : ℕ) = Real.exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he3 : (20.085 : ℝ) < Real.exp 3 := by
    rw [← hcube]
    have h1 : (2.7182818283 : ℝ) ^ (3 : ℕ) ≤ Real.exp 1 ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he.le 3
    have h2 : (20.085 : ℝ) < (2.7182818283 : ℝ) ^ (3 : ℕ) := by norm_num
    linarith
  have he0 : (1.023 : ℝ) ≤ Real.exp 0.023 := by
    have := Real.add_one_le_exp (0.023 : ℝ)
    linarith
  have hprod : Real.exp (3.023 : ℝ) = Real.exp 3 * Real.exp 0.023 := by
    rw [← Real.exp_add]
    norm_num
  have hbig : (41 : ℝ) / 2 < Real.exp 3.023 := by
    rw [hprod]
    nlinarith [he3, he0, Real.exp_pos (3 : ℝ), Real.exp_pos (0.023 : ℝ)]
  have h := Real.log_lt_log (by norm_num) hbig
  rw [Real.log_exp] at h
  exact h.le

/-- **The numeric core.**  With `u = 1/(29 log G)` and `G ≥ 41/2`, any `b` between `u(1−u)` and
`1/4` satisfies the exact hyperbolic requirement. -/
theorem hyperbolic_numeric {G b : ℝ} (hG : 41 / 2 ≤ G)
    (hb : 1 / (29 * Real.log G) * (1 - 1 / (29 * Real.log G)) ≤ b) (hb4 : b ≤ 1 / 4) :
    1 / 4 ≤ b * (G + 2 - 2 * b) := by
  set ℓ : ℝ := Real.log (41 / 2) with hℓdef
  have hℓlow : (2.9921 : ℝ) ≤ ℓ := log_fortyOne_half_lower
  have hℓhigh : ℓ ≤ (3.023 : ℝ) := log_fortyOne_half_upper
  have hG0 : (0 : ℝ) < G := by linarith
  have hLge : ℓ ≤ Real.log G := Real.log_le_log (by norm_num) hG
  have hLpos : (0 : ℝ) < Real.log G := by linarith
  set u : ℝ := 1 / (29 * Real.log G) with hudef
  have hupos : (0 : ℝ) < u := by rw [hudef]; positivity
  have huub : u ≤ 1 / (29 * (2.9921 : ℝ)) := by
    rw [hudef]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hu0 : u ≤ (0.011525 : ℝ) := by
    refine le_trans huub ?_
    norm_num
  -- the monotone comparison in `G`
  have hlogub : Real.log G ≤ ℓ + 2 * G / 41 - 1 := by
    have hratio : Real.log (2 * G / 41) ≤ 2 * G / 41 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log G = ℓ + Real.log (2 * G / 41) := by
      rw [hℓdef, ← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    linarith
  have hKey : (41 / 2 + (2 - 2 * (0.011525 : ℝ))) / (29 * ℓ) ≤ u * (G + (2 - 2 * (0.011525 : ℝ))) := by
    set K : ℝ := 2 - 2 * (0.011525 : ℝ) with hKdef
    have hK : (1.976 : ℝ) ≤ K := by rw [hKdef]; norm_num
    have hK2 : K ≤ (1.978 : ℝ) := by rw [hKdef]; norm_num
    have hstep : (41 / 2 + K) * Real.log G ≤ (G + K) * ℓ := by
      have hcmp : ℓ ≥ 1 + 2 * K / 41 := by nlinarith [hℓlow, hK2]
      nlinarith [hlogub, hG, hcmp, hℓlow]
    rw [hudef, div_mul_eq_mul_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    nlinarith [hstep, hLpos, hℓlow]
  -- assemble
  have hbmin : u * (1 - (0.011525 : ℝ)) * (G + (2 - 2 * (0.011525 : ℝ))) ≤ b * (G + 2 - 2 * b) := by
    have h1 : u * (1 - u) ≤ b := hb
    have h2 : (0 : ℝ) < G + 2 - 2 * b := by nlinarith [hG, hb4]
    have h3 : u * (1 - (0.011525 : ℝ)) ≤ u * (1 - u) := by nlinarith [hupos, hu0]
    have h4 : G + (2 - 2 * (0.011525 : ℝ)) ≤ G + 2 - 2 * b ∨ b ≥ (0.011525 : ℝ) := by
      by_cases hc : b ≤ (0.011525 : ℝ)
      · left; linarith
      · right; linarith [not_le.mp hc]
    rcases h4 with h4 | h4
    · nlinarith [h1, h3, h4, hupos, hb4, hG]
    · nlinarith [h4, hb4, hG, hupos, hu0, h3, h1]
  have hfinal : (1 : ℝ) / 4 ≤ u * (1 - (0.011525 : ℝ)) * (G + (2 - 2 * (0.011525 : ℝ))) := by
    have hlow : (41 / 2 + (2 - 2 * (0.011525 : ℝ))) / (29 * (3.023 : ℝ))
        ≤ (41 / 2 + (2 - 2 * (0.011525 : ℝ))) / (29 * ℓ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hnum : (1 : ℝ) / 4 / (1 - (0.011525 : ℝ))
        ≤ (41 / 2 + (2 - 2 * (0.011525 : ℝ))) / (29 * (3.023 : ℝ)) := by
      norm_num
    nlinarith [hKey, hlow, hnum, hupos]
  linarith [hfinal, hbmin]

/-! ### The hyperbolic condition for every zero copy -/

/-- The zero of a conjugated copy is the conjugated zero. -/
theorem coe_xiZeroCopyConj (q : XiZeroCopy) :
    (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ)
      = (starRingEnd ℂ) ((q.1 : XiDivisorSupport) : ℂ) := rfl

private theorem hyperbolic_exact_of_pos (q : XiZeroCopy) (hpos : 0 < (q.1 : ℂ).im) :
    (1 : ℝ) / 4 ≤ ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re))
      * ((q.1 : ℂ).im ^ (2 : ℕ) + 2 - 2 * ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re))) := by
  set β : ℝ := (q.1 : ℂ).re with hβdef
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  have hγ2 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  rw [← hγdef] at hγ2
  have hγ4 : (4 : ℝ) ≤ γ := by nlinarith [hpos, hγ2]
  have hγ1 : (1 : ℝ) < γ := by linarith
  have hL : (0 : ℝ) < Real.log γ := Real.log_pos hγ1
  have hup := xiZeroCopy_zero_free_fiftyEight (q := q) (by rw [← hγdef]; exact hγ4)
  rw [← hβdef, ← hγdef] at hup
  have hpim : (((lagPartner q).1 : XiDivisorSupport) : ℂ).im = γ := by
    rw [lagPartner_coe, hγdef]
    simp
  have hpre : (((lagPartner q).1 : XiDivisorSupport) : ℂ).re = 1 - β := by
    rw [lagPartner_coe, hβdef]
    simp
  have hplow := xiZeroCopy_zero_free_fiftyEight (q := lagPartner q) (by rw [hpim]; exact hγ4)
  rw [hpre, hpim] at hplow
  -- `u` in the two shapes
  have hlogG : Real.log (γ ^ (2 : ℕ)) = 2 * Real.log γ := by
    rw [Real.log_pow]
    push_cast
    ring
  have hu : 1 / (29 * Real.log (γ ^ (2 : ℕ))) = 1 / 58 / Real.log γ := by
    rw [hlogG]
    field_simp
    ring
  set u : ℝ := 1 / 58 / Real.log γ with hudef
  have hupos : (0 : ℝ) < u := by rw [hudef]; positivity
  have huβ : u ≤ β := by linarith
  have hβu : β ≤ 1 - u := hup
  have hb4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hbmin : u * (1 - u) ≤ β * (1 - β) := by nlinarith [huβ, hβu]
  refine hyperbolic_numeric (G := γ ^ (2 : ℕ)) (b := β * (1 - β)) (by linarith) ?_ hb4
  rw [hu]
  exact hbmin

/-- **The exact hyperbolic condition, for every zero copy of `ξ`.** -/
theorem xiZeroCopy_hyperbolic_exact (q : XiZeroCopy) :
    (1 : ℝ) / 4 ≤ ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re))
      * ((q.1 : ℂ).im ^ (2 : ℕ) + 2 - 2 * ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re))) := by
  rcases lt_trichotomy ((q.1 : ℂ).im) 0 with h | h | h
  · have hc := hyperbolic_exact_of_pos (xiZeroCopyConjEquiv q) (by
      rw [coe_xiZeroCopyConj, Complex.conj_im]
      linarith)
    rw [coe_xiZeroCopyConj, Complex.conj_re, Complex.conj_im] at hc
    have hsq : (-(q.1 : ℂ).im) ^ (2 : ℕ) = ((q.1 : ℂ).im) ^ (2 : ℕ) := by ring
    rw [hsq] at hc
    exact hc
  · exfalso
    have hγ2 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    rw [h] at hγ2
    norm_num at hγ2
  · exact hyperbolic_exact_of_pos q h

/-- The pair condition at `σ = 1/2` follows from the exact hyperbolic condition. -/
theorem pairCondition_half_of_hyperbolic_exact {u γ : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hex : (1 : ℝ) / 4 ≤ (u * (1 - u)) * (γ ^ (2 : ℕ) + 2 - 2 * (u * (1 - u)))) :
    4 * (u - 1 / 2) ^ (4 : ℕ) * γ ^ (2 : ℕ)
      ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ)
          * ((1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ)) := by
  have hb0 : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hg0 : (0 : ℝ) ≤ γ ^ (2 : ℕ) := sq_nonneg γ
  have hsq : (1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ) = u * (1 - u) := by ring
  have hquart : (u - 1 / 2) ^ (4 : ℕ) = (u * (1 - u) - 1 / 4) ^ (2 : ℕ) := by ring
  rw [hsq, hquart]
  nlinarith [hex, hb0, hg0, sq_nonneg (u * (1 - u))]

/-- **Unconditional positivity of the lag pole series on `Re s > 1/2`.** -/
theorem re_lagPoleSeries_nonneg_half {s : ℂ} (hs : 1 / 2 < s.re) :
    0 ≤ (lagPoleSeries s).re := by
  refine re_lagPoleSeries_nonneg_of_pairs
    (summable_lagTerm_of_lt_re (c := 1 / 2) (fun q => (lagPole_re_lt_half q).le) hs)
    fun q => ?_
  have hu0 := xiZeroCopy_re_pos q
  have hu1 := xiZeroCopy_re_lt_one q
  set u : ℝ := (q.1 : ℂ).re with hu
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  set σ : ℝ := s.re with hσ
  have ha : |u - 1 / 2| < σ := by
    rw [abs_lt]; constructor <;> linarith
  refine re_lagTerm_add_partner_nonneg q ha ?_
  have hex := xiZeroCopy_hyperbolic_exact q
  rw [← hu, ← hγdef] at hex
  have hhalf := pairCondition_half_of_hyperbolic_exact hu0 hu1 hex
  have hX0 : 0 < u * (1 - u) + γ ^ (2 : ℕ) := by
    have := mul_pos hu0 (by linarith : (0 : ℝ) < 1 - u)
    positivity
  have hmono : (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ)
        * ((1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ))
      ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ) * (σ ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ)) := by
    have hXsq : (0 : ℝ) ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
    have hss : (1 / 2 : ℝ) ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) := by nlinarith
    nlinarith [hXsq, hss]
  linarith

end

end RHTower
