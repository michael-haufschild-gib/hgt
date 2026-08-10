import GaloisForLFunctions.RHTower.DeningerMobiusPreimage

/-!
# The canonical preimage decays faster than every power on the far ray

On `[1,∞)` the exponential weight of the source becomes a power of the dilation parameter, so the
pullback obeys `‖H_h(y)‖ ≤ C_k y^{-k}` there.  Feeding that into the Möbius series and factoring
`(nx)^{-k} = n^{-k} x^{-k}` leaves the convergent inverse-power series in `n` and the full power
`x^{-k}` in front: no cancellation in `μ` is used.

This is the far-end half of the rapid-decay estimate for the canonical preimage.

* `deningerLogPull_norm_le_inv_pow` : the pullback on `[1,∞)`.
* `deningerMobiusPreimage_ray_decay` : **`‖f_h(x)‖ ≤ C_k x^{-k}` for `x ≥ 1` and every `k ≥ 2`.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

noncomputable section

/-- **The pullback decays faster than every power on `[1,∞)`.** -/
theorem deningerLogPull_norm_le_inv_pow {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → ‖deningerLogPull h y‖ ≤ C / y ^ k := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le hh (k : ℝ)
  refine ⟨C, hCnn, fun y hy => ?_⟩
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hbase := hC y hy0
  rw [abs_of_nonneg hlog] at hbase
  have hval : Real.exp (-((k : ℝ) * Real.log y)) = 1 / y ^ k := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hy0, one_div]
  rw [hval, mul_one_div] at hbase
  exact hbase

/-- **The canonical preimage decays faster than every power on `[1,∞)`.** -/
theorem deningerMobiusPreimage_ray_decay {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖deningerMobiusPreimage h x‖ ≤ C / x ^ k := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_pow hh k
  have hzeta : Summable fun n : ℕ => 1 / (n : ℝ) ^ k :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hzetann : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ k :=
    tsum_nonneg fun n => by positivity
  refine ⟨C * ∑' n : ℕ, 1 / (n : ℝ) ^ k, mul_nonneg hCnn hzetann, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxk : (0 : ℝ) < x ^ k := by positivity
  have hterm : ∀ n : ℕ,
      ‖((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x)‖
        ≤ (C / x ^ k) * (1 / (n : ℝ) ^ k) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hmu : ((moebius 0 : ℤ) : ℂ) = 0 := by simp
      rw [hmu, zero_mul, norm_zero]
      have : (0 : ℝ) ≤ 1 / ((0 : ℕ) : ℝ) ^ k := by positivity
      positivity
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnx : (1 : ℝ) ≤ (n : ℝ) * x := one_le_mul_of_one_le_of_one_le hn1 hx
      have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rcases moebius_eq_or n with h1 | h1 | h1 <;> rw [h1] <;> norm_num
      rw [norm_mul]
      have hstep : ‖((moebius n : ℤ) : ℂ)‖ * ‖deningerLogPull h ((n : ℝ) * x)‖
          ≤ 1 * ‖deningerLogPull h ((n : ℝ) * x)‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
      rw [one_mul] at hstep
      refine le_trans hstep (le_trans (hC _ hnx) (le_of_eq ?_))
      rw [mul_pow]
      field_simp
  have hsummable : Summable fun n : ℕ => (C / x ^ k) * (1 / (n : ℝ) ^ k) := hzeta.mul_left _
  refine le_trans (norm_tsum_le_tsum_norm ((deningerMobiusRay_summable hh hx0).norm)) ?_
  refine le_trans (Summable.tsum_le_tsum hterm
    ((deningerMobiusRay_summable hh hx0).norm) hsummable) (le_of_eq ?_)
  rw [Summable.tsum_mul_left _ hzeta]
  field_simp

end

end RHTower
