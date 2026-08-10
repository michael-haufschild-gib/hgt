import GaloisForLFunctions.RHTower.DeningerExpSchwartz
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMoebius

/-!
# The canonical Möbius preimage on the positive ray

Pulling a cochain of the exponentially decreasing source back along `x ↦ log x` produces a
function on the positive ray that decays faster than every power at *both* ends: the exponential
weight `e^{A|t|}` becomes `min(x^A, x^{-A})`.

The canonical Möbius preimage `f_h(x) = ∑_n μ(n) H_h(nx)` is therefore absolutely convergent on
every positive ray, with the single comparison `‖H_h(nx)‖ ≤ (C/x²)/n²`.  No cancellation in `μ` is
used: the two-sided decay of the pullback already does it.

* `deningerLogPull` : the pullback `H_h(x) = h(log x)`.
* `deningerLogPull_norm_le` : **two-sided power decay on the ray.**
* `deningerMobiusRay_summable` : **the Möbius series converges absolutely on every positive ray.**
* `deningerMobiusPreimage` : the canonical preimage `f_h`.
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

noncomputable section

/-! ## The pullback along the logarithm -/

/-- The pullback of a cochain to the positive ray, `H_h(x) = h(log x)`. -/
def deningerLogPull (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := h (Real.log x)

@[simp]
theorem deningerLogPull_apply (h : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerLogPull h x = h (Real.log x) := rfl

/-- **Two-sided power decay of the pullback.**  An exponential-weight bound on the cochain becomes
a bound by `min(x^A, x^{-A})` on the ray, so the pullback is rapidly decreasing at both ends. -/
theorem deningerLogPull_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖deningerLogPull h x‖ ≤ C * Real.exp (-(A * |Real.log x|)) := by
  obtain ⟨C, hC⟩ := hh A 0
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hval : Real.exp (A * |Real.log x|) * ‖h (Real.log x)‖ ≤ max C 0 := by
    have h0 := hC (Real.log x)
    rw [norm_iteratedFDeriv_zero] at h0
    exact le_trans h0 (le_max_left _ _)
  have hepos : (0 : ℝ) < Real.exp (A * |Real.log x|) := Real.exp_pos _
  rw [deningerLogPull_apply, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
  calc ‖h (Real.log x)‖ * Real.exp (A * |Real.log x|)
      = Real.exp (A * |Real.log x|) * ‖h (Real.log x)‖ := by ring
    _ ≤ max C 0 := hval

/-- The pullback at a positive point is bounded by an inverse square in the dilation parameter. -/
theorem deningerLogPull_norm_le_inv_sq {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → ‖deningerLogPull h y‖ ≤ C * y ^ 2 ∧
      ‖deningerLogPull h y‖ ≤ C / y ^ 2 := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le hh 2
  refine ⟨C, hCnn, fun y hy => ?_⟩
  have hbase := hC y hy
  have hlog : Real.exp (Real.log y) = y := Real.exp_log hy
  have hup : Real.exp (-(2 * |Real.log y|)) ≤ y ^ 2 := by
    have hle : -(2 * |Real.log y|) ≤ 2 * Real.log y := by
      have := neg_abs_le (Real.log y)
      linarith [abs_nonneg (Real.log y)]
    have := Real.exp_le_exp.mpr hle
    rwa [show (2 : ℝ) * Real.log y = Real.log y + Real.log y by ring, Real.exp_add, hlog,
      ← pow_two] at this
  have hdown : Real.exp (-(2 * |Real.log y|)) ≤ 1 / y ^ 2 := by
    have hle : -(2 * |Real.log y|) ≤ -(2 * Real.log y) := by
      have := le_abs_self (Real.log y)
      linarith
    have hexp := Real.exp_le_exp.mpr hle
    have hval : Real.exp (-(2 * Real.log y)) = 1 / y ^ 2 := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log y = Real.log y + Real.log y by ring,
        Real.exp_add, hlog, ← pow_two, one_div]
    rwa [hval] at hexp
  refine ⟨le_trans hbase ?_, le_trans hbase ?_⟩
  · exact mul_le_mul_of_nonneg_left hup hCnn
  · have := mul_le_mul_of_nonneg_left hdown hCnn
    rwa [mul_one_div] at this

/-! ## The canonical Möbius preimage -/

/-- **The Möbius series converges absolutely on every positive ray.**  The pullback decays like an
inverse square in the dilation parameter, so the `n`-th term is at most `(C/x²)/n²`. -/
theorem deningerMobiusRay_summable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    Summable fun n : ℕ =>
      ((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ 2 := by positivity
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (C / x ^ 2) * (1 / (n : ℝ) ^ 2)) ?_ ?_
  · exact (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hmu : ((moebius 0 : ℤ) : ℂ) = 0 := by simp
      rw [hmu, zero_mul, norm_zero]
      simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnpos hx
      have hterm := (hC ((n : ℝ) * x) hnx).2
      have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rcases moebius_eq_or n with h1 | h1 | h1 <;> rw [h1] <;> norm_num
      rw [norm_mul]
      have hstep : ‖((moebius n : ℤ) : ℂ)‖ * ‖deningerLogPull h ((n : ℝ) * x)‖
          ≤ 1 * ‖deningerLogPull h ((n : ℝ) * x)‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
      rw [one_mul] at hstep
      refine le_trans hstep (le_trans hterm (le_of_eq ?_))
      rw [mul_pow]
      field_simp

/-- **The canonical Möbius preimage** `f_h(x) = ∑_n μ(n) H_h(nx)` on the positive ray. -/
def deningerMobiusPreimage (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x)

theorem deningerMobiusPreimage_eq (h : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerMobiusPreimage h x
      = ∑' n : ℕ, ((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x) := rfl

/-- The preimage is bounded on every positive ray by the tail of the inverse-square series. -/
theorem deningerMobiusPreimage_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖deningerMobiusPreimage h x‖
      ≤ (C / x ^ 2) * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ 2 := by positivity
  have hsum : Summable fun n : ℕ => (C / x ^ 2) * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  have hbound : ∀ n : ℕ,
      ‖((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x)‖
        ≤ (C / x ^ 2) * (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hmu : ((moebius 0 : ℤ) : ℂ) = 0 := by simp
      rw [hmu, zero_mul, norm_zero]
      simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnpos hx
      have hterm := (hC ((n : ℝ) * x) hnx).2
      have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rcases moebius_eq_or n with h1 | h1 | h1 <;> rw [h1] <;> norm_num
      rw [norm_mul]
      have hstep : ‖((moebius n : ℤ) : ℂ)‖ * ‖deningerLogPull h ((n : ℝ) * x)‖
          ≤ 1 * ‖deningerLogPull h ((n : ℝ) * x)‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
      rw [one_mul] at hstep
      refine le_trans hstep (le_trans hterm (le_of_eq ?_))
      rw [mul_pow]
      field_simp
  refine ⟨C, hCnn, ?_⟩
  refine le_trans (norm_tsum_le_tsum_norm ((deningerMobiusRay_summable hh hx).norm)) ?_
  refine le_trans (Summable.tsum_le_tsum hbound
    ((deningerMobiusRay_summable hh hx).norm) hsum) (le_of_eq ?_)
  rw [Summable.tsum_mul_left _ (Real.summable_one_div_nat_pow.mpr one_lt_two)]

end

end RHTower
