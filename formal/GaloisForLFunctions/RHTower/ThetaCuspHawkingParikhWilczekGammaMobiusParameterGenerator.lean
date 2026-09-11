import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusLeadingForcing
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Entire coefficient deformation of the actual Gamma/Möbius source

At each fixed positive ray scale, polynomial Gamma moments control the full
coefficient-deformed source and its derivative on every bounded complex
parameter ball. The series is complex differentiable at every parameter.
At zero its derivative is exactly the complete admitted von Mangoldt current
of the original Möbius preimage. Its real part is eventually positive in the
ray scale, so entire parameter admission does not supply stationarity.

These are pointwise ray statements. No global L¹ or L² parameter derivative,
Mellin continuation, spectral parameter identification or Ward balance is
assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace RHTower
open ArithmeticFunction Filter Set
noncomputable section


theorem pwGammaRaySource_polynomial_moment_summable {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * ‖pwGammaRaySource ((n : ℝ) * x)‖) := by
  have hexp := Real.summable_pow_mul_exp_neg_nat_mul (k + 1) hx
  have htail : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k *
      ‖pwGammaRaySource (((n + 1 : ℕ) : ℝ) * x)‖) := by
    have hmajorant := (hexp.comp_injective (i := fun n : ℕ => n + 1)
      (fun _ _ h => Nat.add_right_cancel h)).mul_left
      (Real.sqrt x)
    refine hmajorant.of_nonneg_of_le (fun n => by positivity) ?_
    intro n
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have hsqrt : Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hn1)
    rw [pwGammaRaySource_eq (mul_pos hn hx), Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.sqrt_mul hn.le]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ k *
          ((((n + 1 : ℕ) : ℝ) * Real.sqrt x) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x))) := by
        gcongr
      _ = Real.sqrt x * (((n + 1 : ℕ) : ℝ) ^ (k + 1) *
          Real.exp (-x * ((n + 1 : ℕ) : ℝ))) := by
        rw [pow_succ, neg_mul, mul_comm x]
        ring
  exact (summable_nat_add_iff 1).mp htail

private def pwGammaMobiusTiltTerm (x : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((moebius n : ℤ) : ℂ) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ)) *
    pwGammaRaySource ((n : ℝ) * x)

/-- The literal Gamma/Möbius source with a complex coefficient parameter. -/
def pwGammaMobiusTilt (z : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, pwGammaMobiusTiltTerm x n z

/-- The complete logarithmic current of the same coefficient deformation. -/
def pwGammaMobiusTiltCurrent (z : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, -(Real.log (n : ℝ) : ℂ) * pwGammaMobiusTiltTerm x n z

theorem pwGammaMobiusTilt_zero (x : ℝ) :
    pwGammaMobiusTilt 0 x = pwGammaMobiusPreimage x := by
  simp only [pwGammaMobiusTilt, pwGammaMobiusTiltTerm, neg_zero, zero_mul,
    Complex.exp_zero, mul_one, pwGammaMobiusPreimage]

theorem pwGammaMobiusTiltCurrent_zero (x : ℝ) :
    pwGammaMobiusTiltCurrent 0 x = pwGammaMobiusLogCurrent x := by
  rw [pwGammaMobiusTiltCurrent, pwGammaMobiusLogCurrent]
  refine tsum_congr fun n => ?_
  simp only [pwGammaMobiusTiltTerm, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  push_cast
  ring

private theorem pwGammaMobiusTiltTerm_hasDerivAt (x : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (pwGammaMobiusTiltTerm x n)
      (-(Real.log (n : ℝ) : ℂ) * pwGammaMobiusTiltTerm x n z) z := by
  have h := (((hasDerivAt_id z).neg.mul_const (Real.log (n : ℝ) : ℂ)).cexp.const_mul
    ((moebius n : ℤ) : ℂ)).mul_const (pwGammaRaySource ((n : ℝ) * x))
  change HasDerivAt (fun b : ℂ => ((moebius n : ℤ) : ℂ) *
    Complex.exp (-b * (Real.log (n : ℝ) : ℂ)) * pwGammaRaySource ((n : ℝ) * x)) _ z
  exact h.congr_deriv (by simp only [pwGammaMobiusTiltTerm, Pi.neg_apply, id_eq]; ring)

private theorem pwGammaTiltCoefficient_norm_bound {N n : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (hn : 0 < n) :
    ‖Complex.exp (-z * (Real.log (n : ℝ) : ℂ))‖ ≤ (n : ℝ) ^ N := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hre : -z.re ≤ (N : ℝ) :=
    (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp ((N : ℝ) * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (Real.log_nonneg hn1))
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hnr]

private theorem pwGammaMobiusTiltTerm_norm_bound (x : ℝ) {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (n : ℕ) :
    ‖pwGammaMobiusTiltTerm x n z‖ ≤ (n : ℝ) ^ N *
      ‖pwGammaRaySource ((n : ℝ) * x)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusTiltTerm]
    positivity
  · have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (show |moebius n| ≤ 1 from abs_moebius_le_one)
    rw [pwGammaMobiusTiltTerm, norm_mul, norm_mul]
    have he := pwGammaTiltCoefficient_norm_bound hz hn
    calc
      _ ≤ (1 * (n : ℝ) ^ N) * ‖pwGammaRaySource ((n : ℝ) * x)‖ := by
        gcongr
      _ = _ := by rw [one_mul]

private theorem pwGammaMobiusTiltDerivative_norm_bound (x : ℝ) {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (n : ℕ) :
    ‖-(Real.log (n : ℝ) : ℂ) * pwGammaMobiusTiltTerm x n z‖ ≤
      (n : ℝ) ^ (N + 1) * ‖pwGammaRaySource ((n : ℝ) * x)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog := Real.log_nonneg hn1
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog]
    calc
      _ ≤ Real.log (n : ℝ) * ((n : ℝ) ^ N * ‖pwGammaRaySource ((n : ℝ) * x)‖) :=
        mul_le_mul_of_nonneg_left (pwGammaMobiusTiltTerm_norm_bound x hz n) hlog
      _ ≤ (n : ℝ) * ((n : ℝ) ^ N * ‖pwGammaRaySource ((n : ℝ) * x)‖) := by
        gcongr
        exact Real.log_le_self (Nat.cast_nonneg n)
      _ = _ := by rw [pow_succ]; ring

theorem pwGammaMobiusTilt_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ((moebius n : ℤ) : ℂ) *
      Complex.exp (-z * (Real.log (n : ℝ) : ℂ)) * pwGammaRaySource ((n : ℝ) * x)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  exact Summable.of_norm_bounded (pwGammaRaySource_polynomial_moment_summable hx N)
    (pwGammaMobiusTiltTerm_norm_bound x hN.le)

theorem pwGammaMobiusTiltCurrent_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => -(Real.log (n : ℝ) : ℂ) *
      (((moebius n : ℤ) : ℂ) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ)) *
        pwGammaRaySource ((n : ℝ) * x))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  exact Summable.of_norm_bounded (pwGammaRaySource_polynomial_moment_summable hx (N + 1))
    (pwGammaMobiusTiltDerivative_norm_bound x hN.le)

/-- At every complex parameter, the complete current is the actual complex derivative. -/
theorem pwGammaMobiusTilt_hasDerivAt (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x) (pwGammaMobiusTiltCurrent z x) z := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  have hNpos : (0 : ℝ) < (N : ℝ) := (norm_nonneg z).trans_lt hN
  have hzero : (0 : ℂ) ∈ Metric.ball 0 (N : ℝ) := by
    simpa only [mem_ball_zero_iff, norm_zero] using hNpos
  have hz : z ∈ Metric.ball 0 (N : ℝ) := mem_ball_zero_iff.mpr hN
  have hsum0 : Summable (fun n => pwGammaMobiusTiltTerm x n 0) :=
    pwGammaMobiusTilt_summable 0 hx
  have h := hasDerivAt_tsum_of_isPreconnected
    (pwGammaRaySource_polynomial_moment_summable hx (N + 1)) Metric.isOpen_ball
    (convex_ball (0 : ℂ) (N : ℝ)).isPreconnected
    (fun n b _ => pwGammaMobiusTiltTerm_hasDerivAt x n b)
    (fun n b hb => pwGammaMobiusTiltDerivative_norm_bound x
      (mem_ball_zero_iff.mp hb).le n) hzero hsum0 hz
  exact h

theorem pwGammaMobiusTilt_differentiable {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun b : ℂ => pwGammaMobiusTilt b x) :=
  fun z => (pwGammaMobiusTilt_hasDerivAt z hx).differentiableAt

theorem pwGammaMobiusTilt_deriv (z : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun b : ℂ => pwGammaMobiusTilt b x) z = pwGammaMobiusTiltCurrent z x :=
  (pwGammaMobiusTilt_hasDerivAt z hx).deriv

/-- No positive-collar premise: the original full arithmetic forcing is the derivative at zero. -/
theorem pwGammaMobiusTilt_hasDerivAt_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x) (pwGammaMobiusLogCurrent x) 0 := by
  simpa only [pwGammaMobiusTiltCurrent_zero] using pwGammaMobiusTilt_hasDerivAt 0 hx

theorem pwGammaMobiusTilt_deriv_zero {x : ℝ} (hx : 0 < x) :
    deriv (fun b : ℂ => pwGammaMobiusTilt b x) 0 = pwGammaMobiusLogCurrent x :=
  (pwGammaMobiusTilt_hasDerivAt_zero hx).deriv

/-- The derivative at zero is the admitted full Euler current of the original preimage. -/
theorem pwGammaMobiusTilt_hasDerivAt_euler_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x)
      (∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ) * x)) 0 := by
  rw [pwGammaMobius_connection hx]
  exact pwGammaMobiusTilt_hasDerivAt_zero hx

/-- Entire parameter admission retains a strictly positive derivative for large source scales. -/
theorem pwGammaMobiusTilt_deriv_zero_eventually_pos :
    ∀ᶠ x : ℝ in atTop, 0 < (deriv (fun b : ℂ => pwGammaMobiusTilt b x) 0).re := by
  filter_upwards [pwGammaMobiusLogCurrent_eventually_pos,
    eventually_gt_atTop (0 : ℝ)] with x he hx
  rw [pwGammaMobiusTilt_deriv_zero hx]
  exact he

theorem pwGammaMobiusTilt_eventually_nonconstant :
    ∀ᶠ x : ℝ in atTop, ¬ (∀ b : ℂ, pwGammaMobiusTilt b x = pwGammaMobiusTilt 0 x) := by
  filter_upwards [pwGammaMobiusTilt_deriv_zero_eventually_pos] with x hx
  intro hconstant
  have hf : (fun b : ℂ => pwGammaMobiusTilt b x) =
      (fun _ : ℂ => pwGammaMobiusTilt 0 x) := funext hconstant
  rw [hf, deriv_const, Complex.zero_re] at hx
  exact (lt_irrefl 0) hx

/-- Closed actual-source generator law, with all complex parameters admitted and nonstationarity retained. -/
theorem pwGammaMobiusTilt_entire_generator_closed :
    (∀ x : ℝ, 0 < x →
      Differentiable ℂ (fun b : ℂ => pwGammaMobiusTilt b x) ∧
      pwGammaMobiusTilt 0 x = pwGammaMobiusPreimage x ∧
      HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x) (pwGammaMobiusLogCurrent x) 0 ∧
      HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x)
        (∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ) * x)) 0) ∧
    (∀ᶠ x : ℝ in atTop, 0 < (deriv (fun b : ℂ => pwGammaMobiusTilt b x) 0).re) ∧
    (∀ᶠ x : ℝ in atTop, ¬ (∀ b : ℂ, pwGammaMobiusTilt b x = pwGammaMobiusTilt 0 x)) := by
  exact ⟨fun x hx => ⟨pwGammaMobiusTilt_differentiable hx, pwGammaMobiusTilt_zero x,
    pwGammaMobiusTilt_hasDerivAt_zero hx, pwGammaMobiusTilt_hasDerivAt_euler_zero hx⟩,
    pwGammaMobiusTilt_deriv_zero_eventually_pos, pwGammaMobiusTilt_eventually_nonconstant⟩

end
end RHTower
