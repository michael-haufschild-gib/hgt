import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimeFlipHasAPositiveDivisorCount

/-!
# A positive renewal kernel for the divisor count

The convolution `g = 1 * ω` has logarithmic derivative `(1 + ω)Λ`.
Both `g` and its renewal kernel are nonnegative for every real sign gauge.
This retains positivity while converting a prime-density question into a renewal equation.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem log_convolution (f g : ArithmeticFunction ℝ) :
    ArithmeticFunction.pmul (f * g) ArithmeticFunction.log =
      ArithmeticFunction.pmul f ArithmeticFunction.log * g +
        f * ArithmeticFunction.pmul g ArithmeticFunction.log := by
  ext n
  change (∑ ab ∈ n.divisorsAntidiagonal, f ab.1 * g ab.2) * Real.log n =
    (∑ ab ∈ n.divisorsAntidiagonal, (f ab.1 * Real.log ab.1) * g ab.2) +
      ∑ ab ∈ n.divisorsAntidiagonal, f ab.1 * (g ab.2 * Real.log ab.2)
  rw [sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun ab hab => ?_
  obtain ⟨habn, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≠ 0 := by intro h; apply hn; rw [← habn, h, zero_mul]
  have hb : ab.2 ≠ 0 := by intro h; apply hn; rw [← habn, h, mul_zero]
  rw [← habn, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  ring

private theorem log_signArithmeticFunction {ω : ℕ → ℝ} (hω : IsSignGauge ω) :
    ArithmeticFunction.pmul (signArithmeticFunction ω) ArithmeticFunction.log =
      ArithmeticFunction.pmul (signArithmeticFunction ω) Λ * signArithmeticFunction ω := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (signArithmeticFunction ω a * Λ a) * signArithmeticFunction ω b)]
  change signArithmeticFunction ω n * Real.log n =
    ∑ d ∈ n.divisors, (signArithmeticFunction ω d * Λ d) * signArithmeticFunction ω (n / d)
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdiv := Nat.mem_divisors.mp hd
  have hq0 : n / d ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv.1) (Nat.pos_of_ne_zero hd0)
  simp only [signArithmeticFunction, ArithmeticFunction.coe_mk, if_neg hn,
    if_neg hd0, if_neg hq0]
  rw [show ω n = ω d * ω (n / d) by rw [← hω.mul hd0 hq0, Nat.mul_div_cancel' hdiv.1]]
  ring

private theorem log_zeta :
    ArithmeticFunction.pmul (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      ArithmeticFunction.log = ArithmeticFunction.log := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [ArithmeticFunction.pmul, ArithmeticFunction.zeta, hn]

/-- The positive renewal coefficient; at a prime power it is `(1 + ω(p)^k) log p`. -/
def signRenewalKernel (ω : ℕ → ℝ) (n : ℕ) : ℝ := (1 + ω n) * Λ n

/-- The positive count retains unit mass at the first integer. -/
theorem signDivisorCount_one {ω : ℕ → ℝ} (hω : IsSignGauge ω) : signDivisorCount ω 1 = 1 := by
  have h := hω.mul (m := 1) (n := 1) (by decide) (by decide)
  have h1 : ω 1 = 1 := by
    simpa only [one_mul, hω.mul_self (by decide : 1 ≠ 0)] using h
  simpa only [signDivisorCount, Nat.divisors_one, sum_singleton] using h1

/-- Both signs at a prime give nonnegative logarithmic-derivative coefficients. -/
theorem signRenewalKernel_nonneg {ω : ℕ → ℝ} (hω : IsSignGauge ω) (n : ℕ) :
    0 ≤ signRenewalKernel ω n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [signRenewalKernel]
  have h := neg_abs_le (ω n)
  rw [abs_eq_one_of_mul_self_eq_one (hω.mul_self hn)] at h
  exact mul_nonneg (by linarith only [h]) ArithmeticFunction.vonMangoldt_nonneg

/-- The exact logarithmic derivative identity of the nonnegative divisor convolution. -/
theorem signDivisorCount_mul_log {ω : ℕ → ℝ} (hω : IsSignGauge ω) (n : ℕ) :
    signDivisorCount ω n * Real.log n =
      ∑ d ∈ n.divisors, signRenewalKernel ω d * signDivisorCount ω (n / d) := by
  let f := signArithmeticFunction ω
  let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let K := ArithmeticFunction.pmul f Λ + Λ
  have hid : ArithmeticFunction.pmul (f * z) ArithmeticFunction.log = K * (f * z) := by
    rw [log_convolution, log_signArithmeticFunction hω, log_zeta,
      ← ArithmeticFunction.vonMangoldt_mul_zeta]
    dsimp only [K, f, z]
    ring
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) hid
  change (f * z) n * Real.log n = (K * (f * z)) n at h
  rw [ArithmeticFunction.mul_apply (f := K) (g := f * z),
    Nat.sum_divisorsAntidiagonal (fun a b => K a * (f * z) b)] at h
  rw [signDivisorCount_eq_convolution]
  refine h.trans (sum_congr rfl fun d hd => ?_)
  rw [signDivisorCount_eq_convolution]
  change ((signArithmeticFunction ω d * Λ d) + Λ d) * (f * z) (n / d) =
    ((1 + ω d) * Λ d) * (f * z) (n / d)
  simp only [signArithmeticFunction, ArithmeticFunction.coe_mk,
    if_neg (Nat.pos_of_mem_divisors hd).ne']
  ring

/-- Summing the coefficient identity gives the positive harmonic renewal equation. -/
theorem signDivisorCount_logMoment_eq {ω : ℕ → ℝ} (hω : IsSignGauge ω) (N : ℕ) :
    ∑ n ∈ Icc 1 N, signDivisorCount ω n / n * Real.log n =
      ∑ d ∈ Icc 1 N, signRenewalKernel ω d / d *
        gaugeHarmonicSum (signDivisorCount ω) (N / d) := by
  have hterm : ∀ n ∈ Icc 1 N, signDivisorCount ω n / n * Real.log n =
      ∑ d ∈ n.divisors, signRenewalKernel ω d / d * (signDivisorCount ω (n / d) / (n / d : ℕ)) := by
    intro n hn
    rw [div_mul_eq_mul_div, signDivisorCount_mul_log hω, sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hdn : d * (n / d) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    have hdnR : (d : ℝ) * (n / d : ℕ) = n := by exact_mod_cast hdn
    rw [div_mul_div_comm, hdnR]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
        signRenewalKernel ω d / d * (signDivisorCount ω (n / d) / (n / d : ℕ)) :=
      sum_congr rfl hterm
    _ = ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d),
        signRenewalKernel ω d / d * (signDivisorCount ω k / k) :=
      RHTower.Sieve.sum_divisors_swap N
        (fun d k => signRenewalKernel ω d / d * (signDivisorCount ω k / k))
    _ = _ := sum_congr rfl fun d _ => (mul_sum _ _ _).symm

end GaloisForLFunctions.ArithmeticCountingPositivity
