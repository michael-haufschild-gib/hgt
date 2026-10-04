import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogRecursion

/-!
# Exact logarithmic covariance balance for the damped divisor source

The actual coefficients have logarithmic convolution kernel
`Λ(d) * (1 - d^(-ε))`. Centering by the literal divisor density leaves an
explicit damped Mangoldt forcing. Divisor interchange and finite Abel summation
give a full quadratic balance at every natural cutoff, retaining the dilation,
lower-prefix and forcing covariances. No sign of their combined contribution
or canonical energy ceiling is assumed.
-/

open ArithmeticFunction Finset
noncomputable section
namespace RHTower

private def pml_twist (ε : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n * (n : ℝ)^(-ε)
  map_zero' := by simp

private theorem pml_twist_apply (ε : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    pml_twist ε f n = f n * (n : ℝ)^(-ε) := rfl

private theorem pml_twist_mul (ε : ℝ) (f g : ArithmeticFunction ℝ) :
    pml_twist ε (f*g) = pml_twist ε f * pml_twist ε g := by
  ext n
  simp only [pml_twist_apply, ArithmeticFunction.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have he := (pmNaturalRpowHom ε).map_mul x.1 x.2
  change ((x.1*x.2 : ℕ) : ℝ)^(-ε) = (x.1 : ℝ)^(-ε)*(x.2 : ℝ)^(-ε) at he
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1] at he
  rw [he]
  ring

private theorem pml_twist_log (ε : ℝ) (f : ArithmeticFunction ℝ) :
    (pml_twist ε f).pmul ArithmeticFunction.log =
      pml_twist ε (f.pmul ArithmeticFunction.log) := by
  ext n
  simp only [pml_twist_apply,pmul_apply]
  ring

private theorem pml_twist_neg (ε : ℝ) (f : ArithmeticFunction ℝ) :
    pml_twist ε (-f) = -pml_twist ε f := by
  ext n
  simp only [pml_twist_apply,ArithmeticFunction.neg_apply,neg_mul]

private def pml_c (ε : ℝ) : ArithmeticFunction ℝ :=
  pml_twist ε ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
    ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

private theorem pml_c_apply (ε : ℝ) (n : ℕ) :
    pml_c ε n = pmPowerDampedDivisorCoeff ε n := by
  rw [pml_c,coe_mul_zeta_apply]
  rfl

private theorem pml_c_log (ε : ℝ) :
    (pml_c ε).pmul ArithmeticFunction.log =
      (vonMangoldt - pml_twist ε vonMangoldt) * pml_c ε := by
  rw [pml_c,pmul_log_mul,pml_twist_log,Sieve.moebius_pmul_log,
    pml_twist_neg,pml_twist_mul,zeta_pmul_log,← vonMangoldt_mul_zeta]
  ring

/-- The exact logarithmic convolution kernel, nonnegative for nonnegative damping. -/
def pmPowerDampedLogKernel (ε : ℝ) (n : ℕ) : ℝ :=
  vonMangoldt n * (1-(n : ℝ)^(-ε))

/-- The explicit divisor forcing introduced by centering the coefficient. -/
def pmPowerDampedLogForcing (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, vonMangoldt d * (d : ℝ)^(-ε)

/-- Logarithmic differentiation of the literal finite divisor convolution. -/
theorem pmPowerDampedDivisorCoeff_mul_log (ε : ℝ) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n * Real.log n =
      ∑ d ∈ n.divisors, pmPowerDampedLogKernel ε d *
        pmPowerDampedDivisorCoeff ε (n/d) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (pml_c_log ε)
  have hsub (m : ℕ) : (vonMangoldt - pml_twist ε vonMangoldt) m =
      vonMangoldt m - vonMangoldt m * (m : ℝ)^(-ε) := rfl
  simp only [pmul_apply,log_apply,ArithmeticFunction.mul_apply,hsub,pml_c_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
    (vonMangoldt a - vonMangoldt a * (a : ℝ)^(-ε)) * pmPowerDampedDivisorCoeff ε b)] at h
  simpa only [pmPowerDampedLogKernel,mul_sub,mul_one] using h

theorem pmPowerDampedLogKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ pmPowerDampedLogKernel ε n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [pmPowerDampedLogKernel]
  apply mul_nonneg vonMangoldt_nonneg
  exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) (by linarith))

theorem pmPowerDampedLogForcing_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ pmPowerDampedLogForcing ε n :=
  Finset.sum_nonneg fun d _ => mul_nonneg vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- Centering retains an explicit damped Mangoldt term with a minus sign. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_log (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε n * Real.log n =
      (∑ d ∈ n.divisors, pmPowerDampedLogKernel ε d *
        pmPowerDampedCenteredDivisorCoeff ε (n/d)) -
      (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcing ε n := by
  unfold pmPowerDampedCenteredDivisorCoeff
  rw [sub_mul,pmPowerDampedDivisorCoeff_mul_log]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  have hb : (∑ d ∈ n.divisors, pmPowerDampedLogKernel ε d) +
      pmPowerDampedLogForcing ε n = Real.log n := by
    unfold pmPowerDampedLogKernel pmPowerDampedLogForcing
    rw [← Finset.sum_add_distrib]
    convert (vonMangoldt_sum (n := n)) using 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [← hb]
  ring

theorem pmPowerDampedCenteredDivisor_log_sum (ε : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n * Real.log n) =
      (∑ d ∈ Icc 1 N, pmPowerDampedLogKernel ε d *
        pmPowerDampedCenteredDivisorPrefix ε (N/d)) -
      (pmPowerDampedDivisorDensity ε).re *
        ∑ d ∈ Icc 1 N, vonMangoldt d * (d : ℝ)^(-ε) * (N/d : ℕ) := by
  simp_rw [pmPowerDampedCenteredDivisorCoeff_mul_log]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,
    Sieve.sum_divisors_swap N (fun d k => pmPowerDampedLogKernel ε d *
      pmPowerDampedCenteredDivisorCoeff ε k)]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.mul_sum]
    rfl
  · congr 1
    unfold pmPowerDampedLogForcing
    rw [Sieve.sum_divisors_swap N (fun d _ => vonMangoldt d * (d : ℝ)^(-ε))]
    apply Finset.sum_congr rfl
    intro d _
    simp [mul_comm]

private theorem pml_prefix_succ (ε : ℝ) (N : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (N+1) =
      pmPowerDampedCenteredDivisorPrefix ε N + pmPowerDampedCenteredDivisorCoeff ε (N+1) := by
  exact Finset.sum_Icc_succ_top (by omega) _

private theorem pml_abel (ε : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n * Real.log n) =
      pmPowerDampedCenteredDivisorPrefix ε N * Real.log N -
        ∑ k ∈ range N, pmPowerDampedCenteredDivisorPrefix ε k *
          (Real.log (k+1)-Real.log k) := by
  induction N with
  | zero => simp [pmPowerDampedCenteredDivisorPrefix]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,pml_prefix_succ,ih]
    push_cast
    ring

/-- The complete natural-cutoff recursion, including every lower prefix and floor. -/
theorem pmPowerDampedCenteredDivisorPrefix_log_balance (ε : ℝ) (N : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε N * Real.log N =
      (∑ d ∈ Icc 1 N, pmPowerDampedLogKernel ε d *
        pmPowerDampedCenteredDivisorPrefix ε (N/d)) +
      (∑ k ∈ range N, pmPowerDampedCenteredDivisorPrefix ε k *
        (Real.log (k+1)-Real.log k)) -
      (pmPowerDampedDivisorDensity ε).re *
        ∑ d ∈ Icc 1 N, vonMangoldt d * (d : ℝ)^(-ε) * (N/d : ℕ) := by
  have h := pmPowerDampedCenteredDivisor_log_sum ε N
  rw [pml_abel] at h
  linarith

/-- Actual prefix covariance with the full logarithmic dilation kernel. -/
def pmPowerDampedLogDilationCovariance (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (pmPowerDampedCenteredDivisorPrefix ε n /
    ((n : ℝ)*(n+1))) *
      (∑ d ∈ Icc 1 n, pmPowerDampedLogKernel ε d *
        pmPowerDampedCenteredDivisorPrefix ε (n/d))

/-- The logarithmic lower-prefix covariance from finite Abel summation. -/
def pmPowerDampedLogPrefixCovariance (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (pmPowerDampedCenteredDivisorPrefix ε n /
    ((n : ℝ)*(n+1))) *
      (∑ k ∈ range n, pmPowerDampedCenteredDivisorPrefix ε k *
        (Real.log (k+1)-Real.log k))

/-- Signed covariance with the complete damped Mangoldt forcing. -/
def pmPowerDampedLogForcingCovariance (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (pmPowerDampedCenteredDivisorPrefix ε n /
    ((n : ℝ)*(n+1))) *
      ∑ d ∈ Icc 1 n, vonMangoldt d * (d : ℝ)^(-ε) * (n/d : ℕ)

/-- Exact logarithmically weighted energy, with all three covariances retained. -/
theorem pmPowerDampedDivisor_log_energy_balance (ε : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log n * pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
      ((n : ℝ)*(n+1))) =
      pmPowerDampedLogDilationCovariance ε N + pmPowerDampedLogPrefixCovariance ε N -
        (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N := by
  unfold pmPowerDampedLogDilationCovariance pmPowerDampedLogPrefixCovariance
    pmPowerDampedLogForcingCovariance
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have h := pmPowerDampedCenteredDivisorPrefix_log_balance ε n
  calc
    _ = (pmPowerDampedCenteredDivisorPrefix ε n / ((n : ℝ)*(n+1))) *
        (pmPowerDampedCenteredDivisorPrefix ε n * Real.log n) := by ring
    _ = _ := by rw [h]; ring

end RHTower
