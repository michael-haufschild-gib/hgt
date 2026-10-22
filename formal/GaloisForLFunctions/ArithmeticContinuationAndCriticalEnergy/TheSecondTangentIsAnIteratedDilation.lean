import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSecondDampingTangentAndConvexity
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationCalculusOnIntegerPrefixes

/-!
# The second tangent is an iterated dilation

The pointwise logarithm is a derivation for Dirichlet convolution (`pmul_log_mul`), and applying it
twice to `μ * 1 = δ` identifies the response of `μ log²`:

`(μ log²) * 1 = Λ * Λ − Λ log`  (`pmul_log_pmul_log_moebius_mul_zeta`).

So the second damping tangent of the source is the source dilated by the **second-order prime
kernel** `K = Λ * Λ − Λ log`, with an explicit correction:

`F_ε(n) = Σ_{j ≤ n} K(j) j^{-ε} A_ε(⌊n/j⌋) + (m₀(ε) Σ_{j ≤ n} K(j) j^{-ε} ⌊n/j⌋ − n m'(ε))`
(`dampedChebyshevSecond_eq_dilation`).

Together with the first-order law this puts the whole convexity criterion in dilation coordinates:
the condition `−‖E_ε‖_T² ≤ ⟪A_ε, F_ε⟫_T` of the constant-free criterion is a statement about one
*iterated* prime dilation of the literal source against itself
(`riemannHypothesis_of_secondKernel_dilation_pairing_ge`).  The kernel is explicit: a prime-pair
convolution minus a logarithmically weighted prime row, the first appearance of a second-order
prime object in the continuation layer.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The logarithm is a derivation -/

/-- **Leibniz rule.**  The pointwise logarithm is a derivation for Dirichlet convolution. -/
theorem pmul_log_mul (f g : ArithmeticFunction ℝ) :
    pmul log (f * g) = pmul log f * g + f * pmul log g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have ha : x.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hprod
    exact hn0 hprod.symm
  have hb : x.2 ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hprod
    exact hn0 hprod.symm
  have hlog : ArithmeticFunction.log n =
      ArithmeticFunction.log x.1 + ArithmeticFunction.log x.2 := by
    simp only [ArithmeticFunction.log_apply]
    rw [← hprod]
    push_cast
    rw [Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
  rw [hlog]
  ring

theorem pmul_log_one : pmul log (1 : ArithmeticFunction ℝ) = 0 := by
  ext n
  rcases eq_or_ne n 1 with rfl | hn
  · simp [ArithmeticFunction.pmul_apply]
  · simp [ArithmeticFunction.pmul_apply, hn]

theorem pmul_log_zeta : pmul log (↑ζ : ArithmeticFunction ℝ) = log := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp

/-- The response of `μ log` is `−Λ`. -/
theorem pmul_log_moebius_mul_zeta :
    pmul log (↑moebius : ArithmeticFunction ℝ) * ↑ζ = -Λ := by
  have hD := pmul_log_mul (↑moebius : ArithmeticFunction ℝ) (↑ζ)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, pmul_log_one, pmul_log_zeta,
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt] at hD
  exact eq_neg_of_add_eq_zero_left hD.symm

/-- **The response of `μ log²` is the second-order prime kernel.** -/
theorem pmul_log_pmul_log_moebius_mul_zeta :
    pmul log (pmul log (↑moebius : ArithmeticFunction ℝ)) * ↑ζ = Λ * Λ - pmul log Λ := by
  have hD := pmul_log_mul (pmul log (↑moebius : ArithmeticFunction ℝ)) (↑ζ)
  rw [pmul_log_moebius_mul_zeta, pmul_log_zeta] at hD
  have hneg : pmul log (-Λ : ArithmeticFunction ℝ) = -(pmul log Λ) := by
    ext n
    simp [ArithmeticFunction.pmul_apply]
  have hside : pmul log (↑moebius : ArithmeticFunction ℝ) * log = -(Λ * Λ) := by
    calc pmul log (↑moebius : ArithmeticFunction ℝ) * log
        = pmul log (↑moebius : ArithmeticFunction ℝ) * (Λ * ↑ζ) := by
          rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      _ = (pmul log (↑moebius : ArithmeticFunction ℝ) * ↑ζ) * Λ := by ring
      _ = -(Λ * Λ) := by rw [pmul_log_moebius_mul_zeta, neg_mul]
  rw [hneg, hside] at hD
  linear_combination (norm := abel) -hD

/-! ## §2. The second-order prime kernel and the damped convolution -/

/-- The second-order prime kernel `K = Λ * Λ − Λ log`. -/
def secondPrimeKernel : ArithmeticFunction ℝ := Λ * Λ - pmul log Λ

/-- Its damped weight `K(j) j^{-ε}`. -/
def dampedSecondPrimeWeight (ε : ℝ) (j : ℕ) : ℝ := secondPrimeKernel j * (j : ℝ) ^ (-ε)

/-- **The second tangent row is the source row dilated by the second-order prime kernel.** -/
theorem dampedVonMangoldtSecond_eq_dilation_convolution (ε : ℝ) (k : ℕ) :
    dampedVonMangoldtSecond ε k =
      ∑ j ∈ k.divisors, dampedSecondPrimeWeight ε j *
        pmPowerDampedDivisorCoeff ε (k / j) := by
  have hX : pmul log (pmul log (↑moebius : ArithmeticFunction ℝ)) =
      secondPrimeKernel * (↑moebius : ArithmeticFunction ℝ) := by
    have h := pmul_log_pmul_log_moebius_mul_zeta
    calc pmul log (pmul log (↑moebius : ArithmeticFunction ℝ))
        = pmul log (pmul log (↑moebius : ArithmeticFunction ℝ)) *
            ((↑ζ : ArithmeticFunction ℝ) * ↑moebius) := by
          rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
      _ = (pmul log (pmul log (↑moebius : ArithmeticFunction ℝ)) * ↑ζ) * ↑moebius := by
          rw [mul_assoc]
      _ = secondPrimeKernel * (↑moebius : ArithmeticFunction ℝ) := by
          rw [h, secondPrimeKernel]
  have hcoeff : ∀ m : ℕ, pmPowerDampedDivisorCoeff ε m =
      (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) m :=
    pmPowerDampedDivisorCoeff_eq_mul ε
  have hleft : dampedVonMangoldtSecond ε k =
      (dampedTwist ε (pmul log (pmul log (↑moebius : ArithmeticFunction ℝ))) * ↑ζ) k := by
    rw [ArithmeticFunction.coe_mul_zeta_apply, dampedVonMangoldtSecond]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [dampedTwist_apply]
    simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply,
      ArithmeticFunction.intCoe_apply]
    ring
  rw [hleft, hX, dampedTwist_mul, mul_assoc, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => dampedTwist ε secondPrimeKernel a *
      (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) b)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [dampedTwist_apply, ← hcoeff, dampedSecondPrimeWeight]

/-! ## §3. The second tangent as an iterated dilation of the source -/

/-- The floor sum of the damped second-order kernel. -/
def dampedSecondPrimeFloorSum (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, dampedSecondPrimeWeight ε j * ((n / j : ℕ) : ℝ)

/-- **The second tangent is the source dilated by the second-order prime kernel**, with an explicit
correction from the two centrings. -/
theorem dampedChebyshevSecond_eq_dilation (ε : ℝ) (n : ℕ) :
    dampedChebyshevSecond ε n =
      (∑ j ∈ Icc 1 n, dampedSecondPrimeWeight ε j *
          pmPowerDampedCenteredDivisorPrefix ε ((n / j : ℕ))) +
        ((pmPowerDampedDivisorDensity ε).re * dampedSecondPrimeFloorSum ε n -
          dampedReadoutSecond ε * n) := by
  have hconv : (∑ k ∈ Icc 1 n, dampedVonMangoldtSecond ε k) =
      ∑ j ∈ Icc 1 n, dampedSecondPrimeWeight ε j *
        ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m := by
    rw [← sum_Icc_divisor_convolution_eq_dilation (dampedSecondPrimeWeight ε)
      (pmPowerDampedDivisorCoeff ε) n]
    exact Finset.sum_congr rfl fun k _ => dampedVonMangoldtSecond_eq_dilation_convolution ε k
  have hcentre : ∀ j ∈ Icc 1 n,
      dampedSecondPrimeWeight ε j * ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m =
        dampedSecondPrimeWeight ε j * pmPowerDampedCenteredDivisorPrefix ε (n / j) +
          (pmPowerDampedDivisorDensity ε).re *
            (dampedSecondPrimeWeight ε j * ((n / j : ℕ) : ℝ)) := by
    intro j _
    rw [pmPowerDampedCenteredDivisorPrefix_eq]
    ring
  unfold dampedChebyshevSecond dampedSecondPrimeFloorSum
  rw [hconv, Finset.sum_congr rfl hcentre, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The convexity criterion in dilation coordinates.**  The constant-free criterion asks that the
source, paired with its own iterated prime dilation and the explicit correction, stay above minus
the tangent energy. -/
theorem riemannHypothesis_of_secondKernel_dilation_pairing_ge
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      -(pronicNorm T (dampedChebyshevError ε) ^ 2) ≤
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
          (fun n => (∑ j ∈ Icc 1 n, dampedSecondPrimeWeight ε j *
              pmPowerDampedCenteredDivisorPrefix ε ((n / j : ℕ))) +
            ((pmPowerDampedDivisorDensity ε).re * dampedSecondPrimeFloorSum ε n -
              dampedReadoutSecond ε * n))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_second_tangent_pairing_ge fun T ε hε hε2 => ?_
  have hfun : (dampedChebyshevSecond ε) =
      fun n => (∑ j ∈ Icc 1 n, dampedSecondPrimeWeight ε j *
          pmPowerDampedCenteredDivisorPrefix ε ((n / j : ℕ))) +
        ((pmPowerDampedDivisorDensity ε).re * dampedSecondPrimeFloorSum ε n -
          dampedReadoutSecond ε * n) :=
    funext (dampedChebyshevSecond_eq_dilation ε)
  rw [hfun]
  exact h T ε hε hε2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
