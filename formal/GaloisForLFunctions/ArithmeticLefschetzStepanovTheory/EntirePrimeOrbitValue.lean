import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialUnitOrbit
import GaloisForLFunctions.RHTower.OrderOneFixedDivisorRigidity

/-!
# Entire extensions of prime-orbit polynomials

Finite exponential sums extend polynomial orbit restrictions to entire
functions. Their exponential growth gives subquadratic Nevanlinna proximity,
which allows fixed-divisor rigidity to identify nonvanishing quotients.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- The entire extension of a finite exponential wave. -/
def entireExpWave {ι : Type*} (s : Finset ι) (c ω : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, c i * Complex.exp (ω i * z)

theorem differentiable_entireExpWave {ι : Type*} (s : Finset ι) (c ω : ι → ℂ) :
    Differentiable ℂ (entireExpWave s c ω) := by
  intro z
  exact DifferentiableAt.fun_sum (fun i _ => by fun_prop)

/-- Finite spectra satisfy the order-one envelope needed for entire-quotient rigidity. -/
theorem entireExpWave_orderOne_bound {ι : Type*} (s : Finset ι) (c ω : ι → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖entireExpWave s c ω z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  classical
  let H : ℝ := ∑ i ∈ s, ‖c i‖
  let A : ℝ := ∑ i ∈ s, ‖ω i‖
  have hH : 0 ≤ H := sum_nonneg fun i _ => norm_nonneg _
  have hA : 0 ≤ A := sum_nonneg fun i _ => norm_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (H + A) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hH hA) hlog2.le
  refine ⟨C, hC, fun z => ?_⟩
  have hb : ‖entireExpWave s c ω z‖ ≤ H * Real.exp (A * ‖z‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [show H * Real.exp (A * ‖z‖) =
      ∑ i ∈ s, ‖c i‖ * Real.exp (A * ‖z‖) by rw [← sum_mul]]
    apply sum_le_sum
    intro i hi
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (single_le_sum (fun j _ => norm_nonneg (ω j)) hi) (norm_nonneg z))
  have hHe : H ≤ Real.exp H := by linarith [Real.add_one_le_exp H]
  have hlin : H + A * ‖z‖ ≤ (H + A) * (1 + ‖z‖) := by
    nlinarith [mul_nonneg hH (norm_nonneg z)]
  have hlog : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hfactor : (H + A) * (1 + ‖z‖) = C * (1 + ‖z‖) * Real.log 2 := by
    dsimp [C]
    field_simp
  calc ‖entireExpWave s c ω z‖ ≤ H * Real.exp (A * ‖z‖) := hb
    _ ≤ Real.exp H * Real.exp (A * ‖z‖) :=
      mul_le_mul_of_nonneg_right hHe (Real.exp_pos _).le
    _ = Real.exp (H + A * ‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((H + A) * (1 + ‖z‖)) := Real.exp_le_exp.mpr hlin
    _ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
      apply Real.exp_le_exp.mpr
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hC (by positivity))

/-- Entire extension of a polynomial restricted to the prime orbit. -/
def entirePrimeOrbitValue {P : Finset Nat.Primes} (F : MvPolynomial P ℂ) (z : ℂ) : ℂ :=
  entireExpWave F.support F.coeff (fun α => ((-frequency α : ℝ) : ℂ) * Complex.I) z

theorem entirePrimeOrbitValue_ofReal {P : Finset Nat.Primes}
    (F : MvPolynomial P ℂ) (t : ℝ) :
    entirePrimeOrbitValue F t = complexOrbitValue F t := by
  rw [complexOrbitValue_eq_wave]
  unfold entirePrimeOrbitValue entireExpWave finiteExpWave
  apply sum_congr rfl
  intro α _
  congr 1
  unfold expChar
  congr 1
  push_cast
  ring

theorem analyticOnNhd_entirePrimeOrbitValue {P : Finset Nat.Primes}
    (F : MvPolynomial P ℂ) : AnalyticOnNhd ℂ (entirePrimeOrbitValue F) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (differentiable_entireExpWave _ _ _)

theorem entirePrimeOrbitValue_proximity {P : Finset Nat.Primes} (F : MvPolynomial P ℂ) :
    ValueDistribution.proximity (entirePrimeOrbitValue F) ⊤ =o[atTop]
      fun r : ℝ => r ^ (2 : ℕ) := by
  obtain ⟨C, hC, hb⟩ := entireExpWave_orderOne_bound F.support F.coeff
    (fun α => ((-frequency α : ℝ) : ℂ) * Complex.I)
  exact _root_.RHTower.OrderOneRigidity.proximity_isLittleO_sq_of_growth hC
    (differentiable_entireExpWave _ _ _) hb

#print axioms entirePrimeOrbitValue_proximity
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
