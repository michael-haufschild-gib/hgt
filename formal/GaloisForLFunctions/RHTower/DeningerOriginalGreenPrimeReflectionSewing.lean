import GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm

/-!
# Prime and reflection sewing of the original Green source

Restoring the literal prime Euler denominator gives a prime-independent,
reflection-even scalar for the full meromorphic damping family and its forced
leading coefficient. On the admitted half-plane the identity holds for the
actual Green Mellin integral. This does not construct a zero-damping source
vector or force physical-reader vanishing.
-/

open Complex Filter Topology
namespace RHTower

noncomputable section

/-- Reflection symmetry of the centered Gaussian Mellin source. -/
theorem deningerMeyerReflectedLogGaussianSource_mellin_reflect (s : ℂ) :
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (1 - s) =
      deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s := by
  rw [deningerMeyerReflectedLogGaussianSource_mellin,
    deningerMeyerReflectedLogGaussianSource_mellin]
  congr 1
  ring

/-- Common meromorphic scalar after restoring the literal prime denominator. -/
def deningerOriginalPrimeGreenSewnScalar (rho : XiDivisorSupport) (a : ℂ) : ℂ :=
  deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
    (riemannZeta (a + (rho : ℂ)) * riemannZeta (a + (1 - (rho : ℂ))))

/-- Xi reflection fixes the sewn scalar at every damping parameter. -/
theorem deningerOriginalPrimeGreenSewnScalar_reflect
    (rho : XiDivisorSupport) (a : ℂ) :
    deningerOriginalPrimeGreenSewnScalar (xiZeroReflectEquiv rho) a =
      deningerOriginalPrimeGreenSewnScalar rho a := by
  unfold deningerOriginalPrimeGreenSewnScalar
  simp only [xiZeroReflectEquiv_apply]
  rw [deningerMeyerReflectedLogGaussianSource_mellin_reflect]
  congr 1
  ring

/-- Every prime continuation sews to the same scalar. -/
theorem deningerOriginalPrimeGreenDampingContinuation_sewn
    (p : Nat.Primes) (rho : XiDivisorSupport) (a : ℂ) :
    deningerOriginalPrimeGreenDampingContinuation p rho a *
      (1 - (p : ℂ) ^ (-(rho : ℂ))) =
    deningerOriginalPrimeGreenSewnScalar rho a := by
  rw [deningerOriginalPrimeGreenDampingContinuation,
    deningerOriginalPrimeGreenSewnScalar]
  have hp := deningerOriginalGreen_prime_denominator_ne_zero p
    (xi_divisor_support_re_mem_open_unit rho).1
  field_simp [hp]

/-- Continuations at two primes and reflected Xi points share one sewn scalar. -/
theorem deningerOriginalPrimeGreenDampingContinuation_prime_reflect_sewn
    (p q : Nat.Primes) (rho : XiDivisorSupport) (a : ℂ) :
    deningerOriginalPrimeGreenDampingContinuation p rho a *
        (1 - (p : ℂ) ^ (-(rho : ℂ))) =
      deningerOriginalPrimeGreenDampingContinuation q (xiZeroReflectEquiv rho) a *
        (1 - (q : ℂ) ^ (-(xiZeroReflectEquiv rho : ℂ))) := by
  calc
    _ = deningerOriginalPrimeGreenSewnScalar rho a :=
      deningerOriginalPrimeGreenDampingContinuation_sewn p rho a
    _ = deningerOriginalPrimeGreenSewnScalar (xiZeroReflectEquiv rho) a :=
      (deningerOriginalPrimeGreenSewnScalar_reflect rho a).symm
    _ = _ :=
      (deningerOriginalPrimeGreenDampingContinuation_sewn q
        (xiZeroReflectEquiv rho) a).symm

/-- Sewing holds for the admitted literal Green Mellin integral. -/
theorem deningerDampedOriginalPrimeGreen_mellin_sewn
    (a : {a : ℝ // 1 < a}) (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin
        (deningerDampedOriginalPrimeGreen ⟨a.val, by linarith [a.property]⟩ p)
        (rho : ℂ) * (1 - (p : ℂ) ^ (-(rho : ℂ))) =
      deningerOriginalPrimeGreenSewnScalar rho (a.val : ℂ) := by
  rw [← deningerOriginalPrimeGreenDampingContinuation_eq_literal a p rho]
  exact deningerOriginalPrimeGreenDampingContinuation_sewn p rho (a.val : ℂ)

/-- The forced leading coefficient obeys the same prime sewing law. -/
theorem deningerOriginalPrimeGreenZeroDampingCoefficient_sewn
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenZeroDampingCoefficient p rho *
      (1 - (p : ℂ) ^ (-(rho : ℂ))) =
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
      (meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) *
        meromorphicTrailingCoeffAt riemannZeta (1 - (rho : ℂ))) := by
  rw [deningerOriginalPrimeGreenZeroDampingCoefficient]
  have hp := deningerOriginalGreen_prime_denominator_ne_zero p
    (xi_divisor_support_re_mem_open_unit rho).1
  field_simp [hp]

/-- Forced leading coefficients sew across arbitrary primes and Xi reflection. -/
theorem deningerOriginalPrimeGreenZeroDampingCoefficient_prime_reflect_sewn
    (p q : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenZeroDampingCoefficient p rho *
      (1 - (p : ℂ) ^ (-(rho : ℂ))) =
    deningerOriginalPrimeGreenZeroDampingCoefficient q (xiZeroReflectEquiv rho) *
      (1 - (q : ℂ) ^ (-(xiZeroReflectEquiv rho : ℂ))) := by
  rw [deningerOriginalPrimeGreenZeroDampingCoefficient_sewn,
    deningerOriginalPrimeGreenZeroDampingCoefficient_sewn]
  simp only [xiZeroReflectEquiv_apply]
  rw [deningerMeyerReflectedLogGaussianSource_mellin_reflect]
  congr 1
  ring

/-- The completed scalar germ retains prime and reflection sewing at zero damping. -/
theorem deningerOriginalPrimeGreenZeroDampingRegularization_prime_reflect_sewn
    (p q : Nat.Primes) (rho : XiDivisorSupport) (a : ℂ) :
    deningerOriginalPrimeGreenZeroDampingRegularization p rho a *
        (1 - (p : ℂ) ^ (-(rho : ℂ))) =
      deningerOriginalPrimeGreenZeroDampingRegularization q
          (xiZeroReflectEquiv rho) a *
        (1 - (q : ℂ) ^ (-(xiZeroReflectEquiv rho : ℂ))) := by
  by_cases ha : a = 0
  · subst a
    rw [deningerOriginalPrimeGreenZeroDampingRegularization_zero,
      deningerOriginalPrimeGreenZeroDampingRegularization_zero]
    exact deningerOriginalPrimeGreenZeroDampingCoefficient_prime_reflect_sewn p q rho
  · simp only [deningerOriginalPrimeGreenZeroDampingRegularization, if_neg ha,
      xiSupportMultiplicity_reflect]
    calc
      _ = a ^ (2 * xiSupportMultiplicity rho) *
          (deningerOriginalPrimeGreenDampingContinuation p rho a *
            (1 - (p : ℂ) ^ (-(rho : ℂ)))) := by ring
      _ = a ^ (2 * xiSupportMultiplicity rho) *
          (deningerOriginalPrimeGreenDampingContinuation q
            (xiZeroReflectEquiv rho) a *
            (1 - (q : ℂ) ^ (-(xiZeroReflectEquiv rho : ℂ)))) := by
              rw [deningerOriginalPrimeGreenDampingContinuation_prime_reflect_sewn]
      _ = _ := by ring

end

end RHTower
