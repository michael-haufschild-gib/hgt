/-
# Exact operator-exponential commutator

Differentiating the conjugated polarization gives the noncommutative Duhamel formula with its
exact unit interval and ordering.  No commutativity or spectral assumption is imposed.
-/
import GaloisForLFunctions.HTGeometry.TwoTimeDuhamelObserverCoercivityLaw

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Exact noncommutative Duhamel identity for a commutator with an exponential. -/
theorem commutator_exp_eq_intervalIntegral_duhamel
    (P X : A) :
    P * exp X - exp X * P =
      ∫ t : ℝ in 0..1,
        exp ((1 - t) • X) * (P * X - X * P) * exp (t • X) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let f : ℝ → A := fun t => exp X * exp (t • (-X)) * P * exp (t • X)
  let f' : ℝ → A := fun t =>
    exp X * exp (t • (-X)) * (P * X - X * P) * exp (t • X)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    dsimp only [f, f']
    have h :=
      (((hasDerivAt_exp_smul_const (-X) t).const_mul (exp X)).mul_const P).mul
        (hasDerivAt_exp_smul_const' X t)
    convert h using 1
    · funext r
      simp only [Pi.mul_apply]
    · noncomm_ring
  have hf_deriv : deriv f = f' := by
    funext t
    exact (hf t).deriv
  have hf'_continuous : Continuous f' := by
    dsimp only [f']
    fun_prop
  have hftc := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1)
    f hf_deriv (fun t _ => (hf t).differentiableAt) hf'_continuous.continuousOn
  have hf_zero : f 0 = exp X * P := by simp [f]
  have hcancel : exp X * exp (-X) = (1 : A) := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl X).neg_right]
    simp
  have hf_one : f 1 = P * exp X := by
    dsimp only [f]
    simp only [one_smul]
    rw [hcancel, one_mul]
  rw [hf_one, hf_zero] at hftc
  rw [← hftc]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [f']
  congr 2
  have hcomm : Commute X (t • (-X)) :=
    ((Commute.refl X).neg_right).smul_right t
  rw [← NormedSpace.exp_add_of_commute hcomm]
  congr 1
  module

end

end GaloisForLFunctions.HTGeometry
