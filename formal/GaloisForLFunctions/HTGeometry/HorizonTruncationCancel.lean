import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Cancelling a factor that is invertible at the origin from a truncation

A polynomial with nonzero constant term is coprime to the variable, hence to every power of it.  So
it may be cancelled from a divisibility by a power of the variable: it is invertible modulo that
power.

This is what lets a common factor be removed from a truncated tangent relation without leaving the
class of low-degree solutions.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

theorem not_X_dvd_of_coeff_zero_ne_zero {g : K[X]} (hg : g.coeff 0 ≠ 0) :
    ¬ (Polynomial.X ∣ g) := by
  intro h
  exact hg (Polynomial.X_dvd_iff.1 h)

/-- **A polynomial with nonzero constant term is coprime to the variable.** -/
theorem isCoprime_X_of_coeff_zero_ne_zero {g : K[X]} (hg : g.coeff 0 ≠ 0) :
    IsCoprime (Polynomial.X : K[X]) g :=
  (Polynomial.irreducible_X.coprime_iff_not_dvd).2 (not_X_dvd_of_coeff_zero_ne_zero hg)

/-- **Cancelling a factor invertible at the origin from a truncation.** -/
theorem dvd_of_mul_dvd_of_coeff_zero_ne_zero {g p : K[X]} {L : ℕ}
    (hg : g.coeff 0 ≠ 0) (h : (Polynomial.X : K[X]) ^ L ∣ g * p) :
    (Polynomial.X : K[X]) ^ L ∣ p := by
  have hcop : IsCoprime ((Polynomial.X : K[X]) ^ L) g :=
    (isCoprime_X_of_coeff_zero_ne_zero hg).pow_left
  exact hcop.dvd_of_dvd_mul_left h

/-- **Dividing a truncated tangent relation by a common factor invertible at the origin.**  If the
two components of a vertical tangent pair share a factor with nonzero constant term, the quotients
satisfy the same truncated relation, so they are again a low tangent pair. -/
theorem tangent_relation_of_common_factor {U V A B g U' V' : K[X]} {L : ℕ}
    (hg : g.coeff 0 ≠ 0) (hU : U = g * U') (hV : V = g * V')
    (hrel : (Polynomial.X : K[X]) ^ L ∣ U * B + A * V) :
    (Polynomial.X : K[X]) ^ L ∣ U' * B + A * V' := by
  refine dvd_of_mul_dvd_of_coeff_zero_ne_zero hg ?_
  rw [show g * (U' * B + A * V') = U * B + A * V by rw [hU, hV]; ring]
  exact hrel

end GaloisForLFunctions.HTGeometry
