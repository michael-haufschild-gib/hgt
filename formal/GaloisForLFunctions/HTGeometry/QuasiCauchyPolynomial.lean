import GaloisForLFunctions.HTGeometry.QuasiCauchyIdentity
import GaloisForLFunctions.HTGeometry.ComplexSecondKind

/-!
# The finite-level identity as a polynomial identity

`P(z)/(z − ξ)` is a polynomial in `z` when `ξ` is a root of `P`: it is the cofactor `P /ₘ (X − ξ)`.
So the weighted Cauchy sum, multiplied by `P(z)`, is a polynomial, and link 188 says it agrees with
`s₀·(R_{n+1} + t·Rₙ)` at every real point off the node set — an infinite set, so the two polynomials
are equal.

Being a polynomial identity it holds at complex arguments as well, which is what the Cauchy transform
needs.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The weighted sum of cofactors at the nodes. -/
noncomputable def quasiCofactorSum (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Polynomial ℝ :=
  ∑ ξ ∈ quasiNodes s n t, C (quasiWeight s n t ξ) * (quasiOrtho s n t /ₘ (X - C ξ))

/-- The cofactor at a node evaluates to the Cauchy quotient. -/
theorem eval_quasiCofactor (n : ℕ) (t : ℝ) {ξ : ℝ} (hξ : ξ ∈ quasiNodes s n t) {z : ℝ}
    (hz : z ≠ ξ) :
    (quasiOrtho s n t /ₘ (X - C ξ)).eval z = (quasiOrtho s n t).eval z / (z - ξ) := by
  have hroot : (quasiOrtho s n t).eval ξ = 0 := (mem_quasiNodes_iff n t ξ).mp hξ
  have hmod : (quasiOrtho s n t) %ₘ (X - C ξ) = 0 := by
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, hroot, map_zero]
  have hadd := Polynomial.modByMonic_add_div (quasiOrtho s n t) (X - C ξ)
  rw [hmod, zero_add] at hadd
  have hev := congrArg (Polynomial.eval z) hadd
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hev
  have hne : z - ξ ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  linarith [hev]

/-- **The polynomial form of the finite-level identity.** -/
theorem quasiCofactorSum_eq (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    quasiCofactorSum s n t = C (s 0) * (secondKind s (n + 1) + C t * secondKind s n) := by
  classical
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  have hinf : ((Set.univ : Set ℝ) \ (quasiNodes s n t : Set ℝ)).Infinite :=
    Set.Infinite.sdiff Set.infinite_univ (quasiNodes s n t).finite_toSet
  refine hinf.mono fun z hz => ?_
  have hznode : z ∉ quasiNodes s n t := by
    intro hc
    exact hz.2 (by simpa using hc)
  have hPz : (quasiOrtho s n t).eval z ≠ 0 := by
    intro hc
    exact hznode ((mem_quasiNodes_iff n t z).mpr hc)
  have hne : ∀ ξ ∈ quasiNodes s n t, z ≠ ξ := by
    intro ξ hξ hc
    exact hznode (hc ▸ hξ)
  have hleft : (quasiCofactorSum s n t).eval z
      = -((quasiOrtho s n t).eval z *
          ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ / (ξ - z)) := by
    rw [quasiCofactorSum, Polynomial.eval_finsetSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_quasiCofactor n t hξ (hne ξ hξ)]
    have hzξ : z - ξ = -(ξ - z) := by ring
    rw [hzξ, div_neg, mul_neg]
    ring
  rw [Set.mem_setOf_eq, hleft, quasiCauchy_identity h n t z hPz]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
  ring

/-- **The identity at a complex argument.** -/
theorem quasiCofactorSum_aeval (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (z : ℂ) :
    Polynomial.aeval z (quasiCofactorSum s n t)
      = ((s 0 : ℝ) : ℂ) * (secondKindC s (n + 1) z + ((t : ℝ) : ℂ) * secondKindC s n z) := by
  rw [quasiCofactorSum_eq h n t]
  simp only [map_mul, map_add, Polynomial.aeval_C, secondKindC]
  norm_num

end HTGeometry
