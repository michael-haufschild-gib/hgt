import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The generalised von Mangoldt function of an arithmetic function

Halász's theorem is proved by iterating the identity `f·log = f * Λ_f`, where `Λ_f` is the unique
arithmetic function satisfying it.  When `f 1` is invertible the Dirichlet inverse exists, so `Λ_f` is
simply `f⁻¹ * (f·log)`, and the identity is associativity.

For the classical `f = 1` this is `Λ` itself, since `log = ζ * Λ`.  The point of the general version is
that the recursion it supports never forms a Dirichlet polynomial and never uses a mean-value theorem, so
it avoids the regime obstruction of the contour route.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

/-- The generalised von Mangoldt function of `f`: the unique solution of `f·log = f * Λ_f`. -/
noncomputable def vonMangoldtOf (f : ArithmeticFunction ℝ) (hf : Invertible (f 1)) :
    ArithmeticFunction ℝ :=
  dirichletInverse f hf * pmul f ArithmeticFunction.log

/-- **The defining identity.**  `f·log = f * Λ_f`. -/
theorem pmul_log_eq_mul_vonMangoldtOf (f : ArithmeticFunction ℝ) (hf : Invertible (f 1)) :
    pmul f ArithmeticFunction.log = f * vonMangoldtOf f hf := by
  rw [vonMangoldtOf, ← mul_assoc, self_mul_dirichletInverse, one_mul]

/-- **Uniqueness.**  Any solution of the defining identity is the generalised von Mangoldt
function. -/
theorem eq_vonMangoldtOf_of_mul_eq (f g : ArithmeticFunction ℝ) (hf : Invertible (f 1))
    (hg : f * g = pmul f ArithmeticFunction.log) :
    g = vonMangoldtOf f hf := by
  have h := congrArg (fun h : ArithmeticFunction ℝ => dirichletInverse f hf * h) hg
  rw [← mul_assoc, dirichletInverse_mul_self, one_mul] at h
  rw [h, vonMangoldtOf]

/-- The classical case: for the zeta function the generalised von Mangoldt function is `Λ`. -/
theorem vonMangoldtOf_zeta
    (hf : Invertible (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) 1)) :
    vonMangoldtOf ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) hf = Λ := by
  refine (eq_vonMangoldtOf_of_mul_eq _ Λ hf ?_).symm
  rw [zeta_mul_vonMangoldt]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [pmul, ArithmeticFunction.zeta_apply, hn.ne']

end GaloisForLFunctions.HTGeometry
