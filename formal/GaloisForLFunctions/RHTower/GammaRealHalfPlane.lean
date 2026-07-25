import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Holomorphy of the archimedean factor on the right half-plane

`Complex.Gammaℝ s = π ^ (-s / 2) * Γ (s / 2)` is differentiable wherever `Γ (s / 2)` is, and the
poles of `Γ` sit at the nonpositive integers.  Hence `Γℝ` is holomorphic on `Re s > 0`.

Mathlib provides `Complex.differentiable_Gammaℝ_inv` for the reciprocal, which is entire; the
direct statement needs the half-plane restriction and is recorded here once for the whole tower.
-/

namespace RHTower

/-- `Γℝ` is differentiable at every point of the open right half-plane. -/
theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hfun : Complex.Gammaℝ = fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext fun z => Complex.Gammaℝ_def z
  rw [hfun]
  apply DifferentiableAt.mul
  · apply DifferentiableAt.const_cpow
    · exact differentiableAt_id.neg.div_const 2
    · exact Or.inl (by exact_mod_cast (Real.pi_ne_zero : Real.pi ≠ 0))
  · have hnon : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have hre := congrArg Complex.re h
      have hdiv : (s / 2).re = s.re / 2 := by
        rw [Complex.div_re]
        simp
        ring
      rw [hdiv] at hre
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma _ hnon).comp s
      (differentiableAt_id.div_const 2)

end RHTower
