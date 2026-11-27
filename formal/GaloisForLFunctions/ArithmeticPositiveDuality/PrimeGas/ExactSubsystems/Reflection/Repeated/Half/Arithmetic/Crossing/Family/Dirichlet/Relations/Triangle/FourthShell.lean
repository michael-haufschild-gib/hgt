import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.ShellRank

/-! # Rank bound for relations after adjoining a fourth shell -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Set

/-- Rational combinations of three given weights and one additional weight. -/
def fourEvaluation (w : Fin 3 → ℝ) (y : ℝ) : ((Fin 3 → ℚ) × ℚ) →ₗ[ℚ] ℝ :=
  (Fintype.linearCombination ℚ w).comp (LinearMap.fst ℚ (Fin 3 → ℚ) ℚ) +
    (LinearMap.snd ℚ (Fin 3 → ℚ) ℚ).smulRight y

private theorem kernel_dimension {w : Fin 3 → ℝ} (ind : LinearIndependent ℚ w) (y : ℝ) :
    Module.finrank ℚ (LinearMap.ker (fourEvaluation w y)) ≤ 1 := by
  let L := LinearMap.ker (fourEvaluation w y)
  let p : L →ₗ[ℚ] ℚ := (LinearMap.snd ℚ (Fin 3 → ℚ) ℚ).comp L.subtype
  have inj : Function.Injective p := by
    apply (injective_iff_map_eq_zero p).mpr
    intro v hz
    have last : v.val.2=0 := hz
    have eq : Fintype.linearCombination ℚ w v.val.1 + v.val.2 • y=0 := v.property
    rw [last,zero_smul,add_zero] at eq
    have first := (linearIndependent_iff_injective_fintypeLinearCombination.mp ind) (eq.trans (map_zero _).symm)
    exact Subtype.ext (Prod.ext first last)
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective inj

/-- Two independent rational relations on a four-shell packet force finite
stabilization. The fourth label may even coincide with an earlier label. -/
theorem finite_of_two_relations {t : ℝ} (ht : 0<t) (a b c d : ℕ+)
    (ab : energy a ≠ energy b) (ac : energy a ≠ energy c) (bc : energy b ≠ energy c)
    (two : 1<Module.finrank ℚ (LinearMap.ker
      (fourEvaluation ![shellPower t a,shellPower t b,shellPower t c] (shellPower t d)))) :
    (accumulated t).Finite := by
  by_contra inf
  exact two.not_ge (kernel_dimension (triple_independent ht inf a b c ab ac bc) (shellPower t d))

#print axioms finite_of_two_relations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
