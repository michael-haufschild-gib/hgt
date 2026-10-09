import Mathlib.Analysis.Complex.Polynomial.Basic

namespace GaloisForLFunctions.HTGeometry

/-- Finite critical-value sets remain finite after a polynomial change of variable. -/
theorem finite_critical_values_comp_polynomial {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hcrit : (F '' {z | deriv F z = 0}).Finite)
    (P : Polynomial ℂ) :
    ((fun z => F (P.eval z)) '' {z | deriv (fun z => F (P.eval z)) z = 0}).Finite := by
  classical
  by_cases hP : P.derivative = 0
  · have heq := Polynomial.eq_C_of_derivative_eq_zero hP
    apply (Set.finite_singleton (F (P.coeff 0))).subset
    rintro w ⟨z, _, rfl⟩
    simp only [Set.mem_singleton_iff]
    congr 1
    conv_lhs => rw [heq]
    simp
  · have hpfin := Polynomial.finite_setOf_isRoot hP
    apply (hcrit.union (hpfin.image (fun z => F (P.eval z)))).subset
    rintro w ⟨z, hz, rfl⟩
    have hd : deriv (fun z => F (P.eval z)) z =
        deriv F (P.eval z) * P.derivative.eval z :=
      ((hF (P.eval z)).hasDerivAt.comp z (P.hasDerivAt z)).deriv
    rw [Set.mem_setOf_eq, hd] at hz
    rcases mul_eq_zero.1 hz with houter | hinner
    · exact Or.inl ⟨P.eval z, houter, rfl⟩
    · exact Or.inr ⟨z, hinner, rfl⟩

end GaloisForLFunctions.HTGeometry
