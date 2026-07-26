import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence

/-!
# A rational rank-three period minor exists

The rank-three minor interface asks for two elliptic parameters whose period triple `1, σ, τ` is
rationally independent.  The pair `i, i√2` is such a triple: the real part kills the rational
constant, and irrationality of `√2` kills the remaining rational relation on the imaginary axis.
-/

namespace GaloisForLFunctions

/-- `1`, `i` and `i √2` are rationally independent. -/
theorem linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods Complex.I (Complex.I * (Real.sqrt 2 : ℂ))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [ellipticGammaSourcePeriods, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Rat.smul_def] at hg
  have hre : (g 0 : ℝ) = 0 := by
    have h := congrArg Complex.re hg
    simpa using h
  have him : (g 1 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 := by
    have h := congrArg Complex.im hg
    simpa using h
  have hg2 : g 2 = 0 := by
    by_contra h2
    have h2' : ((g 2 : ℝ)) ≠ 0 := by
      simpa using h2
    have hsqrt : Real.sqrt 2 = ((-g 1 / g 2 : ℚ) : ℝ) := by
      push_cast
      field_simp at him ⊢
      linarith
    exact irrational_sqrt_two ⟨-g 1 / g 2, hsqrt.symm⟩
  have hg1 : g 1 = 0 := by
    rw [hg2] at him
    simpa using him
  have hg0 : g 0 = 0 := by simpa using hre
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- **Rational rank-three minor.**  The parameter pair `i, i√2` realizes the minor interface. -/
theorem multipleEllipticGammaHasRankThreeMinor_I_sqrtTwo :
    MultipleEllipticGammaHasRankThreeMinor
      (![Complex.I, Complex.I * (Real.sqrt 2 : ℂ)] : Fin 2 → ℂ) := by
  refine ⟨0, 1, by decide, ?_⟩
  simpa using linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo

end GaloisForLFunctions
