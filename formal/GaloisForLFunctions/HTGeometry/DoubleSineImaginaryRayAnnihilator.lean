import GaloisForLFunctions.HTGeometry.DoubleSineCoordinateAnnihilator
import GaloisForLFunctions.HTGeometry.DoubleSineImaginaryRaySource

/-!
# The double-sine translation annihilator on the imaginary ray

Specialising the frame to periods `i a`, `i b` on the positive imaginary ray with `a/b` irrational
discharges every hypothesis of the annihilator theorem: the two periods lie in the upper half-plane,
so the Barnes cone construction supplies a source with exact cotangent defects; their cylinder
frequencies are rationally independent; the second dilation is non-torsion; and two translations
along a common ray with irrational ratio have constant common fixed field.

The result is a closed statement: a meromorphic source exists whose translation annihilator modulo
the differentially algebraic sector over `ℂ(z)` is exactly the augmentation ideal, so total exponent
is the complete invariant.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine translation annihilator, unconditionally.**  For periods `i a`, `i b` on the
positive imaginary ray with `a/b` irrational there is a meromorphic source whose two structural
translation defects are the cotangents of the other period, up to a constant, and whose translation
annihilator modulo the differentially algebraic sector over `ℂ(z)` is exactly the augmentation
ideal.  Equivalently: a translation operator sends the source into the differentially algebraic
sector precisely when its coefficients sum to zero, so no single structural translate is
differentially algebraic. -/
theorem daTranslationAnnihilator_doubleSine_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) :
    ∃ (M : meroField (Set.univ : Set ℂ)) (cst : ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
      addTranslationMeroEquiv (Complex.I * (b : ℂ)) M - M
          = -periodCotMero (Complex.I * (a : ℂ)) + ratMero (RatFunc.C cst) ∧
      {Q : MvPolynomial (Fin 2) ℂ |
          DifferentialAlgebraicOver (RatFunc ℂ)
            (transApply ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] Q M)}
        = (augIdeal 2 : Set (MvPolynomial (Fin 2) ℂ)) ∧
      ∀ Q : MvPolynomial (Fin 2) ℂ,
        DifferentialAlgebraicOver (RatFunc ℂ)
            (transApply ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] Q M)
          ↔ ∑ n ∈ Q.support, MvPolynomial.coeff n Q = 0 := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hωdef
  have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by rw [hω0]; exact mul_ne_zero Complex.I_ne_zero haC
  have hω1ne : ω 1 ≠ 0 := by rw [hω1]; exact mul_ne_zero Complex.I_ne_zero hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by rw [hldef, hω0]; simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by rw [hldef, hω1]; simp
  have hper0 : Complex.exp (l 0 * ω 0) = 1 := by
    rw [hl0, div_mul_cancel₀ _ hω0ne]; simp
  have hper1 : Complex.exp (l 1 * ω 1) = 1 := by
    rw [hl1, div_mul_cancel₀ _ hω1ne]; simp
  have hprod : l 1 * ω 0 = 2 * (Real.pi : ℂ) * Complex.I * ((a / b : ℝ) : ℂ) := by
    rw [hl1, hω1, hω0]
    push_cast
    field_simp
  have htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1 := by
    intro n hn
    rw [hprod]
    exact exp_two_pi_I_zpow_ne_one hirr hn
  have hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z := by
    intro z hz0 hz1
    rw [hω0] at hz0
    rw [hω1] at hz1
    exact exists_constant_of_two_imaginaryPeriods_fixed hirr hz0 hz1
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_imaginaryRay ha hb
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]; exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]; exact hM1
  refine ⟨M, cst, hM0, hM1, ?_, ?_⟩
  · have h := daTranslationAnnihilator_doubleSine_eq_augIdeal hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1
    exact h
  · intro Q
    have h := differentialAlgebraicOver_transApply_doubleSine_iff hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 Q
    exact h

end

end GaloisForLFunctions.HTGeometry
