import GaloisForLFunctions.HTGeometry.ConjugateReflectionRecovery

set_option autoImplicit false

/-!
# Exact inversion of a source mixed with its conjugate

The same determinant that controls a reflection residual gives its inverse
and its output compatibility condition.  The statements include zero and
equal-modulus coefficients without assuming nondegeneracy.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The adjugate numerator for conjugate reflection recovery. -/
def conjugateReflectionAdjugate (A B w : ℂ) : ℂ := conj A * w + B * conj w

theorem conjugateReflectionResidual_adjugate (A B w : ℂ) :
    conjugateReflectionResidual A B (conjugateReflectionAdjugate A B w) =
      ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) * w := by
  simp only [conjugateReflectionResidual, conjugateReflectionAdjugate,
    map_add, map_mul, conj_conj, Complex.ofReal_sub,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- Totalized inverse: its value at a singular determinant is zero. -/
def conjugateReflectionInverse (A B w : ℂ) : ℂ :=
  conjugateReflectionAdjugate A B w / (Complex.normSq A - Complex.normSq B : ℝ)

theorem conjugateReflectionResidual_inverse (A B w : ℂ) :
    conjugateReflectionResidual A B (conjugateReflectionInverse A B w) =
      if Complex.normSq A = Complex.normSq B then 0 else w := by
  by_cases h : Complex.normSq A = Complex.normSq B
  · simp [conjugateReflectionInverse, h, conjugateReflectionResidual]
  · rw [if_neg h]
    have hd : ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr h)
    unfold conjugateReflectionInverse conjugateReflectionResidual
    simp only [map_div₀, conj_ofReal]
    rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div,
      ← conjugateReflectionResidual, conjugateReflectionResidual_adjugate]
    field_simp

theorem conjugateReflectionInverse_residual (A B z : ℂ) :
    conjugateReflectionInverse A B (conjugateReflectionResidual A B z) =
      if Complex.normSq A = Complex.normSq B then 0 else z := by
  unfold conjugateReflectionInverse conjugateReflectionAdjugate
  rw [conjugateReflectionResidual_recovery]
  by_cases h : Complex.normSq A = Complex.normSq B
  · simp [h]
  · rw [if_neg h]
    have hd : ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr h)
    field_simp

/-- No outputs are lost exactly when the reflection coefficients have
different magnitudes. -/
theorem conjugateReflectionResidual_surjective_iff (A B : ℂ) :
    Function.Surjective (conjugateReflectionResidual A B) ↔
      Complex.normSq A ≠ Complex.normSq B := by
  constructor
  · intro hs heq
    obtain ⟨z, hz⟩ := hs 1
    obtain ⟨w, hw⟩ := hs I
    have hre := conjugateReflectionResidual_recovery A B z
    have him := conjugateReflectionResidual_recovery A B w
    rw [hz, heq] at hre
    rw [hw, heq] at him
    simp only [map_one, mul_one, sub_self, Complex.ofReal_zero, zero_mul] at hre
    simp only [conj_I, sub_self, Complex.ofReal_zero, zero_mul] at him
    have hsub : conj A - B = 0 := by
      apply (mul_eq_zero.mp (show I * (conj A - B) = 0 by
        linear_combination him)).resolve_left I_ne_zero
    have hAconj : conj A = 0 := by linear_combination (hre + hsub) / 2
    have hA : A = 0 := by simpa using congrArg conj hAconj
    have hB : B = 0 := by simpa [hA] using hre
    simp [conjugateReflectionResidual, hA, hB] at hz
  · intro h w
    exact ⟨conjugateReflectionInverse A B w, by
      rw [conjugateReflectionResidual_inverse, if_neg h]⟩

theorem conjugateReflectionResidual_bijective_iff (A B : ℂ) :
    Function.Bijective (conjugateReflectionResidual A B) ↔
      Complex.normSq A ≠ Complex.normSq B := by
  rw [Function.Bijective, conjugateReflectionResidual_injective_iff,
    conjugateReflectionResidual_surjective_iff, and_self]

/-- A complete output test: the nonsingular case, the rank-one
compatibility equation, and the zero output cover every coefficient pair. -/
theorem conjugateReflectionResidual_mem_range_iff (A B w : ℂ) :
    w ∈ Set.range (conjugateReflectionResidual A B) ↔
      Complex.normSq A ≠ Complex.normSq B ∨
        (A ≠ 0 ∧ conjugateReflectionAdjugate A B w = 0) ∨ w = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hd : Complex.normSq A = Complex.normSq B
    · by_cases hA : A = 0
      · have hB : B = 0 := by
          apply Complex.normSq_eq_zero.mp
          simpa [hA] using hd.symm
        exact Or.inr (Or.inr (by simp [conjugateReflectionResidual, hA, hB]))
      · exact Or.inr (Or.inl ⟨hA, by
          unfold conjugateReflectionAdjugate
          rw [conjugateReflectionResidual_recovery, hd]
          simp⟩)
    · exact Or.inl hd
  · rintro (hd | ⟨hA, hw⟩ | rfl)
    · exact (conjugateReflectionResidual_surjective_iff A B).mpr hd w
    · refine ⟨w / (2 * A), ?_⟩
      have hc : conj A ≠ 0 := by simpa using hA
      unfold conjugateReflectionAdjugate at hw
      unfold conjugateReflectionResidual
      simp only [map_div₀, map_mul, map_ofNat]
      field_simp [hA, hc]
      linear_combination -hw
    · exact ⟨0, by simp [conjugateReflectionResidual]⟩

end

end GaloisForLFunctions.HTGeometry
