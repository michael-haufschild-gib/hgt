/-
# Chen--Gupta--Li Proposition 5.1 character bounds

Closes the elementary finite character estimate used in the axial `S₁`
analysis: Dirichlet characters are bounded by one at every residue, and the
one surviving additive twisted character sum is bounded by the modulus.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialReduction

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Every complex Dirichlet character value has norm at most one, including
the zero value at nonunits. -/
theorem norm_cglDirichletCharacter_apply_le_one
    (Q : CGLPositiveModulus) (chi : DirichletCharacter ℂ Q.value) (a : ZMod Q.value) :
    ‖chi a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.unit_norm_eq_one]
  · rw [MulChar.map_nonunit chi ha, norm_zero]
    exact zero_le_one

/-- The remaining additive twisted character sum on an axial `S₁` frequency
is bounded by the complete residue count. -/
theorem norm_cglProposition51AxialTwistedCharacterFactor_le
    (Q : CGLPositiveModulus) (chi psi : DirichletCharacter ℂ Q.value) (m : ℤ) :
    ‖cglProposition51AxialTwistedCharacterFactor Q chi psi m‖ ≤ Q.value := by
  unfold cglProposition51AxialTwistedCharacterFactor
  calc
    ‖∑ a : ZMod Q.value,
        chi a * (starRingEnd ℂ) (psi a) * ZMod.stdAddChar (a * (m : ZMod Q.value))‖ ≤
      ∑ a : ZMod Q.value,
        ‖chi a * (starRingEnd ℂ) (psi a) * ZMod.stdAddChar (a * (m : ZMod Q.value))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : ZMod Q.value, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul, norm_mul, Complex.norm_conj, AddChar.norm_apply]
      have hchi := norm_cglDirichletCharacter_apply_le_one Q chi a
      have hpsi := norm_cglDirichletCharacter_apply_le_one Q psi a
      simpa using mul_le_one₀ hchi (norm_nonneg _) hpsi
    _ = Q.value := by simp

end RHTower
