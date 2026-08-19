import Mathlib

/-!
# Connes--van Suijlekom, Appendix B: the three-dimensional cone

This module formalizes the finite real-matrix calculation in Lemma B.2 of
Connes--van Suijlekom, arXiv:2511.23257v1.  The source cone consists of

`μ(a,b,c) = [[a,c,c],[c,b,c],[c,c,a]]`.

The displayed coordinates of the compression to
`E = span ((0,1,0), (1/sqrt 2,0,1/sqrt 2))` are the source's concrete
two-dimensional model.  Subsequent declarations prove the cone equivalence
and then its extreme-ray statement.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real symmetric matrix `μ(a,b,c)` in Appendix B. -/
def connesVanSuijlekomB2Mu (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, c, c;
     c, b, c;
     c, c, a]

/-- Matrix of the Appendix-B compression in its displayed orthonormal basis of `E`. -/
def connesVanSuijlekomB2Rho (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b, Real.sqrt 2 * c;
     Real.sqrt 2 * c, a + c]

/-- The inclusion of the Appendix-B plane `E` in the source three-space. -/
def connesVanSuijlekomB2Embed : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, (Real.sqrt 2)⁻¹;
     1, 0;
     0, (Real.sqrt 2)⁻¹]

private theorem connesVanSuijlekomB2_sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

private theorem connesVanSuijlekomB2_sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

/-- The source compression has exactly the coordinates printed in Lemma B.2. -/
theorem connesVanSuijlekomB2_compression_eq_rho (a b c : ℝ) :
    connesVanSuijlekomB2Embed.conjTranspose * connesVanSuijlekomB2Mu a b c *
        connesVanSuijlekomB2Embed =
      connesVanSuijlekomB2Rho a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Embed, connesVanSuijlekomB2Mu,
      connesVanSuijlekomB2Rho, Matrix.mul_apply,
      Fin.sum_univ_three]
  all_goals
    field_simp [connesVanSuijlekomB2_sqrt_two_ne_zero]
    rw [connesVanSuijlekomB2_sqrt_two_sq]
    ring

/-- The exact orthogonal splitting behind Appendix B's cone calculation. -/
theorem connesVanSuijlekomB2_quadratic_decomposition (a b c : ℝ) (x : Fin 3 → ℝ) :
    star x ⬝ᵥ (connesVanSuijlekomB2Mu a b c).mulVec x =
      (a - c) * ((x 0 - x 2) / Real.sqrt 2) ^ 2 +
        star (![x 1, (x 0 + x 2) / Real.sqrt 2] : Fin 2 → ℝ) ⬝ᵥ
          (connesVanSuijlekomB2Rho a b c).mulVec
            (![x 1, (x 0 + x 2) / Real.sqrt 2] : Fin 2 → ℝ) := by
  simp [connesVanSuijlekomB2Mu, connesVanSuijlekomB2Rho, Matrix.dotProduct,
    Matrix.mulVec, Fin.sum_univ_three]
  field_simp [connesVanSuijlekomB2_sqrt_two_ne_zero]
  rw [connesVanSuijlekomB2_sqrt_two_sq]
  ring

/-- **Connes--van Suijlekom, Lemma B.2(i--ii), coordinate cone form.**

The Appendix-B compression identifies the positive cone of the source matrices
with the positive semidefinite `2 × 2` cone subject to the source half-space
`z ≥ sqrt(2) y`.  In the displayed coordinates that half-space is `c ≤ a`.
-/
theorem connesVanSuijlekomB2_cone_iff (a b c : ℝ) :
    (connesVanSuijlekomB2Mu a b c).PosSemidef ↔
      (connesVanSuijlekomB2Rho a b c).PosSemidef ∧ c ≤ a := by
  constructor
  · intro hMu
    refine ⟨?_, ?_⟩
    · have hCompression := hMu.conjTranspose_mul_mul_same connesVanSuijlekomB2Embed
      rw [connesVanSuijlekomB2_compression_eq_rho] at hCompression
      exact hCompression
    · let odd : Fin 3 → ℝ := ![1, 0, -1]
      have hOdd := hMu.dotProduct_mulVec_nonneg odd
      change 0 ≤ star odd ⬝ᵥ (connesVanSuijlekomB2Mu a b c).mulVec odd at hOdd
      simp [odd, connesVanSuijlekomB2Mu, Matrix.dotProduct, Matrix.mulVec,
        Fin.sum_univ_three] at hOdd
      linarith
  · rintro ⟨hRho, hca⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · show (connesVanSuijlekomB2Mu a b c)ᴴ = connesVanSuijlekomB2Mu a b c
      ext i j
      fin_cases i <;> fin_cases j <;> simp [connesVanSuijlekomB2Mu]
    · intro x
      rw [connesVanSuijlekomB2_quadratic_decomposition]
      refine add_nonneg ?_ ?_
      · exact mul_nonneg (sub_nonneg.mpr hca) (sq_nonneg _)
      · exact hRho.dotProduct_mulVec_nonneg _

end

end GaloisForLFunctions.HTGeometry
