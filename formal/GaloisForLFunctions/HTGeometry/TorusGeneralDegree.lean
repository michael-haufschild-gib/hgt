import GaloisForLFunctions.HTGeometry.TorusDiagonal
import GaloisForLFunctions.HTGeometry.SmithNormalFormMatrix

/-!
# The degree of an arbitrary torus substitution

Smith normal form reduces a nonsingular integer substitution to a diagonal one: the unimodular
factors act by automorphisms of the palette and do not change the generated differential field, so
the degree of the ambient field over the substituted field is at most the absolute determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

section

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

omit [CharZero E] in
include hx in
/-- **Smith reduction of a torus substitution.**  Every nonsingular substitution generates the same
differential field as a diagonal one applied to a unimodularly changed palette. -/
theorem exists_diagonal_differentialAdjoin_eq {M : Matrix (Fin r) (Fin r) ℤ}
    (hM : M.det ≠ 0) :
    ∃ (V : Matrix (Fin r) (Fin r) ℤ) (d : Fin r → ℤ), IsUnit V.det ∧ (∀ i, d i ≠ 0) ∧
      (∏ i, (d i).natAbs) = M.det.natAbs ∧
      differentialAdjoin C (Set.range (monomialFamily M x))
        = differentialAdjoin C
            (Set.range (monomialFamily (Matrix.diagonal d) (monomialFamily V x))) := by
  classical
  obtain ⟨U, V, d, hU, hV, hd, hMUDV⟩ := exists_unimodular_diagonal M hM
  have hx0 : ∀ i, x i ≠ 0 := torus_palette_ne_zero hx
  refine ⟨V, d, hV, hd, ?_, ?_⟩
  · have hdet : M.det = U.det * (∏ i, d i) * V.det := by
      rw [hMUDV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hUabs : U.det.natAbs = 1 := Int.isUnit_iff.mp hU |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    have hVabs : V.det.natAbs = 1 := Int.isUnit_iff.mp hV |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    rw [hdet, Int.natAbs_mul, Int.natAbs_mul, hUabs, hVabs, one_mul, mul_one]
    exact (map_prod Int.natAbsHom d Finset.univ).symm
  · have hsplit : monomialFamily M x
        = monomialFamily U (monomialFamily (Matrix.diagonal d * V) x) := by
      rw [← monomialFamily_mul _ _ hx0, ← Matrix.mul_assoc, ← hMUDV]
    rw [hsplit, differentialAdjoin_monomialFamily_unimodular_eq hU _
      (fun i ↦ monomialFamily_ne_zero _ hx0 i), monomialFamily_mul _ _ hx0]

include hx hgen in
/-- **The degree of a torus substitution.**  The ambient field has degree at most the absolute
determinant over the differential field of the substituted palette. -/
theorem finrank_torus_le_natAbs_det {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Module.finrank (↥(differentialAdjoin C (Set.range (monomialFamily M x)))) E
      ≤ M.det.natAbs := by
  classical
  obtain ⟨V, d, hV, hd, hprod, heq⟩ := exists_diagonal_differentialAdjoin_eq hx hM
  have hVne : V.det ≠ 0 := det_ne_zero_of_isUnit_det hV
  have hyindep : DifferentialIndependent C (monomialFamily V x) :=
    differentialIndependent_monomialFamily hx hVne
  have hygen : differentialAdjoin C (Set.range (monomialFamily V x)) = ⊤ :=
    differentialAdjoin_monomialFamily_eq_top_of_isUnit_det hx hgen hV
  have hbound := finrank_diagonal_le_prod hyindep hygen hd
  rw [heq, ← hprod]
  exact hbound

end

end

end GaloisForLFunctions.HTGeometry
