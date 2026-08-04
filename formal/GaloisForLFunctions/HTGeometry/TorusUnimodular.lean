import GaloisForLFunctions.HTGeometry.TorusScaleAction

/-!
# Unimodular monomial substitutions are automorphisms

A monomial substitution whose matrix is invertible over the integers has an integral inverse
substitution, so it is an automorphism of the freely generated differential field and its monomial
family generates the whole field again.

This is the coordinate change that reduces an arbitrary integer matrix to its Smith normal form
without changing the generated field: only the elementary divisors matter.
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

/-- An integrally invertible matrix has nonzero determinant. -/
theorem det_ne_zero_of_isUnit_det {M : Matrix (Fin r) (Fin r) ℤ} (hu : IsUnit M.det) :
    M.det ≠ 0 := by
  intro h
  rw [h] at hu
  exact (not_isUnit_zero (M₀ := ℤ)) hu

include hx hgen in
/-- **A unimodular monomial substitution is an automorphism.** -/
theorem torusEndo_bijective_of_isUnit_det {M : Matrix (Fin r) (Fin r) ℤ} (hu : IsUnit M.det) :
    Function.Bijective (torusEndo hx hgen (det_ne_zero_of_isUnit_det hu)) := by
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hu
  have hMN : M * (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) = 1 := by
    rw [← hv]
    exact v.mul_inv
  have hNM : (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) * M = 1 := by
    rw [← hv]
    exact v.inv_mul
  have hNdet : ((↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)).det ≠ 0 := by
    intro h
    have hone : (1 : Matrix (Fin r) (Fin r) ℤ).det = 0 := by
      rw [← hNM, Matrix.det_mul, h, zero_mul]
    rw [Matrix.det_one] at hone
    exact one_ne_zero hone
  have hone : (1 : Matrix (Fin r) (Fin r) ℤ).det ≠ 0 := by
    rw [Matrix.det_one]
    exact one_ne_zero
  have hcomp₁ : (torusEndo hx hgen (det_ne_zero_of_isUnit_det hu)).comp
      (torusEndo hx hgen hNdet) = AlgHom.id C E := by
    rw [torusEndo_comp]
    rw [torusEndo_congr hx hgen _ hone hNM]
    exact torusEndo_one hx hgen hone
  have hcomp₂ : (torusEndo hx hgen hNdet).comp
      (torusEndo hx hgen (det_ne_zero_of_isUnit_det hu)) = AlgHom.id C E := by
    rw [torusEndo_comp]
    rw [torusEndo_congr hx hgen _ hone hMN]
    exact torusEndo_one hx hgen hone
  constructor
  · intro a b hab
    have h := congrArg (torusEndo hx hgen hNdet) hab
    have ha := AlgHom.congr_fun hcomp₂ a
    have hb := AlgHom.congr_fun hcomp₂ b
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at ha hb
    rw [ha, hb] at h
    exact h
  · intro z
    refine ⟨torusEndo hx hgen hNdet z, ?_⟩
    have h := AlgHom.congr_fun hcomp₁ z
    simpa using h

include hx hgen in
/-- **A unimodular monomial substitution keeps the whole field.**  Its monomial family generates the
same differential field as the original palette. -/
theorem differentialAdjoin_monomialFamily_eq_top_of_isUnit_det
    {M : Matrix (Fin r) (Fin r) ℤ} (hu : IsUnit M.det) :
    differentialAdjoin C (Set.range (monomialFamily M x)) = ⊤ := by
  have hsurj := (torusEndo_bijective_of_isUnit_det hx hgen hu).2
  rw [← torusEndo_map_top hx hgen (det_ne_zero_of_isUnit_det hu)]
  apply top_unique
  intro z _
  rw [IntermediateField.mem_map]
  obtain ⟨w, hw⟩ := hsurj z
  exact ⟨w, trivial, hw⟩


omit [CharZero E] in
/-- **A substitution can only shrink the generated differential field.** -/
theorem differentialAdjoin_monomialFamily_le (A : Matrix (Fin r) (Fin r) ℤ) (z : Fin r → E) :
    differentialAdjoin C (Set.range (monomialFamily A z))
      ≤ differentialAdjoin C (Set.range z) := by
  refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
  rintro _ ⟨i, rfl⟩
  rw [monomialFamily_apply]
  exact prod_mem fun j _ ↦ zpow_mem
    (subset_differentialAdjoin C _ (Set.mem_range_self j)) _

omit [CharZero E] in
/-- **Factoring a substitution shrinks its differential field.**  If the rows of `Q` are integer
combinations of the rows of `P`, the field of `Q` is contained in the field of `P`. -/
theorem differentialAdjoin_monomialFamily_le_of_factor {P Q : Matrix (Fin r) (Fin r) ℤ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hQ : Q = A * P) (z : Fin r → E) (hz0 : ∀ i, z i ≠ 0) :
    differentialAdjoin C (Set.range (monomialFamily Q z))
      ≤ differentialAdjoin C (Set.range (monomialFamily P z)) := by
  rw [hQ, monomialFamily_mul _ _ hz0]
  exact differentialAdjoin_monomialFamily_le A (monomialFamily P z)

omit [CharZero E] in
/-- **A unimodular substitution does not change the generated differential field.**  This holds for
an arbitrary nonzero family, not only for a generating palette: the inverse substitution is again
integral. -/
theorem differentialAdjoin_monomialFamily_unimodular_eq {M : Matrix (Fin r) (Fin r) ℤ}
    (hu : IsUnit M.det) (z : Fin r → E) (hz0 : ∀ i, z i ≠ 0) :
    differentialAdjoin C (Set.range (monomialFamily M z))
      = differentialAdjoin C (Set.range z) := by
  classical
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hu
  have hNM : (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) * M = 1 := by
    rw [← hv]
    exact v.inv_mul
  have hmono : ∀ (A : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → E), (∀ i, w i ≠ 0) →
      differentialAdjoin C (Set.range (monomialFamily A w))
        ≤ differentialAdjoin C (Set.range w) := fun A w _ ↦
    differentialAdjoin_monomialFamily_le A w
  refine le_antisymm (hmono M z hz0) ?_
  have hback : monomialFamily (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)
      (monomialFamily M z) = z := by
    rw [← monomialFamily_mul _ _ hz0, hNM, monomialFamily_one]
  have := hmono (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) (monomialFamily M z)
    (fun i ↦ monomialFamily_ne_zero M hz0 i)
  rwa [hback] at this

end

end

end GaloisForLFunctions.HTGeometry
