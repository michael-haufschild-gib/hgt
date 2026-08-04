import GaloisForLFunctions.HTGeometry.MvPolynomialCoefficientDescent
import GaloisForLFunctions.HTGeometry.DifferentialRelationBaseChange

/-!
# A relation over an intermediate field must use a coefficient outside the base

If every coefficient of a differential-polynomial relation lies in the base field, the relation
descends to the base, and a hypertranscendental element admits no nonzero relation there.

So a nonzero relation of a hypertranscendental element over an intermediate field always has a
coefficient outside the base — which is where a Lüroth argument gets the element it will show
generates the intermediate field.
-/

namespace GaloisForLFunctions

noncomputable section

open MvPolynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- Evaluating a relation is unchanged by reading its base-field coefficients in the base. -/
theorem differentialPolynomialEvalOver_map_botEquiv (y : E)
    (Q : DifferentialPolynomial Unit (⊥ : IntermediateField F E)) :
    differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
        (MvPolynomial.map (IntermediateField.botEquiv F E).toAlgHom.toRingHom Q) =
      differentialPolynomialEvalOver (K := (⊥ : IntermediateField F E)) (fun _ : Unit ↦ y) Q := by
  change MvPolynomial.eval₂ (algebraMap F E)
      (fun a : Unit × ℕ ↦ differentialJet a.2 y)
        (MvPolynomial.map (IntermediateField.botEquiv F E).toAlgHom.toRingHom Q) =
    MvPolynomial.eval₂ (algebraMap (⊥ : IntermediateField F E) E)
      (fun a : Unit × ℕ ↦ differentialJet a.2 y) Q
  have hhom : ((algebraMap F E).comp
      (IntermediateField.botEquiv F E).toAlgHom.toRingHom)
      = algebraMap (⊥ : IntermediateField F E) E := by
    ext c
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.1 c.2
    have hc : c = algebraMap F (⊥ : IntermediateField F E) x := Subtype.ext hx.symm
    rw [RingHom.comp_apply]
    change (algebraMap F E) ((IntermediateField.botEquiv F E) c) = (c : E)
    rw [hc, IntermediateField.botEquiv_def]
    rfl
  rw [MvPolynomial.eval₂_map, hhom]

/-- **A nonzero relation of a hypertranscendental element uses a coefficient outside the base.** -/
theorem exists_coeff_notMem_bot_of_relation [Differential F] [DifferentialAlgebra F E] {y : E}
    (hy : HypertranscendentalOver F y) (G : IntermediateField F E)
    {P : DifferentialPolynomial Unit G} (hP : P ∈ differentialIntermediateRelationIdeal G y)
    (hPne : P ≠ 0) :
    ∃ m, ((P.coeff m : G) : E) ∉ (⊥ : IntermediateField F E) := by
  classical
  by_contra hall
  push Not at hall
  -- the relation descends to the base field
  set Q := HTGeometry.descendCoefficients (bot_le : (⊥ : IntermediateField F E) ≤ G) P hall with hQ
  set R := MvPolynomial.map (IntermediateField.botEquiv F E).toAlgHom.toRingHom Q with hR
  have hmapQ : MvPolynomial.map
      (IntermediateField.inclusion (bot_le : (⊥ : IntermediateField F E) ≤ G) :
        (⊥ : IntermediateField F E) →ₐ[F] G).toRingHom Q = P :=
    HTGeometry.map_descendCoefficients _ P hall
  have hQne : Q ≠ 0 := by
    intro h0
    exact hPne (by rw [← hmapQ, h0, map_zero])
  have hRne : R ≠ 0 := by
    intro h0
    refine hQne ?_
    refine MvPolynomial.map_injective _ ?_ (by simpa using h0)
    exact (IntermediateField.botEquiv F E).injective
  -- and it is still a relation, now with coefficients in the base
  have hQrel : differentialPolynomialEvalOver (K := (⊥ : IntermediateField F E))
      (fun _ : Unit ↦ y) Q = 0 := by
    have := differentialPolynomialEvalOver_map_inclusion
      (bot_le : (⊥ : IntermediateField F E) ≤ G) y Q
    rw [hmapQ] at this
    rw [← this]
    exact hP
  have hRrel : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) R = 0 := by
    rw [hR, differentialPolynomialEvalOver_map_botEquiv y Q]
    exact hQrel
  -- a hypertranscendental element admits no such relation
  have hind : AlgebraicIndependent F fun p : Unit × ℕ => differentialJet p.2 y := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hy
    exact hy
  rw [algebraicIndependent_iff] at hind
  exact hRne (hind R hRrel)

end

end GaloisForLFunctions
