import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality

/-!
# Substitution in a free scalar differential field

A hypertranscendental scalar freely generates a rational field in all of its jets.  This module
packages the canonical substitution homomorphism sending that generator to any other
hypertranscendental scalar in the same ambient field, and proves that the substitution commutes
with the derivation.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The canonical differential substitution from a free scalar field, sending its generator to
another hypertranscendental scalar in the same ambient field. -/
def scalarDifferentialSubstitutionAlgHom
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (y v : E) (hy : HypertranscendentalOver C y)
    (hv : HypertranscendentalOver C v)
    (hytop : differentialAdjoin C {y} = ⊤) : E →ₐ[C] E := by
  let x : Unit → E := fun _ ↦ y
  let z : Unit → E := fun _ ↦ v
  have hx : DifferentialIndependent C x :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C y).mp hy
  have hz : DifferentialIndependent C z :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C v).mp hv
  have hxtop : differentialAdjoin C (Set.range x) = ⊤ := by
    simpa [x] using hytop
  let ex : differentialAdjoin C (Set.range x) ≃ₐ[C] E :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  let ez : differentialAdjoin C (Set.range z) →ₐ[C] E :=
    IntermediateField.topEquiv.toAlgHom.comp
      (IntermediateField.inclusion le_top)
  exact ez.comp
    ((differentialIndependentAdjoinAlgEquiv x z hx hz).toAlgHom.comp ex.symm.toAlgHom)

@[simp]
theorem scalarDifferentialSubstitutionAlgHom_generator
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (y v : E) (hy : HypertranscendentalOver C y)
    (hv : HypertranscendentalOver C v)
    (hytop : differentialAdjoin C {y} = ⊤) :
    scalarDifferentialSubstitutionAlgHom y v hy hv hytop y = v := by
  let x : Unit → E := fun _ ↦ y
  let z : Unit → E := fun _ ↦ v
  have hx : DifferentialIndependent C x :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C y).mp hy
  have hz : DifferentialIndependent C z :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C v).mp hv
  have hxtop : differentialAdjoin C (Set.range x) = ⊤ := by
    simpa [x] using hytop
  let ex : differentialAdjoin C (Set.range x) ≃ₐ[C] E :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  have hxpre : ex.symm y =
      ⟨y, subset_differentialAdjoin C (Set.range x) (Set.mem_range_self ())⟩ := by
    apply ex.injective
    rfl
  have hxy := congrArg Subtype.val
    (differentialIndependentAdjoinAlgEquiv_jet x z hx hz () 0)
  change ((differentialIndependentAdjoinAlgEquiv x z hx hz) (ex.symm y)).1 = v
  rw [hxpre]
  exact hxy

/-- Scalar differential substitution commutes with the derivation. -/
theorem scalarDifferentialSubstitutionAlgHom_deriv
    {C E : Type*} [Field C] [Field E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (y v : E) (hy : HypertranscendentalOver C y)
    (hv : HypertranscendentalOver C v)
    (hytop : differentialAdjoin C {y} = ⊤) (w : E) :
    scalarDifferentialSubstitutionAlgHom y v hy hv hytop w′ =
      (scalarDifferentialSubstitutionAlgHom y v hy hv hytop w)′ := by
  let x : Unit → E := fun _ ↦ y
  let z : Unit → E := fun _ ↦ v
  have hx : DifferentialIndependent C x :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C y).mp hy
  have hz : DifferentialIndependent C z :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C v).mp hv
  have hxtop : differentialAdjoin C (Set.range x) = ⊤ := by
    simpa [x] using hytop
  let ex : differentialAdjoin C (Set.range x) ≃ₐ[C] E :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  let wx : differentialAdjoin C (Set.range x) := ex.symm w
  have hwx : ex.symm w′ = wx′ := by
    apply Subtype.ext
    rfl
  have hxy := differentialIndependentAdjoinAlgEquiv_deriv x z hx hz wx
  change ((differentialIndependentAdjoinAlgEquiv x z hx hz) (ex.symm w′)).1 =
    (((differentialIndependentAdjoinAlgEquiv x z hx hz) (ex.symm w)).1)′
  rw [hwx]
  exact congrArg Subtype.val hxy

end

end GaloisForLFunctions
