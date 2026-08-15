import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.ElementaryOstrowski
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid

/-!
# Differential independence is insensitive to differentially algebraic perturbations

Shifting each member of a family by an element of the coefficient field is an automorphism of the
polynomial algebra on the jet variables, so it preserves algebraic — hence differential —
independence.  Adjoining differentially algebraic elements to the coefficient field changes no
independence statement, so a family may be perturbed by differentially algebraic amounts without
changing its differential matroid.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The polynomial automorphism shifting each variable by a constant. -/
noncomputable def shiftVarsAlgEquiv {F σ : Type*} [CommRing F] (β : σ → F) :
    MvPolynomial σ F ≃ₐ[F] MvPolynomial σ F :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun s => MvPolynomial.X s + MvPolynomial.C (β s))
    (MvPolynomial.aeval fun s => MvPolynomial.X s - MvPolynomial.C (β s))
    (by
      apply MvPolynomial.algHom_ext
      intro s
      simp)
    (by
      apply MvPolynomial.algHom_ext
      intro s
      simp)

/-- **Algebraic independence is preserved by a base-field shift.** -/
theorem algebraicIndependent_add_algebraMap {F E σ : Type*} [CommRing F] [CommRing E]
    [Algebra F E] {v : σ → E} (hv : AlgebraicIndependent F v) (β : σ → F) :
    AlgebraicIndependent F (fun s => v s + algebraMap F E (β s)) := by
  have hcomp : (MvPolynomial.aeval (fun s => v s + algebraMap F E (β s)) :
        MvPolynomial σ F →ₐ[F] E)
      = ((MvPolynomial.aeval v : MvPolynomial σ F →ₐ[F] E)).comp
        (shiftVarsAlgEquiv β).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [shiftVarsAlgEquiv]
  have hinj : Function.Injective
      (⇑(MvPolynomial.aeval (fun s => v s + algebraMap F E (β s)) :
        MvPolynomial σ F →ₐ[F] E)) := by
    rw [hcomp, AlgHom.coe_comp]
    exact Function.Injective.comp hv (shiftVarsAlgEquiv β).injective
  exact hinj

/-- **Differential independence is preserved by a base-field shift.** -/
theorem differentialIndependent_add_algebraMap {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    {x : ι → E} (hx : DifferentialIndependent F x) (b : ι → F) :
    DifferentialIndependent F (fun i => x i + algebraMap F E (b i)) := by
  have hshift := algebraicIndependent_add_algebraMap hx
    (fun p : ι × ℕ => differentialJet p.2 (b p.1))
  have hfun : (fun p : ι × ℕ =>
        differentialJet p.2 ((fun i => x i + algebraMap F E (b i)) p.1))
      = fun p : ι × ℕ =>
        differentialJet p.2 (x p.1) + algebraMap F E (differentialJet p.2 (b p.1)) := by
    funext p
    rw [differentialJet_additive, differentialJet_algebraMap]
  show AlgebraicIndependent F _
  rw [hfun]
  exact hshift

set_option synthInstance.maxHeartbeats 400000 in
/-- **Differentially algebraic perturbations preserve differential independence.** -/
theorem differentialIndependent_of_sub_differentialAlgebraic {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : ι → E} (hd : ∀ i, DifferentialAlgebraicOver F (y i - x i))
    (hx : DifferentialIndependent F x) : DifferentialIndependent F y := by
  classical
  set G : Set E := Set.range (fun i => y i - x i) with hG
  have hGDA : ∀ g ∈ G, DifferentialAlgebraicOver F g := by
    rintro g ⟨i, rfl⟩
    exact hd i
  haveI : DifferentialAlgebra ↥(differentialAdjoin F G) E :=
    ⟨fun z => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F G) z⟩
  have hx' : DifferentialIndependent ↥(differentialAdjoin F G) x :=
    (differentialIndependent_differentialAdjoin_iff hGDA).mpr hx
  have hb : ∀ i, y i - x i ∈ differentialAdjoin F G :=
    fun i => subset_differentialAdjoin F G ⟨i, rfl⟩
  have hshift := differentialIndependent_add_algebraMap hx'
    (fun i => (⟨y i - x i, hb i⟩ : ↥(differentialAdjoin F G)))
  have hfun : (fun i => x i + algebraMap ↥(differentialAdjoin F G) E
      (⟨y i - x i, hb i⟩ : ↥(differentialAdjoin F G))) = y := by
    funext i
    show x i + (y i - x i) = y i
    ring
  rw [hfun] at hshift
  exact (differentialIndependent_differentialAdjoin_iff hGDA).mp hshift

/-- The differential matroids of two families differing by differentially algebraic amounts
agree. -/
theorem differentialIndependent_congr_of_sub_differentialAlgebraic {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : ι → E} (hd : ∀ i, DifferentialAlgebraicOver F (y i - x i)) :
    DifferentialIndependent F x ↔ DifferentialIndependent F y := by
  constructor
  · exact differentialIndependent_of_sub_differentialAlgebraic hd
  · refine differentialIndependent_of_sub_differentialAlgebraic fun i => ?_
    have hneg := differentialAlgebraicOver_neg (hd i)
    have hid : -(y i - x i) = x i - y i := by ring
    rwa [hid] at hneg

set_option synthInstance.maxHeartbeats 400000 in
/-- **The differential family matroid is insensitive to differentially algebraic
perturbations.** -/
theorem differentialFamilyMatroid_congr_of_sub_differentialAlgebraic {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : ι → E} (hd : ∀ i, DifferentialAlgebraicOver F (y i - x i)) :
    GaloisForLFunctions.differentialFamilyMatroid (F := F) x
      = GaloisForLFunctions.differentialFamilyMatroid (F := F) y := by
  refine Matroid.ext_indep ?_ fun I _ => ?_
  · simp [GaloisForLFunctions.differentialFamilyMatroid]
  · rw [differentialFamilyMatroid_indep_iff, differentialFamilyMatroid_indep_iff]
    exact differentialIndependent_congr_of_sub_differentialAlgebraic
      (fun i : I => hd (i : ι))

end

end GaloisForLFunctions.HTGeometry
