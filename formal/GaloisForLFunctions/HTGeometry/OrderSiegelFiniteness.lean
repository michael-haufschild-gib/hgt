import GaloisForLFunctions.HTGeometry.OrderSymmetricSpace

/-!
# The finiteness half over an order is inherited

The symmetric space of `SL_n(R)` sits inside the cone of positive definite `nd × nd` real forms, and
the group acts through integral unimodular matrices.  So a set of forms that is Siegel-reduced for the
**ambient** integral group already has a finite overlap set for the smaller group: the conjugating
matrices are integral unimodular and carry one ambient Siegel-reduced form to another, and there are
only finitely many of those.

This is what makes the reduction theory of an order need only its covering half.

* `orderToCone` : the inclusion of the symmetric space into the ambient cone.
* `orderMeet_finite` : **the overlap set is finite.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

theorem orderRepR_injective (ω : Module.Basis (Fin d) ℤ R) :
    Function.Injective (orderRepR (nb := nb) ω) := by
  intro M N hMN
  refine orderRep_injective ω ?_
  ext p q
  have h : ((orderRep ω M p q : ℤ) : ℝ) = ((orderRep ω N p q : ℤ) : ℝ) :=
    congrFun (congrFun hMN p) q
  exact_mod_cast h

theorem orderInvRep_injective (ω : Module.Basis (Fin d) ℤ R) :
    Function.Injective (orderInvRep (nb := nb) ω) := by
  intro M N hMN
  have h := orderRepR_injective ω hMN
  have hinv : (M⁻¹ : Matrix.SpecialLinearGroup (Fin nb) R)
      = (N⁻¹ : Matrix.SpecialLinearGroup (Fin nb) R) := Subtype.ext h
  exact inv_injective hinv

theorem isIntUnimodular_orderInvRep (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) : IsIntUnimodular (orderInvRep ω M) := by
  refine isIntUnimodular_orderRep ω ?_
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  rw [Matrix.SpecialLinearGroup.det_coe]
  exact isUnit_one

/-- The symmetric space of `SL_n(R)`, inside the ambient cone. -/
def orderToCone (ω : Module.Basis (Fin d) ℤ R) (A : ↥(orderCone (nb := nb) ω)) :
    posDefCone (nb * d) :=
  ⟨orderToSymm ω (A : ↥(orderForms (nb := nb) ω)), A.2⟩

theorem coneMat_orderToCone (ω : Module.Basis (Fin d) ℤ R) (A : ↥(orderCone (nb := nb) ω)) :
    coneMat (orderToCone ω A)
      = ((A : ↥(orderForms (nb := nb) ω)) : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) := rfl

theorem coneMat_orderToCone_smul (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) (A : ↥(orderCone (nb := nb) ω)) :
    coneMat (orderToCone ω (orderSmul ω M A))
      = (orderInvRep ω M)ᵀ * coneMat (orderToCone ω A) * orderInvRep ω M := rfl

/-- **The overlap set of an ambient Siegel-reduced set is finite for the order group.** -/
theorem orderMeet_finite (ω : Module.Basis (Fin d) ℤ R) {t u : ℝ} (ht : 1 ≤ t)
    {V : Set ↥(orderCone (nb := nb) ω)}
    (hV : ∀ A ∈ V, (jacOf (orderToCone ω A)).IsSiegel t u) :
    {M : Matrix.SpecialLinearGroup (Fin nb) R | ∃ A ∈ V, orderSmul ω M A ∈ V}.Finite := by
  classical
  have hSfin := siegel_finiteness (nb * d) t u ht
  refine Set.Finite.subset (Set.Finite.preimage
    (fun a _ b _ h => orderInvRep_injective ω h) hSfin) ?_
  rintro M ⟨A, hA, hMA⟩
  refine ⟨isIntUnimodular_orderInvRep ω M, jacOf (orderToCone ω A),
    jacOf (orderToCone ω (orderSmul ω M A)), hV A hA, hV _ hMA, ?_⟩
  rw [jacOf_form, jacOf_form, coneMat_orderToCone_smul]

end GaloisForLFunctions.HTGeometry
