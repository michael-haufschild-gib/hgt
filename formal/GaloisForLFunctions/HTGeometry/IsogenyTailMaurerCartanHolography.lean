import GaloisForLFunctions.HTGeometry.DifferentialHorizonInterface
import GaloisForLFunctions.HTGeometry.DifferentialTranscendenceDegree
import GaloisForLFunctions.HTGeometry.FixedFieldStableCoreRestriction
import GaloisForLFunctions.HTGeometry.IsogenyKernelClosure

/-!
# Isogeny-tail Maurer–Cartan holography foundations

This module proves three unconditional pieces of the general isogeny-tail theorem:

* topologically dense translation families and their closures have the same fixed field whenever
  field-element stabilizers are closed;
* the iterated isogeny-kernel union therefore has the same fixed field as its closed envelope;
* an open continuous surjective isogeny descends to an automorphism after quotienting by that
  envelope.

The differential-transcendence cardinal used by the Maurer–Cartan dimension statement is supplied
by `DifferentialTranscendenceDegree`.
-/

open scoped Classical Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Topologically dense translations have the same fixed field as their closure when every
field-element stabilizer is closed. -/
theorem differentialTranslationFixedField_eq_of_topologicalClosure_eq
    {K L A : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    [TopologicalSpace A]
    (translation : A → DifferentialAlgEquiv K L) (S T : Set A)
    (hclosure : closure S = T)
    (hclosed : ∀ z : L, IsClosed {a : A | (translation a).toAlgEquiv z = z}) :
    differentialTranslationFixedField translation S =
      differentialTranslationFixedField translation T := by
  ext z
  constructor
  · intro hz a ha
    let Z : Set A := {b | (translation b).toAlgEquiv z = z}
    have hSZ : S ⊆ Z := fun b hb => hz b hb
    have hTZ : T ⊆ Z := by
      rw [← hclosure]
      exact closure_minimal hSZ (hclosed z)
    exact hTZ ha
  · intro hz a ha
    apply hz a
    rw [← hclosure]
    exact subset_closure ha

/-- Stable-range tail equals the fixed field of a topologically closed deck envelope.  Unlike the
older interface theorem, equality of the two fixed fields is derived from density and closed
stabilizers rather than supplied as a hypothesis. -/
theorem stableRangeCore_eq_fixedField_of_topologicalDeckClosure
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [TopologicalSpace A]
    (phi : L →ₐ[K] L)
    (deck : ℕ → Subgroup (L ≃ₐ[K] L))
    (hdeck : ∀ n,
      IntermediateField.map (phi ^ n) ⊤ = IntermediateField.fixedField (deck n))
    (translation : A → DifferentialAlgEquiv K L)
    (finiteDeckPoints closedDeckPoints : Set A)
    (closedDeck : Subgroup (L ≃ₐ[K] L))
    (hfiniteDeckImage :
      (fun a => (translation a).toAlgEquiv) '' finiteDeckPoints =
        ((⨆ n, deck n) : Subgroup (L ≃ₐ[K] L)))
    (hclosedDeckImage :
      (fun a => (translation a).toAlgEquiv) '' closedDeckPoints =
        (closedDeck : Set (L ≃ₐ[K] L)))
    (hclosure : closure finiteDeckPoints = closedDeckPoints)
    (hclosedStabilizer : ∀ z : L,
      IsClosed {a : A | (translation a).toAlgEquiv z = z}) :
    stableRangeCore phi = IntermediateField.fixedField closedDeck := by
  calc
    stableRangeCore phi = IntermediateField.fixedField (⨆ n, deck n) :=
      stableRangeCore_eq_fixedField_iSup phi deck hdeck
    _ = differentialTranslationFixedField translation finiteDeckPoints :=
      (differentialTranslationFixedField_eq_fixedField_of_image_eq
        translation finiteDeckPoints (⨆ n, deck n) hfiniteDeckImage).symm
    _ = differentialTranslationFixedField translation closedDeckPoints :=
      differentialTranslationFixedField_eq_of_topologicalClosure_eq
        translation finiteDeckPoints closedDeckPoints hclosure hclosedStabilizer
    _ = IntermediateField.fixedField closedDeck :=
      differentialTranslationFixedField_eq_fixedField_of_image_eq
        translation closedDeckPoints closedDeck hclosedDeckImage

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- The iterated-kernel union and its topological closure have the same translation fixed field
when rational-function stabilizers are closed. -/
theorem differentialTranslationFixedField_iteratedKernelUnion_eq_closure
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (translation : G → DifferentialAlgEquiv K L) (alpha : G →+ G)
    (hclosed : ∀ z : L, IsClosed {a : G | (translation a).toAlgEquiv z = z}) :
    differentialTranslationFixedField translation (iteratedKernelUnion alpha : Set G) =
      differentialTranslationFixedField translation
        ((iteratedKernelUnion alpha).topologicalClosure : Set G) := by
  apply differentialTranslationFixedField_eq_of_topologicalClosure_eq
    translation (iteratedKernelUnion alpha : Set G)
      ((iteratedKernelUnion alpha).topologicalClosure : Set G)
  · exact AddSubgroup.topologicalClosure_coe.symm
  · exact hclosed

/-- An open continuous surjective isogeny descends to an additive automorphism after quotienting
by the closed envelope of all iterated kernels. -/
noncomputable def isogenyKernelClosureQuotientAddEquiv
    (alpha : G →+ G) (hsurj : Function.Surjective alpha)
    (hopen : IsOpenMap alpha) (hcont : Continuous alpha) :
    G ⧸ (iteratedKernelUnion alpha).topologicalClosure ≃+
      G ⧸ (iteratedKernelUnion alpha).topologicalClosure :=
  nonautonomousQuotientAddEquiv
    (iteratedKernelUnion alpha).topologicalClosure
    (iteratedKernelUnion alpha).topologicalClosure alpha hsurj
    (iteratedKernelUnion_topologicalClosure_comap alpha hopen hcont)

@[simp]
theorem isogenyKernelClosureQuotientAddEquiv_mk
    (alpha : G →+ G) (hsurj : Function.Surjective alpha)
    (hopen : IsOpenMap alpha) (hcont : Continuous alpha) (x : G) :
    isogenyKernelClosureQuotientAddEquiv alpha hsurj hopen hcont
        (QuotientAddGroup.mk x) = QuotientAddGroup.mk (alpha x) := by
  rfl

end

end GaloisForLFunctions.HTGeometry
