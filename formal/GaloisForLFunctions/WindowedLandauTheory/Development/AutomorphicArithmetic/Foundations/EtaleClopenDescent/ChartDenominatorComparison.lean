import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalValueDenominators

/-! A chart containing a rational point gives a single choice of right
chart on which all sections are regular in the left local ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
  {s : Y ⟶ Spec (CommRingCat.of k)} [Algebra k Y.functionField]
  {ι κ : Type} {U : ι → Y.Opens} {V : κ → Y.Opens}
  {A : Finset ι → Subalgebra k Y.functionField} {B : Finset κ → Subalgebra k Y.functionField}

/-- The sections of some chart of the second cover have denominators
nonvanishing at the given point of the first chart. -/
theorem IsAffCover.exists_rightChart_clearDenominator
    (hA : IsAffCover s U A) (hB : IsAffCover s V B) {I : Finset ι} (hI : I.Nonempty)
    (e : A I →ₐ[k] k) : ∃ j : κ, ∀ v ∈ B {j}, ∃ (b : Y.functionField) (hb : b ∈ A I),
      e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ A I := by
  obtain ⟨y, rfl⟩ := (hA.chartPointEquiv I hI).surjective e
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hB.cover.ge (show y.1.hom default ∈ ⊤ from trivial))
  let J : Finset κ := {j}
  let hJ : J.Nonempty := Finset.singleton_nonempty j
  have hyJ : y.1.hom default ∈ J.inf V := by simpa [J] using hj
  let i := hA.sectionEquiv I hI
  let e := hA.chartPointEquiv I hI y
  refine ⟨j, fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := (hB.sectionEquiv J hJ).surjective ⟨v, hv⟩
  let z := (Y.presheaf.germ (J.inf V) (y.1.hom default) hyJ).hom a
  let c := (localPointEval y.1).hom z
  have hz : (stalkToFunctionField (y.1.hom default)).hom z = v := by
    calc
      _ = (Y.presheaf.germ (J.inf V) (genericPoint Y) (hB.ne J)).hom a :=
        ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hyJ
          (genericPoint_specializes (y.1.hom default))) a
      _ = (hB.sectionEquiv J hJ a : Y.functionField) := rfl
      _ = v := congrArg Subtype.val ha
  have h := (GlobalTheory.WH.val_iff_exists_local (hA.affine I hI) y.1 y.2 i e
    (fun _ => rfl) (hA.chartPointEquiv_eval I hI y) v c).mpr ⟨z, hz, rfl⟩
  obtain ⟨b, hb, hmul, hne, _⟩ := h
  exact ⟨b, hb, hne, hmul⟩

end GlobalTheory.PD
