import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsPushforward
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RelativeFormsTrace

/-! The trace on Hodge cohomology along a finite étale morphism. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

noncomputable section

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

private abbrev PushforwardFormsCohomology (t : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X) (p q : ℕ) :=
  CohomologyOn ((Scheme.Modules.pushforward f).obj (relativeForms t p)) ⊤ q

private abbrev pushforwardFormsModule (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X) (p q : ℕ) :
    Module k (PushforwardFormsCohomology t f p q) :=
  letI : Algebra k Γ(X, ⊤) := sectionAlgebra s ⊤
  Module.compHom _ (algebraMap k Γ(X, ⊤))

private def formsPushforwardEquiv (hf : f ≫ s = t) (p q : ℕ) :
    letI := pushforwardFormsModule s t f p q
    PushforwardFormsCohomology t f p q ≃ₗ[k] HodgeCohomology t p q := by
  letI := pushforwardFormsModule s t f p q
  letI : Algebra k Γ(X, ⊤) := sectionAlgebra s ⊤
  letI : Algebra k Γ(Y, ⊤) := sectionAlgebra t ⊤
  let C := CohomologyOn.pushforwardComparison f (relativeForms t p) ⊤ q
  let L : PushforwardFormsCohomology t f p q →ₗ[k] HodgeCohomology t p q :=
    { C.toAddMonoidHom with
      map_smul' r x := by
        change C (algebraMap k Γ(X, ⊤) r • x) = algebraMap k Γ(Y, ⊤) r • C x
        exact (C.map_smulₛₗ (algebraMap k Γ(X, ⊤) r) x).trans
          (congrArg (fun a : Γ(Y, ⊤) => a • C x) ((sectionPullback hf ⊤).commutes r)) }
  exact LinearEquiv.ofBijective L (relativeForms_pushforwardComparison_bijective f t p q ⊤)

/-- Trace on Hodge cohomology is the trace on the direct image of relative forms. -/
def hodgeTrace (hf : f ≫ s = t) (p q : ℕ) : HodgeCohomology t p q →ₗ[k] HodgeCohomology s p q := by
  letI := pushforwardFormsModule s t f p q
  letI : Algebra k Γ(X, ⊤) := sectionAlgebra s ⊤
  let T := CohomologyOn.map (relativeFormsTrace hf p) ⊤ q
  let L : PushforwardFormsCohomology t f p q →ₗ[k] HodgeCohomology s p q :=
    { T.toAddMonoidHom with
      map_smul' r x := T.map_smul (algebraMap k Γ(X, ⊤) r) x }
  exact L.comp (formsPushforwardEquiv hf p q).symm.toLinearMap

local instance traceSheafHasExt (X : TopCat.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

private theorem map_comp_apply {F G H : X.Modules} (a : F ⟶ G) (b : G ⟶ H) (q : ℕ)
    (x : CohomologyOn F ⊤ q) :
    CohomologyOn.map b ⊤ q (CohomologyOn.map a ⊤ q x) = CohomologyOn.map (a ≫ b) ⊤ q x := by
  let P := SheafOfModules.toSheaf X.ringCatSheaf
  change ((x : Ext _ _ q).comp (Ext.mk₀ (P.map a)) (add_zero q)).comp
      (Ext.mk₀ (P.map b)) (add_zero q) =
    (x : Ext _ _ q).comp (Ext.mk₀ (P.map (a ≫ b))) (add_zero q)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp]

/-- Trace after pullback is induced by the composite of the two morphisms on relative forms. -/
theorem hodgeTrace_hodgePullback (hf : f ≫ s = t) (p q : ℕ) (x : HodgeCohomology s p q) :
    hodgeTrace hf p q (hodgePullback hf p q x) =
      CohomologyOn.map (relativeFormsPullback hf p ≫ relativeFormsTrace hf p) ⊤ q x := by
  letI := pushforwardFormsModule s t f p q
  let E := formsPushforwardEquiv hf p q
  let y := CohomologyOn.map (relativeFormsPullback hf p) ⊤ q x
  change CohomologyOn.map (relativeFormsTrace hf p) ⊤ q (E.symm (E y)) =
    CohomologyOn.map (relativeFormsPullback hf p ≫ relativeFormsTrace hf p) ⊤ q x
  rw [E.symm_apply_apply]
  exact map_comp_apply (relativeFormsPullback hf p) (relativeFormsTrace hf p) q x

private theorem map_nsmul_id (F : X.Modules) (q d : ℕ) (x : CohomologyOn F ⊤ q) :
    CohomologyOn.map (d • 𝟙 F) ⊤ q x = d • x := by
  let P := SheafOfModules.toSheaf X.ringCatSheaf
  change (x : Ext _ _ q).comp (Ext.mk₀ (P.map (d • 𝟙 F))) (add_zero q) = d • (x : Ext _ _ q)
  have hP : P.map (d • 𝟙 F) = d • 𝟙 (P.obj F) :=
    P.map_nsmul.trans (congrArg (d • ·) (P.map_id F))
  let A := P.obj F
  let mk : (A ⟶ A) →+ Ext A A 0 :=
    (Ext.addEquiv₀ (X := A) (Y := A)).symm.toAddMonoidHom
  have hd : Ext.mk₀ (d • 𝟙 A) = d • Ext.mk₀ (𝟙 A) :=
    mk.map_nsmul d (𝟙 A)
  have h : Ext.mk₀ (P.map (d • 𝟙 F)) = d • Ext.mk₀ (𝟙 (P.obj F)) :=
    (congrArg (fun y : A ⟶ A => Ext.mk₀ y) hP).trans hd
  have e := ((x : Ext _ _ q).precomp (P.obj F) (add_zero q)).map_nsmul
    d (Ext.mk₀ (𝟙 (P.obj F)))
  exact (congrArg (fun y => (x : Ext _ _ q).comp y (add_zero q)) h).trans
    (e.trans (congrArg (d • ·) ((x : Ext _ _ q).comp_mk₀_id)))

/-- When the trace of the unit is constant, trace after pullback is multiplication by it. -/
theorem hodgeTrace_hodgePullback_of_trace_one (hf : f ≫ s = t) (p q d : ℕ)
    (hd : ∀ (U : X.Opens) (hU : IsAffineOpen U), affineSectionTrace (f := f) s t hU 1 = d)
    (x : HodgeCohomology s p q) : hodgeTrace hf p q (hodgePullback hf p q x) = d • x := by
  rw [hodgeTrace_hodgePullback, relativeFormsTrace_comp_pullback hf p d hd]
  exact map_nsmul_id (relativeForms s p) q d x

end GlobalTheory.SchemeCohomology
