import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StalkRationalValues
import GaloisForLFunctions.HTGeometry.SchemeStalkPoints
import Mathlib.RingTheory.RingHom.Unramified

/-! Germs and pullbacks of local rings at rational points as maps over the
base field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

abbrev stalkBaseAlgebra (s : X ⟶ Spec (CommRingCat.of k)) (p : X) :
    Algebra k (X.presheaf.stalk p) :=
  (stalkConstants (Over.mk s) p).hom.toAlgebra

/-- The germ of a section, with the structure algebra on the stalk. -/
def sectionGermAlg (s : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}
    {p : X} (hp : p ∈ U) :
    letI := stalkBaseAlgebra s p
    SectionRing s U →ₐ[k] X.presheaf.stalk p := by
  letI := stalkBaseAlgebra s p
  refine { toRingHom := (X.presheaf.germ U p hp).hom, commutes' := fun a => ?_ }
  have h : s.appLE ⊤ U le_top ≫ X.presheaf.germ U p hp =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ (s p) trivial ≫ s.stalkMap p := by
    rw [s.germ_stalkMap]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res']
  exact ConcreteCategory.congr_hom (congrArg ((Scheme.ΓSpecIso _).inv ≫ ·) h) a

theorem sectionGerm_formallyEtale {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) :
    (X.presheaf.germ U p hp).hom.FormallyEtale := by
  let point : U := ⟨p, hp⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) := X.presheaf.algebra_section_stalk point
  let S := (hU.primeIdealOf point).asIdeal.primeCompl
  letI : IsLocalization S (X.presheaf.stalk p) := hU.isLocalization_stalk point
  exact RingHom.formallyEtale_algebraMap.mpr (Algebra.FormallyEtale.of_isLocalization S)

/-- Evaluation of the local ring at a base-field point. -/
def localPointEvalAlg (y : Y.BaseFieldPointOver k t) :
    letI := stalkBaseAlgebra t (y.hom default)
    Y.presheaf.stalk (y.hom default) →ₐ[k] k := by
  letI := stalkBaseAlgebra t (y.hom default)
  refine { toRingHom := (localPointEval y).hom, commutes' := fun a => ?_ }
  have h : stalkConstants (Over.mk t) (y.hom default) ≫ localPointEval y = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpecStalk_comp_hom]
    change Spec.map (localPointEval y) ≫ Y.fromSpecStalk (y.hom default) ≫ t = _
    rw [← Category.assoc, specMap_localPointEval_fromSpecStalk, Spec.map_id]
    exact y.commutes
  change (stalkConstants (Over.mk t) (y.hom default) ≫ localPointEval y).hom a = a
  rw [h]
  rfl

theorem localPointEvalAlg_germ (y : Y.BaseFieldPointOver k t) {U : Y.Opens}
    (hy : y.hom default ∈ U) (a : SectionRing t U) :
    localPointEvalAlg y (sectionGermAlg t hy a) = affinePointEval y hy a :=
  localPointEval_germ y hy a

variable {c : Y ⟶ X}

/-- The stalk map of a morphism over the base field. -/
def stalkPullbackAlg (hc : c ≫ s = t) (p : Y) :
    letI := stalkBaseAlgebra s (c p)
    letI := stalkBaseAlgebra t p
    X.presheaf.stalk (c p) →ₐ[k] Y.presheaf.stalk p := by
  letI := stalkBaseAlgebra s (c p)
  letI := stalkBaseAlgebra t p
  refine { toRingHom := (c.stalkMap p).hom, commutes' := fun a => ?_ }
  have h : stalkConstants (Over.mk s) (c p) ≫ c.stalkMap p =
      stalkConstants (Over.mk t) p := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpecStalk_comp_hom]
    change Spec.map (c.stalkMap p) ≫ X.fromSpecStalk (c p) ≫ s = _
    rw [← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, hc]
    exact fromSpecStalk_comp_hom (Over.mk t) p
  change (stalkConstants (Over.mk s) (c p) ≫ c.stalkMap p).hom a =
    (stalkConstants (Over.mk t) p).hom a
  rw [h]
  rfl

theorem stalkPullbackAlg_germ (hc : c ≫ s = t) {U : X.Opens} {p : Y}
    (hp : p ∈ c ⁻¹ᵁ U) (a : SectionRing s U) :
    stalkPullbackAlg hc p (sectionGermAlg s hp a) =
      sectionGermAlg t hp (sectionPullback hc U a) :=
  c.stalkMap_germ_apply U p hp a

theorem localPointEvalAlg_stalkPullback (hc : c ≫ s = t) (y : Y.BaseFieldPointOver k t)
    (a : X.presheaf.stalk (c (y.hom default))) :
    localPointEvalAlg y (stalkPullbackAlg hc (y.hom default) a) =
      localPointEvalAlg (mapBaseFieldPoint hc y) a := by
  obtain ⟨U, hy, b, rfl⟩ := X.presheaf.exists_germ_eq a
  change localPointEvalAlg y (stalkPullbackAlg hc _ (sectionGermAlg s hy b)) = _
  rw [stalkPullbackAlg_germ, localPointEvalAlg_germ]
  exact (affinePointEval_pullback hc y U hy b).symm.trans
    (localPointEvalAlg_germ (mapBaseFieldPoint hc y) hy b).symm

theorem stalkPullback_formallyEtale [IsFinite c] [Etale c] (p : Y)
    {U : X.Opens} (hU : IsAffineOpen U) (hp : c p ∈ U) :
    (c.stalkMap p).hom.FormallyEtale := by
  let W := c ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage c
  have hg : (c.app U).hom.Etale := by
    rw [c.app_eq_appLE]
    exact c.etale_appLE hU hW le_rfl
  have h₁ : (X.presheaf.germ U (c p) hp).hom.FormallyUnramified := by
    letI := (X.presheaf.germ U (c p) hp).hom.toAlgebra
    letI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk (c p)) := sectionGerm_formallyEtale hU hp
    exact inferInstanceAs (Algebra.FormallyUnramified Γ(X, U) (X.presheaf.stalk (c p)))
  apply RingHom.FormallyEtale.of_comp h₁
  change (X.presheaf.germ U (c p) hp ≫ c.stalkMap p).hom.FormallyEtale
  rw [c.germ_stalkMap]
  have he : (c.app U).hom.FormallyEtale := by
    letI := (c.app U).hom.toAlgebra
    letI : Algebra.Etale Γ(X, U) Γ(Y, W) := hg
    exact inferInstanceAs (Algebra.FormallyEtale Γ(X, U) Γ(Y, W))
  exact he.comp (sectionGerm_formallyEtale hW hp)

end GlobalTheory.SchemeCohomology
