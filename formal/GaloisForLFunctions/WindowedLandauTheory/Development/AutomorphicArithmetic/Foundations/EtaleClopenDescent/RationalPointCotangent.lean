import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalCotangentFibre
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalPointStalkAlgebra

/-! The cotangent endomorphism of an étale correspondence at a fixed
point, defined by its two pullbacks on local rings. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

abbrev CotangentAt (y : Y.BaseFieldPointOver k t) :=
  letI := stalkBaseAlgebra t (y.hom default)
  CotangentFibre (localPointEvalAlg y)

/-- The differential of a germ at the rational point. -/
def cotangentAtD (y : Y.BaseFieldPointOver k t) (a : Y.presheaf.stalk (y.hom default)) :
    CotangentAt y :=
  letI := stalkBaseAlgebra t (y.hom default)
  cotangentFibreD (localPointEvalAlg y) a

/-- Localization from an affine chart identifies its cotangent fibre with
the cotangent fibre of the local ring. -/
def chartCotangentEquiv (y : Y.BaseFieldPointOver k t) {U : Y.Opens}
    (hU : IsAffineOpen U) (hy : y.hom default ∈ U) :
    CotangentFibre (affinePointEval y hy) ≃ₗ[k] CotangentAt y := by
  letI := stalkBaseAlgebra t (y.hom default)
  exact cotangentFibreEtaleEquiv (affinePointEval y hy) (localPointEvalAlg y)
    (sectionGermAlg t hy) (AlgHom.ext (localPointEvalAlg_germ y hy))
    (sectionGerm_formallyEtale hU hy)

theorem chartCotangentEquiv_D (y : Y.BaseFieldPointOver k t) {U : Y.Opens}
    (hU : IsAffineOpen U) (hy : y.hom default ∈ U) (a : SectionRing t U) :
    chartCotangentEquiv y hU hy (cotangentFibreD (affinePointEval y hy) a) =
      cotangentAtD y (sectionGermAlg t hy a) := by
  letI := stalkBaseAlgebra t (y.hom default)
  exact cotangentFibreEtaleEquiv_D _ _ _ _ _ a

variable {c c₁ c₂ : Y ⟶ X}

/-- An étale morphism induces an isomorphism on cotangent fibres at
compatible rational points. -/
def cotangentPullbackEquiv [IsFinite c] [Etale c] (hc : c ≫ s = t)
    (y : Y.BaseFieldPointOver k t) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : y.hom default ∈ c ⁻¹ᵁ U) :
    CotangentAt (mapBaseFieldPoint hc y) ≃ₗ[k] CotangentAt y := by
  letI := stalkBaseAlgebra s ((mapBaseFieldPoint hc y).hom default)
  letI := stalkBaseAlgebra t (y.hom default)
  exact cotangentFibreEtaleEquiv (localPointEvalAlg (mapBaseFieldPoint hc y)) (localPointEvalAlg y)
    (stalkPullbackAlg hc (y.hom default)) (AlgHom.ext (localPointEvalAlg_stalkPullback hc y))
    (stalkPullback_formallyEtale (y.hom default) hU hy)

theorem cotangentPullbackEquiv_D [IsFinite c] [Etale c] (hc : c ≫ s = t)
    (y : Y.BaseFieldPointOver k t) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : y.hom default ∈ c ⁻¹ᵁ U) (a : SectionRing s U) :
    cotangentPullbackEquiv hc y hU hy
        (cotangentAtD (mapBaseFieldPoint hc y) (sectionGermAlg s hy a)) =
      cotangentAtD y (sectionGermAlg t hy (sectionPullback hc U a)) := by
  letI := stalkBaseAlgebra s ((mapBaseFieldPoint hc y).hom default)
  letI := stalkBaseAlgebra t (y.hom default)
  exact (cotangentFibreEtaleEquiv_D (localPointEvalAlg (mapBaseFieldPoint hc y))
    (localPointEvalAlg y) (stalkPullbackAlg hc (y.hom default))
    (AlgHom.ext (localPointEvalAlg_stalkPullback hc y))
    (stalkPullback_formallyEtale (y.hom default) hU hy) (sectionGermAlg s hy a)).trans
    (congrArg (cotangentAtD y) (stalkPullbackAlg_germ hc hy a))

section Fixed

variable [IsFinite c₁] [Etale c₁] [IsFinite c₂] [Etale c₂]
  (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) (y : Y.BaseFieldPointOver k t)
  (h : mapBaseFieldPoint h₁ y = mapBaseFieldPoint h₂ y)
  {U : X.Opens} (hU : IsAffineOpen U)
  (hy₁ : y.hom default ∈ c₁ ⁻¹ᵁ U) (hy₂ : y.hom default ∈ c₂ ⁻¹ᵁ U)

/-- Invert the first cotangent pullback and then apply the second. -/
def fixedCotangentEquiv : CotangentAt y ≃ₗ[k] CotangentAt y :=
  (cotangentPullbackEquiv h₁ y hU hy₁).symm.trans
    (h.symm ▸ cotangentPullbackEquiv h₂ y hU hy₂)

private theorem cotangentEquiv_apply_differential
    {z z' : X.BaseFieldPointOver k s} (e : z = z') {V : Type}
    [AddCommGroup V] [Module k V] (g : CotangentAt z' ≃ₗ[k] V)
    (hz : z.hom default ∈ U) (hz' : z'.hom default ∈ U) (a : SectionRing s U) :
    (e.symm ▸ g : CotangentAt z ≃ₗ[k] V)
        (cotangentAtD z (sectionGermAlg s hz a)) =
      g (cotangentAtD z' (sectionGermAlg s hz' a)) := by
  cases e
  rfl

theorem fixedCotangentEquiv_D (a : SectionRing s U) :
    fixedCotangentEquiv h₁ h₂ y h hU hy₁ hy₂
        (cotangentAtD y (sectionGermAlg t hy₁ (sectionPullback h₁ U a))) =
      cotangentAtD y (sectionGermAlg t hy₂ (sectionPullback h₂ U a)) := by
  unfold fixedCotangentEquiv
  rw [LinearEquiv.trans_apply, ← cotangentPullbackEquiv_D h₁ y hU hy₁,
    LinearEquiv.symm_apply_apply]
  exact (cotangentEquiv_apply_differential h (cotangentPullbackEquiv h₂ y hU hy₂)
    hy₁ hy₂ a).trans (cotangentPullbackEquiv_D h₂ y hU hy₂ a)

end Fixed

end GlobalTheory.SchemeCohomology
