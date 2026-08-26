import GaloisForLFunctions.HTGeometry.ParametricRootCovering
import GaloisForLFunctions.HTGeometry.LocalHomeomorphPullback

/-!
# Continuous base change of simple analytic root loci

This module identifies the direct substituted zero locus with the topological fibre product and
transports the implicit-function charts through arbitrary continuous parameter maps.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Set

noncomputable section

variable {P X : Type*} [TopologicalSpace X]

/-- Root locus after pulling a scalar relation back along a parameter map. -/
def ParametricRootBaseChange (f : P × ℂ → ℂ) (c : X → P) : Set (X × ℂ) :=
  {q | f (c q.1, q.2) = 0}

/-- Projection of a base-changed root locus. -/
def parametricRootBaseChangeProj {f : P × ℂ → ℂ} {c : X → P}
    (q : ParametricRootBaseChange f c) : X := q.1.1

/-- Direct root-locus base change as the topological pullback of the ambient root projection. -/
def parametricRootBaseChangeToPullback {f : P × ℂ → ℂ} {c : X → P}
    (q : ParametricRootBaseChange f c) :
    LocalHomeomorphPullback (parametricRootProj (f := f)) c :=
  ⟨(q.1.1, ⟨(c q.1.1, q.1.2), q.2⟩), rfl⟩

/-- The topological pullback recovered as a direct base-changed root locus. -/
def parametricRootBaseChangeFromPullback {f : P × ℂ → ℂ} {c : X → P}
    (q : LocalHomeomorphPullback (parametricRootProj (f := f)) c) :
    ParametricRootBaseChange f c := by
  refine ⟨(q.1.1, q.1.2.1.2), ?_⟩
  have hcoeff : c q.1.1 = q.1.2.1.1 := q.2
  show f (c q.1.1, q.1.2.1.2) = 0
  rw [hcoeff]
  exact q.1.2.2

omit [TopologicalSpace X] in
theorem parametricRootBaseChange_left_inv {f : P × ℂ → ℂ} {c : X → P}
    (q : ParametricRootBaseChange f c) :
    parametricRootBaseChangeFromPullback (parametricRootBaseChangeToPullback q) = q := by
  rfl

omit [TopologicalSpace X] in
theorem parametricRootBaseChange_right_inv {f : P × ℂ → ℂ} {c : X → P}
    (q : LocalHomeomorphPullback (parametricRootProj (f := f)) c) :
    parametricRootBaseChangeToPullback (parametricRootBaseChangeFromPullback q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact q.2
    · rfl

/-- The direct and fibre-product presentations of a root-locus base change are homeomorphic. -/
def parametricRootBaseChangeHomeomorph {f : P × ℂ → ℂ} {c : X → P}
    [TopologicalSpace P] (hc : Continuous c) :
    ParametricRootBaseChange f c ≃ₜ
      LocalHomeomorphPullback (parametricRootProj (f := f)) c :=
  Homeomorph.mk
    { toFun := parametricRootBaseChangeToPullback
      invFun := parametricRootBaseChangeFromPullback
      left_inv := parametricRootBaseChange_left_inv
      right_inv := parametricRootBaseChange_right_inv }
    (by
      apply Continuous.subtype_mk
      have hx : Continuous (fun q : ParametricRootBaseChange f c => q.1.1) :=
        continuous_fst.comp continuous_subtype_val
      have hz : Continuous (fun q : ParametricRootBaseChange f c => q.1.2) :=
        continuous_snd.comp continuous_subtype_val
      have hroot : Continuous (fun q : ParametricRootBaseChange f c =>
          ((c q.1.1, q.1.2) : P × ℂ)) := (hc.comp hx).prodMk hz
      have hrootSub : Continuous (fun q : ParametricRootBaseChange f c =>
          (⟨(c q.1.1, q.1.2), q.2⟩ : ParametricRootLocus f)) :=
        Continuous.subtype_mk hroot (fun q => q.2)
      exact hx.prodMk hrootSub)
    (by
      apply Continuous.subtype_mk
      have hx : Continuous (fun q :
          LocalHomeomorphPullback (parametricRootProj (f := f)) c => q.1.1) :=
        continuous_fst.comp continuous_subtype_val
      have hroot : Continuous (fun q :
          LocalHomeomorphPullback (parametricRootProj (f := f)) c => q.1.2.1) :=
        continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
      exact hx.prodMk (continuous_snd.comp hroot))

/-- A pointwise chart for a continuously base-changed analytic root relation.  Only simplicity of
the selected root is required; other fibres may be singular. -/
theorem exists_chart_parametricRootBaseChangeProj
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {c : X → P} (hc : Continuous c)
    (q : ParametricRootBaseChange f c)
    (hf : AnalyticAt ℂ f (c q.1.1, q.1.2))
    (hvertical : (fderiv ℂ f (c q.1.1, q.1.2)) (0, 1) ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (ParametricRootBaseChange f c) X,
      q ∈ φ.source ∧ parametricRootBaseChangeProj = φ := by
  let H := parametricRootBaseChangeHomeomorph (f := f) hc
  let q' := H q
  have hcoeff : c q'.1.1 = q'.1.2.1.1 := q'.2
  obtain ⟨e, hqe, hproj⟩ := exists_chart_parametricRootProj q'.1.2
    (by
      change AnalyticAt ℂ f (c q.1.1, q.1.2)
      exact hf)
    (by
      change (fderiv ℂ f (c q.1.1, q.1.2)) (0, 1) ≠ 0
      exact hvertical)
  obtain ⟨φ, hqφ, hφ⟩ := exists_chart_localHomeomorphPullbackProj_of_chart
    q' e hqe hproj hc
  let ψ : OpenPartialHomeomorph (ParametricRootBaseChange f c) X :=
    H.toOpenPartialHomeomorph.trans φ
  refine ⟨ψ, ?_, ?_⟩
  · simpa [ψ] using hqφ
  · funext x
    change localHomeomorphPullbackProj (H x) = φ (H x)
    rw [hφ]

/-- A continuous base change of an analytic relation with simple roots has locally homeomorphic
root projection. -/
theorem isLocalHomeomorph_parametricRootBaseChangeProj
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {c : X → P} (hc : Continuous c)
    (hf : ∀ x z, AnalyticAt ℂ f (c x, z))
    (hvertical : ∀ x z, f (c x, z) = 0 →
      (fderiv ℂ f (c x, z)) (0, 1) ≠ 0) :
    IsLocalHomeomorph (parametricRootBaseChangeProj (f := f) (c := c)) := by
  intro q
  exact exists_chart_parametricRootBaseChangeProj hc q
    (hf q.1.1 q.1.2)
    (hvertical q.1.1 q.1.2 q.2)

end

end GaloisForLFunctions.HTGeometry
