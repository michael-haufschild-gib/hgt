import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothComponents
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! Geometrically connected smooth fibres are integral when they are quasi-compact. -/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory

/-- A connected quasi-compact smooth scheme over a field has one integral component. -/
theorem isIntegral_of_smooth_field_of_compact_of_connected {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (.of K)) [Smooth f] [CompactSpace X] [ConnectedSpace X] : IsIntegral X := by
  obtain ⟨J, _, V, hdisj, hcov, hI⟩ :=
    UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth X f
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, V i from hcov.symm ▸ trivial)
  let U : X.Opens := ⨆ j : {j : J // j ≠ i}, V j.1
  have hU : (U : Set X) = (V i : Set X)ᶜ := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨j, hj⟩, hzj⟩ := Opens.mem_iSup.mp (show z ∈ U from hz)
      intro hzi
      have hb : z ∈ V j ⊓ V i := ⟨hzj, hzi⟩
      rw [hdisj j i hj] at hb
      exact hb
    · intro hz
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show z ∈ ⨆ j, V j from hcov.symm ▸ trivial)
      exact Opens.mem_iSup.mpr ⟨⟨j, fun e => hz (e ▸ hj)⟩, hj⟩
  have hclosed : IsClosed (V i : Set X) := isOpen_compl_iff.mp (hU ▸ U.isOpen)
  have htop : V i = ⊤ := Opens.ext (IsClopen.eq_univ ⟨hclosed, (V i).isOpen⟩ ⟨x, hi⟩)
  haveI : IsIntegral (⊤ : X.Opens).toScheme := htop ▸ hI i
  exact IsIntegral.of_isIso X.topIso.hom

/-- Geometric connectedness and smoothness give geometric integrality for a quasi-compact morphism. -/
theorem geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected {X S : Scheme}
    (f : X ⟶ S) [QuasiCompact f] [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹Smooth f›
  haveI : QuasiCompact snd := MorphismProperty.of_isPullback (P := @QuasiCompact) h ‹QuasiCompact f›
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace snd
  haveI : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field_of_compact_of_connected snd

end GlobalTheory
