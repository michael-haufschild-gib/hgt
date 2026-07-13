import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compact uniform finite probes for surjective control families

Pointwise controllability does not by itself provide the finite-dimensional parameter manifold
required by parametric transversality.  This module proves the missing compact uniformization law.

Let `L h : X →L[ℝ] Y` vary continuously, with finite-dimensional target `Y`.  If `L h` is
surjective at one point, a finite-dimensional subspace of `X` remains surjectively controlling on
an open neighborhood: choose a linear right inverse at the point and use nonvanishing of the
determinant of `L h` composed with that right inverse.  A compact set then has a finite subcover;
the finite sum of the local probe spaces controls every point of the compact family.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A surjective member of a continuous finite-target control family admits one finitely generated
probe subspace which remains surjective throughout an open neighborhood. -/
theorem exists_local_finiteProbe_of_continuous_surjectiveControl
    {H X Y : Type*} [TopologicalSpace H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : H → (X →L[ℝ] Y)) (hL : Continuous L) (h₀ : H)
    (hsurj : Function.Surjective (L h₀)) :
    ∃ U : Set H, ∃ V : Submodule ℝ X,
      IsOpen U ∧ h₀ ∈ U ∧ V.FG ∧
        ∀ h ∈ U, Function.Surjective ((L h).domRestrict V) := by
  have hrange : (L h₀).toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  obtain ⟨s, hs⟩ :=
    (L h₀).toLinearMap.exists_rightInverse_of_surjective hrange
  let sc : Y →L[ℝ] X := LinearMap.toContinuousLinearMap s
  let V : Submodule ℝ X := LinearMap.range s
  let g : H → (Y →L[ℝ] Y) := fun h => (L h).comp sc
  let U : Set H := {h | (g h).det ≠ 0}
  have hg : Continuous g := hL.clm_comp continuous_const
  have hU : IsOpen U := by
    exact isOpen_ne.preimage (ContinuousLinearMap.continuous_det.comp hg)
  have hgh₀ : g h₀ = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hs y
  have hh₀ : h₀ ∈ U := by
    simp [U, hgh₀, ContinuousLinearMap.det, LinearMap.det_id]
  have hV : V.FG := Submodule.fg_range s
  refine ⟨U, V, hU, hh₀, hV, ?_⟩
  intro h hh y
  have hgdet : (g h).det ≠ 0 := hh
  let e : Y ≃L[ℝ] Y := (g h).toContinuousLinearEquivOfDetNeZero hgdet
  let x : Y := e.symm y
  let v : V := ⟨s x, ⟨x, rfl⟩⟩
  refine ⟨v, ?_⟩
  change L h (s x) = y
  change g h x = y
  exact e.apply_symm_apply y

/-- **Compact uniform finite-probe law.** A continuous compact family of surjective controls with
one fixed finite-dimensional target admits a single finitely generated probe subspace on which
every control remains surjective. -/
theorem compact_surjectiveControls_have_uniform_finiteProbe
    {H X Y : Type*} [TopologicalSpace H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : H → (X →L[ℝ] Y)) (hL : Continuous L)
    (K : Set H) (hK : IsCompact K)
    (hsurj : ∀ h ∈ K, Function.Surjective (L h)) :
    ∃ V : Submodule ℝ X, V.FG ∧
      ∀ h ∈ K, Function.Surjective ((L h).domRestrict V) := by
  choose U V hUopen hhU hVfg hVU using
    fun h : K => exists_local_finiteProbe_of_continuous_surjectiveControl
      L hL h.1 (hsurj h.1 h.2)
  obtain ⟨s, hscover⟩ := hK.elim_finite_subcover (fun h : K => U h)
    (fun h => hUopen h) (by
      intro h hh
      exact Set.mem_iUnion.mpr ⟨⟨h, hh⟩, hhU ⟨h, hh⟩⟩)
  let W : Submodule ℝ X := s.sup V
  have hWfg : W.FG :=
    Submodule.fg_finset_sup s V (fun i _ => hVfg i)
  refine ⟨W, hWfg, ?_⟩
  intro h hh y
  have hhcover := hscover hh
  simp only [Set.mem_iUnion] at hhcover
  obtain ⟨j, hjs, hjU⟩ := hhcover
  obtain ⟨v, hv⟩ := hVU j h hjU y
  have hle : V j ≤ W := Finset.le_sup hjs
  exact ⟨⟨v.1, hle v.2⟩, hv⟩

end

end GaloisForLFunctions.HTGeometry
