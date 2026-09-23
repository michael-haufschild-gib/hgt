import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionRankLaw
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Multiple-Gamma period-action properness law

This module proves exact topological nonproperness of the finite marked action and constructs the
effective boundary `Z^(2 : ℕ)` action as a proper, cocompact lattice action on `C`.
-/

open Set Topology Complex

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-! ## Properness of the marked action graph -/

/-- Source-target graph of a marked translation action. -/
def markedActionGraph (p : MultipleGammaPeriodSource →+ ℂ) :
    MultipleGammaPeriodSource × ℂ → ℂ × ℂ :=
  fun nz => (p nz.1 + nz.2, nz.2)

/-- A marked translation action whose image is not closed cannot be proper. -/
theorem markedActionGraph_not_isProperMap_of_not_closed
    (p : MultipleGammaPeriodSource →+ ℂ) (hp : ¬ IsClosed (p.range : Set ℂ)) :
    ¬ IsProperMap (markedActionGraph p) := by
  intro hproper
  have hzero : IsClosed (Set.univ ×ˢ ({0} : Set ℂ)) :=
    (isClosed_univ : IsClosed (Set.univ : Set MultipleGammaPeriodSource)).prod
      isClosed_singleton
  have himage : markedActionGraph p '' (Set.univ ×ˢ ({0} : Set ℂ)) =
      (p.range : Set ℂ) ×ˢ ({0} : Set ℂ) := by
    ext w
    constructor
    · rintro ⟨⟨n, z⟩, ⟨-, hz⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨⟨n, by simp [markedActionGraph]⟩, rfl⟩
    · rintro ⟨hwRange, hwZero⟩
      rcases hwRange with ⟨n, hn⟩
      simp only [Set.mem_singleton_iff] at hwZero
      refine ⟨(n, 0), ⟨Set.mem_univ _, rfl⟩, ?_⟩
      ext
      · simpa [markedActionGraph] using hn
      · exact hwZero.symm
  have hclosedProd : IsClosed ((p.range : Set ℂ) ×ˢ ({0} : Set ℂ)) := by
    rw [← himage]
    exact hproper.isClosedMap _ hzero
  apply hp
  have hc : Continuous (fun x : ℂ => (x, (0 : ℂ))) :=
    continuous_id.prodMk continuous_const
  have hpre := hclosedProd.preimage hc
  simpa using hpre

/-- Every finite multiple-Gamma marked translation action is nonproper. -/
theorem finiteMultipleGammaAction_not_proper (m : ℕ+) :
    ¬ IsProperMap (markedActionGraph (finiteMultipleGammaPeriodMap m)) :=
  markedActionGraph_not_isProperMap_of_not_closed _
    (finiteMultipleGammaPeriodSubgroup_not_isClosed m)

/-! ## Effective boundary lattice action -/

/-- Effective boundary lattice after rigidification by the rank-one kernel. -/
abbrev BoundaryEffectiveSource := Fin 2 → ℤ

/-- Effective boundary period embedding `(a,b) ↦ a + bi`. -/
def boundaryEffectivePeriodMap : BoundaryEffectiveSource →+ ℂ where
  toFun n :=
    Complex.equivRealProdCLM.toContinuousAddEquiv.symm ((n 0 : ℝ), (n 1 : ℝ))
  map_zero' := by simp
  map_add' x y := by
    rw [show ((↑((x + y) 0), ↑((x + y) 1)) : ℝ × ℝ) =
        ((x 0 : ℝ), (x 1 : ℝ)) + ((y 0 : ℝ), (y 1 : ℝ)) by
      ext <;> simp]
    exact Complex.equivRealProdCLM.toContinuousAddEquiv.symm.map_add _ _

theorem boundaryEffectivePeriodMap_apply (n : BoundaryEffectiveSource) :
    boundaryEffectivePeriodMap n = (n 0 : ℂ) + (n 1 : ℂ) * Complex.I := by
  change Complex.equivRealProdCLM.symm ((n 0 : ℝ), (n 1 : ℝ)) = _
  simpa using Complex.equivRealProdCLM_symm_apply ((n 0 : ℝ), (n 1 : ℝ))

/-- Effective boundary period realization is a closed topological embedding. -/
theorem boundaryEffectivePeriodMap_isClosedEmbedding :
    IsClosedEmbedding boundaryEffectivePeriodMap := by
  let hpi : BoundaryEffectiveSource ≃ₜ ℤ × ℤ :=
    Homeomorph.piFinTwo (fun _ : Fin 2 => ℤ)
  have hcast : IsClosedEmbedding (Prod.map ((↑) : ℤ → ℝ) ((↑) : ℤ → ℝ)) :=
    Real.isClosedEmbedding_intCast.prodMap Real.isClosedEmbedding_intCast
  have h :=
    Complex.equivRealProdCLM.toContinuousAddEquiv.symm.toHomeomorph.isClosedEmbedding.comp
      (hcast.comp hpi.isClosedEmbedding)
  change IsClosedEmbedding (fun n : BoundaryEffectiveSource =>
    Complex.equivRealProdCLM.symm ((n 0 : ℝ), (n 1 : ℝ)))
  have hfun :
      (fun n : BoundaryEffectiveSource =>
        Complex.equivRealProdCLM.symm ((n 0 : ℝ), (n 1 : ℝ))) =
        (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) ∘
          Prod.map ((↑) : ℤ → ℝ) ((↑) : ℤ → ℝ) ∘ hpi := by
    funext n
    rfl
  rw [hfun]
  exact h

instance : VAdd BoundaryEffectiveSource ℂ where
  vadd n z := boundaryEffectivePeriodMap n + z

instance : AddAction BoundaryEffectiveSource ℂ where
  zero_vadd z := by
    change boundaryEffectivePeriodMap 0 + z = z
    rw [map_zero, zero_add]
  add_vadd n k z := by
    change boundaryEffectivePeriodMap (n + k) + z =
      boundaryEffectivePeriodMap n + (boundaryEffectivePeriodMap k + z)
    rw [map_add]
    abel

/-- Effective boundary `Z^(2 : ℕ)` translation action is proper. -/
theorem boundaryEffectiveAction_proper : ProperVAdd BoundaryEffectiveSource ℂ := by
  exact properVAdd_of_isClosedEmbedding boundaryEffectivePeriodMap
    boundaryEffectivePeriodMap_isClosedEmbedding (fun _ _ => rfl)

/-- Effective and marked boundary realizations have the same period lattice. -/
theorem boundaryEffectivePeriodMap_range :
    boundaryEffectivePeriodMap.range = boundaryMultipleGammaPeriodSubgroup := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨![n 0, n 1, 0], ?_⟩
    rw [boundaryMultipleGammaPeriodMap_apply, boundaryEffectivePeriodMap_apply]
    simp
  · rintro ⟨n, rfl⟩
    refine ⟨boundaryMultipleGammaEffectiveCoordinates n, ?_⟩
    rw [boundaryEffectivePeriodMap_apply, boundaryMultipleGammaPeriodMap_apply]
    simp [boundaryMultipleGammaEffectiveCoordinates]
    ring

/-- Effective boundary quotient is compact, hence the action is cocompact. -/
theorem boundaryEffectiveQuotient_compactSpace :
    CompactSpace (ℂ ⧸ boundaryEffectivePeriodMap.range) := by
  rw [boundaryEffectivePeriodMap_range]
  exact boundaryMultipleGammaCoarseQuotient_compactSpace

end

end HTGeometry
end GaloisForLFunctions
