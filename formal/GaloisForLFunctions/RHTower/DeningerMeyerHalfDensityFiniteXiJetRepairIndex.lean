import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityFiniteXiJetVerticalDefect
import GaloisForLFunctions.HTGeometry.EventComplementaryRecord

/-!
# Repair-memory index of the half-density Xi-jet relation

An off-line finite Xi packet makes the closed half-density observation relation multivalued by
the complete multiplicity-bounded jet packet. This module converts that vertical defect into an
operational lower bound: every finite-dimensional auxiliary linear record which restores faithful
readout must carry at least the packet's total analytic multiplicity.

Thus Xi multiplicity is not only Jordan thickness in Meyer's spectral realization. It is the exact
minimum number of independent coordinates required to repair the information erased by this
half-density completion.
-/

open Complex Filter Set Topology
open scoped Classical

namespace RHTower

noncomputable section

/-- Closed full finite Xi-jet observation relation in the canonical half-density completion. -/
def deningerMeyerFiniteXiJetClosedRelation
    (S : Finset XiDivisorSupport) :
    Submodule ℂ
      (DeningerMeyerHalfDensityCompletion × DeningerMeyerFiniteXiJetPacket S) :=
  (deningerMeyerFiniteXiJetGraph S).topologicalClosure

/-- Source projection from the closed Xi-jet relation. Its kernel is the multivalued defect. -/
def deningerMeyerFiniteXiJetClosedSourceProjection
    (S : Finset XiDivisorSupport) :
    ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ]
      DeningerMeyerHalfDensityCompletion :=
  (LinearMap.fst ℂ DeningerMeyerHalfDensityCompletion
      (DeningerMeyerFiniteXiJetPacket S)).domRestrict
    (deningerMeyerFiniteXiJetClosedRelation S)

/-- A vertical output is exactly a source-invisible vector of the closed relation. -/
def deningerMeyerFiniteXiJetVerticalToSourceKernel
    (S : Finset XiDivisorSupport) :
    deningerMeyerFiniteXiJetGraphVertical S →ₗ[ℂ]
      LinearMap.ker (deningerMeyerFiniteXiJetClosedSourceProjection S) where
  toFun y :=
    ⟨⟨(0, y.1), y.2⟩, by
      simp [deningerMeyerFiniteXiJetClosedSourceProjection]⟩
  map_add' y z := by
    ext <;> simp
  map_smul' c y := by
    ext <;> simp

theorem deningerMeyerFiniteXiJetVerticalToSourceKernel_bijective
    (S : Finset XiDivisorSupport) :
    Function.Bijective (deningerMeyerFiniteXiJetVerticalToSourceKernel S) := by
  constructor
  · intro y z h
    apply Subtype.ext
    exact congrArg
      (fun w : LinearMap.ker (deningerMeyerFiniteXiJetClosedSourceProjection S) =>
        w.1.1.2) h
  · intro z
    let y : deningerMeyerFiniteXiJetGraphVertical S :=
      ⟨z.1.1.2, by
        have hz : z.1.1.1 = 0 := by
          have hz0 : deningerMeyerFiniteXiJetClosedSourceProjection S z.1 = 0 := z.2
          change z.1.1.1 = 0 at hz0
          exact hz0
        change (0, z.1.1.2) ∈
          (deningerMeyerFiniteXiJetGraph S).topologicalClosure
        have hmem := z.1.2
        change (z.1.1.1, z.1.1.2) ∈
          (deningerMeyerFiniteXiJetGraph S).topologicalClosure at hmem
        rwa [hz] at hmem⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hz : z.1.1.1 = 0 := by
        have hz0 : deningerMeyerFiniteXiJetClosedSourceProjection S z.1 = 0 := z.2
        change z.1.1.1 = 0 at hz0
        exact hz0
      exact hz.symm
    · rfl

/-- The vertical fibre and the information erased by source projection are linearly identical. -/
def deningerMeyerFiniteXiJetVerticalSourceKernelEquiv
    (S : Finset XiDivisorSupport) :
    deningerMeyerFiniteXiJetGraphVertical S ≃ₗ[ℂ]
      LinearMap.ker (deningerMeyerFiniteXiJetClosedSourceProjection S) :=
  LinearEquiv.ofBijective
    (deningerMeyerFiniteXiJetVerticalToSourceKernel S)
    (deningerMeyerFiniteXiJetVerticalToSourceKernel_bijective S)

/-- Off line, source projection erases exactly the total analytic Xi multiplicity. -/
theorem finrank_deningerMeyerFiniteXiJetClosedSourceProjection_ker_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2) :
    Module.finrank ℂ
        (LinearMap.ker (deningerMeyerFiniteXiJetClosedSourceProjection S)) =
      deningerMeyerFiniteXiTotalMultiplicity S := by
  rw [← finrank_deningerMeyerFiniteXiJetGraphVertical_of_offline S hoffline]
  exact (LinearEquiv.finrank_eq
    (deningerMeyerFiniteXiJetVerticalSourceKernelEquiv S)).symm

/-- Canonical auxiliary record: retain the output coordinate of the closed relation. -/
def deningerMeyerFiniteXiJetClosedOutputProjection
    (S : Finset XiDivisorSupport) :
    ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ]
      DeningerMeyerFiniteXiJetPacket S :=
  (LinearMap.snd ℂ DeningerMeyerHalfDensityCompletion
      (DeningerMeyerFiniteXiJetPacket S)).domRestrict
    (deningerMeyerFiniteXiJetClosedRelation S)

/-- Source and canonical output coordinates faithfully recover every point of the relation. -/
theorem deningerMeyerFiniteXiJetClosedProjections_injective
    (S : Finset XiDivisorSupport) :
    Function.Injective
      ((deningerMeyerFiniteXiJetClosedSourceProjection S).prod
        (deningerMeyerFiniteXiJetClosedOutputProjection S)) := by
  intro x y h
  apply Subtype.ext
  exact h

/-- The canonical record has dimension equal to total analytic Xi multiplicity. -/
theorem finrank_deningerMeyerFiniteXiJetPacket
    (S : Finset XiDivisorSupport) :
    Module.finrank ℂ (DeningerMeyerFiniteXiJetPacket S) =
      deningerMeyerFiniteXiTotalMultiplicity S := by
  rw [← card_deningerMeyerFiniteXiJetSlot S]
  simp

universe u

/-- **Xi repair-memory index.** Every finite-dimensional linear record which, together with the
half-density source coordinate, faithfully resolves the closed off-line Xi-jet relation has output
dimension at least the packet's total analytic multiplicity. -/
theorem deningerMeyerFiniteXiJetRepair_finrank_lower_bound
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (E : Type u) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (record : ↥(deningerMeyerFiniteXiJetClosedRelation S) →ₗ[ℂ] E)
    (hfaithful : Function.Injective
      ((deningerMeyerFiniteXiJetClosedSourceProjection S).prod record)) :
    deningerMeyerFiniteXiTotalMultiplicity S ≤ Module.finrank ℂ E := by
  rw [← finrank_deningerMeyerFiniteXiJetClosedSourceProjection_ker_of_offline S hoffline]
  exact GaloisForLFunctions.HTGeometry.eventRecord_finrank_lower_bound
    (deningerMeyerFiniteXiJetClosedSourceProjection S) record hfaithful

end
end RHTower
