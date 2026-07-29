import GaloisForLFunctions.HTGeometry.FiniteClockReferenceFrameCovariance
import GaloisForLFunctions.HTGeometry.MultiClockMasterObservability

/-!
# Finite-clock unitary reference-frame master-observability universality

Simultaneous unitary conjugation of a finite clock family, its observed quantity, and its state
preserves total erased observability energy exactly.  The transformed zero-energy locus is the
kernel of the transformed finite quantum master constraint.

This closes operator-valued finite-clock covariance with the scalar multi-clock
master-observability theorem.
-/

open scoped BigOperators

namespace HTGeometry

section Algebraic

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Conjugation by two-sided inverse frame maps carries a shifted clock constraint to the
conjugate of the original shifted constraint. -/
theorem twoSidedConjugation_sub_one
    (U V W : E →L[𝕜] E) (hVW : V * W = 1) :
    V * U * W - 1 = V * (U - 1) * W := by
  calc
    V * U * W - 1 = V * U * W - V * W := by rw [hVW]
    _ = V * (U - 1) * W := by noncomm_ring

/-- Physicality for one bounded constraint is invariant under an invertible two-sided frame
change when the state is moved by the same frame map. -/
theorem physicalState_twoSidedConjugation_iff
    (C V W : E →L[𝕜] E) (ψ : E) (hWV : W * V = 1) :
    GaloisForLFunctions.PhysicalState (V * C * W).toLinearMap (V ψ) ↔
      GaloisForLFunctions.PhysicalState C.toLinearMap ψ := by
  rw [GaloisForLFunctions.PhysicalState, GaloisForLFunctions.PhysicalState]
  change (V * C * W) (V ψ) = 0 ↔ C ψ = 0
  have hleftApply := congrArg
    (fun T : E →L[𝕜] E => T ψ) hWV
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hleftApply
  simp only [mul_apply_eq_comp]
  rw [hleftApply]
  constructor
  · intro h
    have hw := congrArg (fun y : E => W y) h
    change W (V (C ψ)) = W 0 at hw
    rw [map_zero] at hw
    calc
      C ψ = (W * V) (C ψ) := by rw [hWV]; rfl
      _ = W (V (C ψ)) := rfl
      _ = 0 := hw
  · intro h
    rw [h, map_zero]

end Algebraic

noncomputable section

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [Fintype ι]

/-- Total finite-clock observability energy is exactly invariant when clocks, observable, and
state are simultaneously moved by one unitary frame map. -/
theorem finiteClockFamilyObservabilityEnergy_unitaryReferenceFrame
    (U : ι → E →L[𝕜] E) (X V : E →L[𝕜] E)
    (N : ι → ℕ) (ψ : E)
    (hleft : V.adjoint * V = 1) (hright : V * V.adjoint = 1) :
    finiteClockFamilyObservabilityEnergy
        (fun i => V * U i * V.adjoint) (V * X * V.adjoint) N (V ψ) =
      finiteClockFamilyObservabilityEnergy U X N ψ := by
  unfold finiteClockFamilyObservabilityEnergy
  apply Finset.sum_congr rfl
  intro i hi
  unfold finiteClockObservabilityEnergy
  rw [finiteCyclicObservableTwirlKadisonDefect_twoSidedConjugation
    (U i) X V V.adjoint (N i) hleft hright]
  have happly :
      (V * finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) *
          V.adjoint) (V ψ) =
        V (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) ψ) := by
    simp only [mul_apply_eq_comp]
    have hleftApply := congrArg
      (fun T : E →L[𝕜] E => T ψ) hleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun y : E =>
        V (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) y))
        hleftApply
  rw [happly]
  have hinner :
      inner 𝕜 (V ψ)
          (V (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) ψ)) =
        inner 𝕜 ψ
          (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) ψ) := by
    rw [← V.adjoint_inner_left
      (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) ψ) (V ψ)]
    have hleftApply := congrArg
      (fun T : E →L[𝕜] E => T ψ) hleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun y : E => inner 𝕜 y
        (finiteCyclicObservableTwirlKadisonDefect (U i) X (N i) ψ))
        hleftApply
  rw [hinner]

/-- The transformed finite master constraint has exactly the transported original physical
kernel. -/
theorem finiteQuantumMasterConstraint_physical_unitaryReferenceFrame_iff
    (U : ι → E →L[𝕜] E) (X V : E →L[𝕜] E) (ψ : E)
    (hleft : V.adjoint * V = 1) (hright : V * V.adjoint = 1) :
    GaloisForLFunctions.PhysicalState
        (finiteQuantumMasterConstraint
          (fun i => V * U i * V.adjoint - 1)).toLinearMap
        ((V * X * V.adjoint) (V ψ)) ↔
      GaloisForLFunctions.PhysicalState
        (finiteQuantumMasterConstraint (fun i => U i - 1)).toLinearMap
        (X ψ) := by
  rw [physicalState_finiteQuantumMasterConstraint_iff,
    physicalState_finiteQuantumMasterConstraint_iff]
  have hx :
      (V * X * V.adjoint) (V ψ) = V (X ψ) := by
    simp only [mul_apply_eq_comp]
    have hleftApply := congrArg
      (fun T : E →L[𝕜] E => T ψ) hleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg V (congrArg X hleftApply)
  rw [hx]
  constructor
  · intro hall i
    have hi := hall i
    rw [twoSidedConjugation_sub_one (U i) V V.adjoint hright] at hi
    exact
      (physicalState_twoSidedConjugation_iff
        (U i - 1) V V.adjoint (X ψ) hleft).mp hi
  · intro hall i
    rw [twoSidedConjugation_sub_one (U i) V V.adjoint hright]
    exact
      (physicalState_twoSidedConjugation_iff
        (U i - 1) V V.adjoint (X ψ) hleft).mpr (hall i)

/-- **Finite-clock unitary reference-frame master-observability universality law.**  The
transformed total erased energy equals the original energy, and it vanishes exactly on the
transformed finite master-constraint kernel. -/
theorem finiteClockFamily_unitaryReferenceFrameMasterObservabilityUniversality
    (U : ι → E →L[𝕜] E) (X V : E →L[𝕜] E)
    (N : ι → ℕ) (ψ : E)
    (hleft : V.adjoint * V = 1) (hright : V * V.adjoint = 1)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyObservabilityEnergy
        (fun i => V * U i * V.adjoint) (V * X * V.adjoint) N (V ψ) =
      finiteClockFamilyObservabilityEnergy U X N ψ ∧
    (finiteClockFamilyObservabilityEnergy
        (fun i => V * U i * V.adjoint) (V * X * V.adjoint) N (V ψ) = 0 ↔
      GaloisForLFunctions.PhysicalState
        (finiteQuantumMasterConstraint
          (fun i => V * U i * V.adjoint - 1)).toLinearMap
        ((V * X * V.adjoint) (V ψ))) := by
  have hinvariant :=
    finiteClockFamilyObservabilityEnergy_unitaryReferenceFrame
      U X V N ψ hleft hright
  refine ⟨hinvariant, ?_⟩
  rw [hinvariant]
  exact
    (finiteClockFamilyObservabilityEnergy_eq_zero_iff_masterPhysical
      U X N hN hadjoint_mul hperiod hX hψ).trans
      (finiteQuantumMasterConstraint_physical_unitaryReferenceFrame_iff
        U X V ψ hleft hright).symm

end

end HTGeometry
