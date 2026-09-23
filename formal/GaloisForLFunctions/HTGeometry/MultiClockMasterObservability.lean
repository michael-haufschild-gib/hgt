import GaloisForLFunctions.HTGeometry.FiniteClockOrthogonalObservability

/-!
# Multi-clock master observability

For a finite family of periodic isometric clocks, this file packages the
observable energy erased by each clock and identifies the joint zero set with
the kernel of the existing finite quantum master constraint.

No pairwise commutativity of the clocks is assumed.  The construction is
kinematical: it describes which values of an observable survive all clock
constraints on an already stationary state, rather than propagating the state
in an external time.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [Fintype ι]

/-- The observable energy erased by one finite periodic clock. -/
def finiteClockObservabilityEnergy
    (U X : E →L[𝕜] E) (N : ℕ) (ψ : E) : ℝ :=
  RCLike.re
    (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ))

/-- Total observable energy erased by a finite family of clocks. -/
def finiteClockFamilyObservabilityEnergy
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ) (ψ : E) : ℝ :=
  ∑ i, finiteClockObservabilityEnergy (U i) X (N i) ψ

theorem finiteClockObservabilityEnergy_eq_erasedNormSq
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    finiteClockObservabilityEnergy U X N ψ =
      ‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ (2 : ℕ) := by
  exact re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hX hψ

theorem finiteClockObservabilityEnergy_nonneg
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    0 ≤ finiteClockObservabilityEnergy U X N ψ :=
  re_inner_finiteCyclicObservableTwirlKadisonDefect_nonneg
    U X N hN hadjoint_mul hperiod hX hψ

theorem finiteClockObservabilityEnergy_eq_zero_iff_physical
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    finiteClockObservabilityEnergy U X N ψ = 0 ↔
      GaloisForLFunctions.PhysicalState (U - 1).toLinearMap (X ψ) :=
  re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_physical
    U X N hN hadjoint_mul hperiod hX hψ

theorem finiteClockFamilyObservabilityEnergy_eq_sum_erasedNormSq
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyObservabilityEnergy U X N ψ =
      ∑ i, ‖(1 - finiteCyclicGaugeAverage (U i) (N i)) (X ψ)‖ ^ (2 : ℕ) := by
  unfold finiteClockFamilyObservabilityEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteClockObservabilityEnergy_eq_erasedNormSq
    (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) hX (hψ i)

theorem finiteClockFamilyObservabilityEnergy_nonneg
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    0 ≤ finiteClockFamilyObservabilityEnergy U X N ψ := by
  unfold finiteClockFamilyObservabilityEnergy
  exact Finset.sum_nonneg fun i hi => finiteClockObservabilityEnergy_nonneg
    (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) hX (hψ i)

theorem finiteClockFamilyObservabilityEnergy_eq_zero_iff_forall_physical
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyObservabilityEnergy U X N ψ = 0 ↔
      ∀ i, GaloisForLFunctions.PhysicalState (U i - 1).toLinearMap (X ψ) := by
  unfold finiteClockFamilyObservabilityEnergy
  have hterm : ∀ i,
      0 ≤ finiteClockObservabilityEnergy (U i) X (N i) ψ := fun i =>
    finiteClockObservabilityEnergy_nonneg
      (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) hX (hψ i)
  constructor
  · intro hzero i
    have hi : finiteClockObservabilityEnergy (U i) X (N i) ψ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp
        hzero i (Finset.mem_univ i)
    exact (finiteClockObservabilityEnergy_eq_zero_iff_physical
      (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) hX (hψ i)).mp hi
  · intro hphysical
    apply Finset.sum_eq_zero
    intro i hi
    exact (finiteClockObservabilityEnergy_eq_zero_iff_physical
      (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) hX (hψ i)).mpr
        (hphysical i)

theorem finiteClockFamilyObservabilityEnergy_eq_zero_iff_masterPhysical
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyObservabilityEnergy U X N ψ = 0 ↔
      GaloisForLFunctions.PhysicalState
        (finiteQuantumMasterConstraint (fun i => U i - 1)).toLinearMap (X ψ) := by
  rw [finiteClockFamilyObservabilityEnergy_eq_zero_iff_forall_physical
    U X N hN hadjoint_mul hperiod hX hψ]
  exact (physicalState_finiteQuantumMasterConstraint_iff
    (fun i => U i - 1) (X ψ)).symm

/-- Zero observable erosion supplies the master-constraint premise required by
the existing Ward-value theorem. -/
theorem finiteClockFamily_zeroEnergy_WardValue_eq_zero
    (U : ι → E →L[𝕜] E) (X A : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : ∀ i, U i ψ = ψ)
    (hzero : finiteClockFamilyObservabilityEnergy U X N ψ = 0) :
    inner 𝕜 (X ψ)
      (finiteQuantumMasterConstraint (fun i => U i - 1) (A (X ψ))) = 0 := by
  apply finiteQuantumMasterConstraint_WardValue_eq_zero (fun i => U i - 1) A
  exact (finiteClockFamilyObservabilityEnergy_eq_zero_iff_forall_physical
    U X N hN hadjoint_mul hperiod hX hψ).mp hzero

end

end HTGeometry
