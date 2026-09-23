import GaloisForLFunctions.HTGeometry.TotalDegreePolynomialCircuitReplicaHilbertLaw
import GaloisForLFunctions.RHTower.PolynomialCircuitCarrierFirstEntryLaw

/-!
# Total-degree circuit carrier first-entry law

The exact total-degree Hilbert carrier contains every continuous exact-`s`
two-qubit Choi circuit target.  Its rank is the simplex feature count

`(n*n)^s * Nat.choose (r*s + 16*s) (16*s)`.

Combining this carrier with return-excised coarea proves continuous exclusion
from end of initial ramp through any prescribed first-reentry horizon whenever
its quenched incidence action is below explicit threshold.  Complete circuit
union is retained; only initial return interval is removed.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem returnExcisedReplicaCarrierIncidenceAction_nonneg
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (returnSet : Set X) :
    0 ≤ returnExcisedReplicaCarrierIncidenceAction μ r S state returnSet := by
  unfold returnExcisedReplicaCarrierIncidenceAction
  unfold returnExcisedFiniteCoordinateIncidenceAction
  apply integral_nonneg
  intro p
  exact sq_nonneg _

end GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Total-degree carrier first-entry law for the complete continuous exact-`s`
two-qubit Choi circuit class. The action pays the exact simplex feature count,
not the coordinatewise-degree box count. -/
theorem no_second_twoQubitCircuitChoiCapture_of_totalDegreeCarrierAction_lt
    {C : Type*} {n s : ℕ}
    (pos : C → TwoQubitCircuit.twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, TwoQubitCircuit.IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (D : (((Fin n → Bool) × (Fin n → Bool)) → ℂ) →
      (((Fin n → Bool) × (Fin n → Bool)) → ℂ) → ℝ)
    (psi : ℝ → ((Fin n → Bool) × (Fin n → Bool)) → ℂ)
    (r : ℕ)
    (htarget : ∀ c, finiteComplexInner
      (fun p : (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool)))
      (fun p : (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) = 1)
    {speed epsn epsw T threshold : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ t u c,
      D (psi t) (fun p => (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool))) ≤
        D (psi t) (psi u) +
          D (psi u) (fun p => (List.ofFn (G c)).prod p.1 p.2 /
            Real.sqrt (Fintype.card (Fin n → Bool))))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c,
      D (psi t) (fun p => (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t)
        (fun p => (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool))))
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (TwoQubitCircuit.twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r)
        (psi (T * x)) i)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (TwoQubitCircuit.twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r)
        (psi (T * x)) i‖ ^ (2 : ℕ))
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (haction :
      (((n * n) ^ s * (r * s + s * 16).choose (s * 16) : ℕ) : ℝ) *
        returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r
          (TwoQubitCircuit.twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r)
          (fun x => psi (T * x))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)) <
      (gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
        threshold ^ r) ^ (2 : ℕ)) :
    ¬ ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t)
        (fun p => (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool))) ≤ epsn := by
  let target : C → ((Fin n → Bool) × (Fin n → Bool)) → ℂ :=
    fun c p => (List.ofFn (G c)).prod p.1 p.2 /
      Real.sqrt (Fintype.card (Fin n → Bool))
  let S := TwoQubitCircuit.twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r
  have hmem : ∀ c, finitePureTensorPowerEuclidean r (target c) ∈ S := by
    intro c
    exact TwoQubitCircuit.finitePureTensorPowerEuclidean_twoQubitCircuitChoi_mem_totalDegreeCarrier
      pos G hG r c
  have hactionNonneg : 0 ≤
      returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
        (fun x => psi (T * x))
        (Icc (-(epsw / speed / T)) (epsw / speed / T)) :=
    returnExcisedReplicaCarrierIncidenceAction_nonneg _ _ _ _ _
  have hrankNat : Module.finrank ℂ S ≤
      (n * n) ^ s * (r * s + s * 16).choose (s * 16) :=
    TwoQubitCircuit.finrank_twoQubitCircuitChoiTotalDegreeReplicaCarrier_le n s r
  have hrankReal : (Module.finrank ℂ S : ℝ) ≤
      (((n * n) ^ s * (r * s + s * 16).choose (s * 16) : ℕ) : ℝ) := by
    exact_mod_cast hrankNat
  have hsmall :
      (Module.finrank ℂ S : ℝ) *
        returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
          (fun x => psi (T * x))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)) <
      (gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
        threshold ^ r) ^ (2 : ℕ) := by
    exact (mul_le_mul_of_nonneg_right hrankReal hactionNonneg).trans_lt
      (by simpa [S] using haction)
  simpa [target, S] using
    (no_second_capture_of_returnExcised_gaussianCarrierAction_lt
      D psi target r S hmem htarget hspeed hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity hmeas hcoord hsmall)

end RHTower
