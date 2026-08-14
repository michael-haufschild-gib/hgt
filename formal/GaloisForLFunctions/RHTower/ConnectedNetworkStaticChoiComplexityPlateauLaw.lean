import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import GaloisForLFunctions.HTGeometry.ConnectedNetworkRecurrenceLaw

/-!
# Static Choi complexity plateau for connected interaction networks

This file closes the composition between arbitrary-graph spectral genericity
and the projective static Choi target-capacity theorem.  For every connected
finite onsite-plus-edge interaction network with local dimensions at least
two, one dense residual full-measure coefficient set simultaneously supplies
maximal projective spectrum and the completed-time padded-circuit occupation
bound.  The spectral enumeration is arbitrary and therefore carries no
eigenbasis hypothesis.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A connected-network spectrum relabelled by an arbitrary finite
enumeration suitable for the projective Choi phase law. -/
def connectedNetworkChoiEnergy
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : Fin (interactionCoordinateCount A G) → ℝ) {d : ℕ}
    (e : Fin (d + 1) ≃ LocalConfiguration A (Finset.univ : Finset V)) :
    Fin (d + 1) → ℝ :=
  fun i => (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues (e i)

/-- Generic connected-network maximal projective rank survives every
enumeration of the physical basis. -/
theorem maximallyProjective_connectedNetworkChoiEnergy
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ allSubsystemGenericSet A G) {d : ℕ}
    (e : Fin (d + 1) ≃ LocalConfiguration A (Finset.univ : Finset V)) :
    MaximallyProjectiveEnergy (connectedNetworkChoiEnergy A G p e) :=
  MaximallyProjectiveEnergy.comp_equiv
    (maximallyProjective_subsystemBlock_univ_of_connected
      A G hG (hp Finset.univ)) e

/-- **Generic static-local completed-time Choi plateau.**  The coefficient
set is dense, residual and full Lebesgue measure; every Hamiltonian in it
obeys the exact completed-time circuit-target occupation bound.  No
spectral, randomness, mixing or eigenbasis premise remains outside the
statement. -/
theorem connectedNetwork_completedTime_paddedCircuitTargets_generic
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.Connected) (h2 : ∀ v, 2 ≤ Fintype.card (A v))
    {d : ℕ}
    (e : Fin (d + 1) ≃ LocalConfiguration A (Finset.univ : Finset V))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    (Dense (allSubsystemGenericSet A G) ∧
        allSubsystemGenericSet A G ∈
          residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
        volume (allSubsystemGenericSet A G)ᶜ = 0) ∧
      ∀ p ∈ allSubsystemGenericSet A G,
        let targetSet := zeroAnchoredPaddedCircuitTarget d s target δ
        atTop.limsup (fun T ↦
            (finiteTorusPhaseProbabilityMeasure
              (zeroProjectiveFrequency
                (connectedNetworkChoiEnergy A G p e)) T :
              Measure (UnitAddTorus (Fin d))) targetSet) ≤
              volume targetSet ∧
          volume.real targetSet ≤
            (Fintype.card gate : ℝ) ^ (s + 1) *
              (((d + 1 : ℕ) : ℝ) *
                Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
                Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
                  ((d + 1 : ℕ) - 1)) := by
  constructor
  · exact allSubsystemGenericSet_dense_residual_fullMeasure A G h2
  · intro p hp
    exact completedTime_zeroAnchoredPaddedCircuitTargets
      (connectedNetworkChoiEnergy A G p e)
      (maximallyProjective_connectedNetworkChoiEnergy A G hG hp e)
      s target hδ

end RHTower
