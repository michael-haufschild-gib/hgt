/-
# Burnol conductor reflection for the exact Sonin resolvent

The real-place conductor `H = M + J M J` commutes with the scattering
reflection `J`.  If the position channel `M` commutes with a cutoff `A`, then
its commutator with the reflected cutoff `J A J` is exactly the reflection of
the bounded conductor edge `[H,A]`.  The final theorem inserts this cancellation
into the existing two-projection resolvent formula.

This is the bounded algebraic layer of the Burnol conductor argument.  It does
not construct the unbounded position/conductor multipliers or prove the BMO
boundedness of their analytic commutator.
-/
import GaloisForLFunctions.RHTower.CCM.CCMSoninResolventCommutator

noncomputable section

namespace RHTower

variable {R : Type*} [Ring R]

/-- Algebraic Burnol conductor associated with a position channel and a reflection. -/
def burnolConductor (M J : R) : R :=
  M + J * M * J

/-- Reflection of a cutoff by an involution. -/
def reflectedCutoff (A J : R) : R :=
  J * A * J

/-- The Burnol conductor is invariant under the defining involution. -/
theorem ccmCommutator_burnolConductor_reflection
    (M J : R) (hJ : J * J = 1) :
    ccmCommutator (burnolConductor M J) J = 0 := by
  rw [ccmCommutator, burnolConductor]
  rw [show (M + J * M * J) * J = M * J + J * M by
    calc
      (M + J * M * J) * J = M * J + J * M * (J * J) := by noncomm_ring
      _ = M * J + J * M := by rw [hJ, mul_one]]
  rw [show J * (M + J * M * J) = J * M + M * J by
    calc
      J * (M + J * M * J) = J * M + (J * J) * M * J := by noncomm_ring
      _ = J * M + M * J := by rw [hJ, one_mul]]
  noncomm_ring

/-- Reflecting the cutoff turns the position commutator into the conductor commutator. -/
theorem ccmCommutator_reflectedCutoff_eq_conductor
    (M J A : R) (hJ : J * J = 1)
    (hMA : ccmCommutator M A = 0) :
    ccmCommutator M (reflectedCutoff A J) =
      ccmCommutator (burnolConductor M J) (reflectedCutoff A J) := by
  have hMA' : M * A = A * M := by
    simpa [ccmCommutator, sub_eq_zero] using hMA
  have hleft : (J * M * J) * (J * A * J) = J * (M * A) * J := by
    calc
      (J * M * J) * (J * A * J) = J * M * (J * J) * A * J := by noncomm_ring
      _ = J * M * A * J := by rw [hJ, mul_one]
      _ = J * (M * A) * J := by noncomm_ring
  have hright : (J * A * J) * (J * M * J) = J * (A * M) * J := by
    calc
      (J * A * J) * (J * M * J) = J * A * (J * J) * M * J := by noncomm_ring
      _ = J * A * M * J := by rw [hJ, mul_one]
      _ = J * (A * M) * J := by noncomm_ring
  have hzero : ccmCommutator (J * M * J) (reflectedCutoff A J) = 0 := by
    rw [ccmCommutator, reflectedCutoff, hleft, hright, hMA', sub_self]
  calc
    ccmCommutator M (reflectedCutoff A J) =
        ccmCommutator M (reflectedCutoff A J) + 0 := by rw [add_zero]
    _ = ccmCommutator M (reflectedCutoff A J) +
        ccmCommutator (J * M * J) (reflectedCutoff A J) := by rw [hzero]
    _ = ccmCommutator (burnolConductor M J) (reflectedCutoff A J) := by
      simp [ccmCommutator, burnolConductor]
      noncomm_ring

/-- Conductor reflection transports its cutoff commutator across the involution. -/
theorem ccmCommutator_burnolConductor_reflectedCutoff
    (M J A : R) (hJ : J * J = 1) :
    ccmCommutator (burnolConductor M J) (reflectedCutoff A J) =
      J * ccmCommutator (burnolConductor M J) A * J := by
  have hcomm := ccmCommutator_burnolConductor_reflection M J hJ
  have hHJ : burnolConductor M J * J = J * burnolConductor M J := by
    simpa [ccmCommutator, sub_eq_zero] using hcomm
  have hleft : burnolConductor M J * reflectedCutoff A J =
      J * burnolConductor M J * A * J := by
    calc
      burnolConductor M J * reflectedCutoff A J =
          (burnolConductor M J * J) * A * J := by
            simp [reflectedCutoff]
            noncomm_ring
      _ = (J * burnolConductor M J) * A * J := by rw [hHJ]
  have hright : reflectedCutoff A J * burnolConductor M J =
      J * A * burnolConductor M J * J := by
    calc
      reflectedCutoff A J * burnolConductor M J =
          J * A * (J * burnolConductor M J) := by
            simp [reflectedCutoff]
            noncomm_ring
      _ = J * A * (burnolConductor M J * J) := by rw [hHJ]
      _ = J * A * burnolConductor M J * J := by noncomm_ring
  rw [ccmCommutator, ccmCommutator, hleft, hright]
  noncomm_ring

/-- Burnol's cancellation identity: the reflected position edge is the reflected conductor
edge, provided position commutes with the unreflected cutoff. -/
theorem ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge
    (M J A : R) (hJ : J * J = 1)
    (hMA : ccmCommutator M A = 0) :
    ccmCommutator M (reflectedCutoff A J) =
      J * ccmCommutator (burnolConductor M J) A * J := by
  rw [ccmCommutator_reflectedCutoff_eq_conductor M J A hJ hMA,
    ccmCommutator_burnolConductor_reflectedCutoff M J A hJ]

/-- Exact two-projection resolvent dressing after Burnol reflection has cancelled the naked
position terms. -/
theorem ccmCommutator_burnol_dressed_two_projection
    (M J A V : R) (hJ : J * J = 1)
    (hMA : ccmCommutator M A = 0)
    (hL : V * (1 - reflectedCutoff A J * A * reflectedCutoff A J) = 1)
    (hR : (1 - reflectedCutoff A J * A * reflectedCutoff A J) * V = 1) :
    let E := 1 - A
    let B := reflectedCutoff A J
    let Q := E - E * V * B * E
    ccmCommutator M Q =
      -E * V *
        ((J * ccmCommutator (burnolConductor M J) A * J) * A * B * V * B +
          B * A * (J * ccmCommutator (burnolConductor M J) A * J) * V * B +
          J * ccmCommutator (burnolConductor M J) A * J) * E := by
  dsimp
  rw [ccmCommutator_dressed_two_projection M A (reflectedCutoff A J) V hMA hL hR]
  rw [ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge M J A hJ hMA]

end RHTower
