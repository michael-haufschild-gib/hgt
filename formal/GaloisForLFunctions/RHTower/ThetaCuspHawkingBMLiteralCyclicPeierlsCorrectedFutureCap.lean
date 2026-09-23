import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCorrectedFutureFixedArmDecomposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapDefect

/-!
# Literal corrected-future cyclic Peierls cap

The corrected future field contains three mathematically distinct pieces.  The
first is the forced physical bulk contact
`parameter * timeLiftField - timeAngularSeedField`; it is neither a cutoff nor
a freely chosen counterterm.  After removing exactly that contact, the field is
the admitted original future pulse plus the literal combined cap
`seedCapField - parameter * capBoundaryField`.

Proof-chain role:
`literal bulk contact + corrected future -> pulse + combined cap -> cap normal
trace -> native-circle/QNM transport -> HB B2 decision`.

This is deliberately an exact finite-field identity.  It does not assert a
noncompact limit or suppress the pulse; those are the remaining analytic
obligations for the actual left-QNM pairing.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCorrectedFutureCap

open D4BMJointSource D4BMModularCore D4BMFuturePulseAdmission D4BMGlobalAngularResponse
open D4BMFutureSeedHorizon D4BMFutureHorizon
open D4BMCompleteOriginalWeakSource D4BMCorrectedFutureFixedArmDecomposition

noncomputable section
set_option autoImplicit false

/-- The prescribed physical bulk contact in the corrected-future field.  Its
two angular vertices are the literal full and square fields. -/
def cyclicBulkContact (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau t X k : ℝ) : ℂ :=
  parameter q branch * timeLiftField q branch amp tau t ![X, Real.exp k] -
    timeAngularSeedField q branch amp tau t ![X, Real.exp k]

/-- Literal full-minus-square vertex carried by the forced bulk contact. -/
def cyclicPeierlsBulkVertex (q : XiZeroCopy) (branch : Bool) (X k : ℝ) : ℂ :=
  fullAngularField q branch ![X, Real.exp k] -
    physicalRate q branch * (physicalRate q branch - 1) / 4 *
      fullSquarePotential q ![X, Real.exp k]

/-- The forced bulk contact factors through the actual source amplitude and
onset.  No radial endpoint has been taken in this identity. -/
theorem cyclicBulkContact_factor (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau t X k : ℝ) :
    cyclicBulkContact q branch amp tau t X k =
      sourceAmplitude (physicalRate q branch) 0 amp 1 t *
        timeOnset (2 * physicalRate q branch) (tau + t) *
        (parameter q branch * (-(physicalRate q branch *
          (physicalRate q branch - 1) / 4)) * (radialUnit t : ℂ) ^ 3 *
            fullSquarePotential q ![X, Real.exp k] -
          sourceSeedPolynomial (physicalRate q branch) (parameter q branch)
            (radialUnit t) * fullAngularField q branch ![X, Real.exp k]) := by
  unfold cyclicBulkContact timeLiftField timeAngularSeedField timeRadialLift
    timeSourceSeed radialLift sourceSeedField
  ring

/-- At the literal compact horizon vertex `u = 1`, the bulk contact is exactly
the physical cyclic Peierls full-minus-square vertex. -/
theorem cyclicBulkContact_horizon_vertex (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    parameter q branch * (-(physicalRate q branch *
      (physicalRate q branch - 1) / 4)) * (1 : ℂ) ^ 3 *
        fullSquarePotential q ![X, Real.exp k] -
      sourceSeedPolynomial (physicalRate q branch) (parameter q branch) 1 *
        fullAngularField q branch ![X, Real.exp k] =
      parameter q branch * cyclicPeierlsBulkVertex q branch X k := by
  unfold sourceSeedPolynomial cyclicPeierlsBulkVertex
  rw [parameter_physicalRate q branch]
  simp only [D4BMQuadraticMixedSource.resolventParameter]
  ring

/-- Corrected future after removing only its forced physical bulk contact. -/
def correctedFutureCapResidual (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau t X k : ℝ) : ℂ :=
  parameter q branch * correctedFutureField q branch amp ((tau, t), X + Complex.I * k) -
    cyclicBulkContact q branch amp tau t X k

/-- Exact corrected-future realization of the literal combined cap.  The pulse
remains displayed rather than being assumed negligible or absorbed. -/
theorem correctedFutureCapResidual_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau : ℝ) (depth : NNReal) (X k : ℝ) :
    correctedFutureCapResidual q branch amp tau (-(depth : ℝ)) X k =
      response q branch amp tau (-(depth : ℝ)) X k +
        (seedCapField q branch amp tau (-(depth : ℝ)) X k -
          parameter q branch * capBoundaryField q branch amp tau (-(depth : ℝ)) X k) := by
  rw [correctedFutureCapResidual, cyclicBulkContact,
    correctedFutureField_pulse_cap_decomposition]
  ring

/-- The same identity on the literal ingoing cap trajectory.  `v` is original
time and `x` is tortoise radius; their distinction is retained. -/
theorem correctedFutureCapResidual_ingoing_eq (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x X k : ℝ) (hx : x ≤ 0) :
    correctedFutureCapResidual q branch amp (v - x) x X k =
      response q branch amp (v - x) x X k +
        (seedCapField q branch amp (v - x) x X k -
          parameter q branch * capBoundaryField q branch amp (v - x) x X k) := by
  let depth : NNReal := ⟨-x, neg_nonneg.mpr hx⟩
  have h := correctedFutureCapResidual_eq q branch amp (v - x) depth X k
  have hcoe : -(depth : ℝ) = x := by
    show -(-x) = x
    ring
  rw [hcoe] at h
  exact h

end

end RHTower.D4BMLiteralCyclicPeierlsCorrectedFutureCap
