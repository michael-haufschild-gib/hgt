import GaloisForLFunctions.HTGeometry.CoherenceFlatness
import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy

/-!
# Boolean clock-holonomy universality

Boolean XOR coherence is exactly the order-two sector of group-valued clock calibration. Encoding
`Bool` in the multiplicative form of `ZMod 2` identifies open-walk XOR with clock transport,
Boolean symmetry with reversibility, Boolean flatness with clock flatness, and the reconstructed
Boolean vertex orientation with a global clock potential.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Boolean parity as the multiplicative form of the order-two additive clock. -/
def booleanClockValue (b : Bool) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd ((b.toNat : ℕ) : ZMod 2)

@[simp] theorem booleanClockValue_false : booleanClockValue false = 1 := by
  rfl

theorem booleanClockValue_xor (a b : Bool) :
    booleanClockValue (Bool.xor a b) =
      booleanClockValue a * booleanClockValue b := by
  cases a with
  | false =>
      cases b <;> rfl
  | true =>
      cases b with
      | false => rfl
      | true =>
          change Multiplicative.ofAdd (0 : ZMod 2) =
            Multiplicative.ofAdd (1 : ZMod 2) *
              Multiplicative.ofAdd (1 : ZMod 2)
          rw [← ofAdd_add]
          congr 1

theorem booleanClockValue_eq_one_iff (b : Bool) :
    booleanClockValue b = 1 ↔ b = false := by
  cases b <;> norm_num [booleanClockValue]

theorem booleanClockValue_inv (b : Bool) :
    (booleanClockValue b)⁻¹ = booleanClockValue b := by
  cases b
  · rfl
  · simp only [booleanClockValue]
    rw [← ofAdd_neg]
    congr 1

/-- Boolean edge labels viewed as an order-two multiplicative clock calibration. -/
def booleanClockCalibration {V : Type*} (c : V → V → Bool) :
    V → V → Multiplicative (ZMod 2) :=
  fun u v => booleanClockValue (c u v)

/-- Order-two clock transport is exactly encoded XOR holonomy on every open walk. -/
theorem clockWalkTransport_booleanClockCalibration
    {V : Type*} {G : SimpleGraph V} (c : V → V → Bool)
    {u v : V} (p : G.Walk u v) :
    clockWalkTransport (booleanClockCalibration c) p =
      booleanClockValue (walkXor c p) := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      rw [clockWalkTransport_cons, walkXor_cons, ih,
        booleanClockValue_xor]
      rfl

/-- Symmetric Boolean edge fields give reversible order-two clock calibrations. -/
theorem booleanClockCalibration_reversible
    {V : Type*} {G : SimpleGraph V} (c : V → V → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c) :
    ClockCalibrationReversible G (booleanClockCalibration c) := by
  intro u v huv
  rw [booleanClockCalibration, booleanClockCalibration, hsymm huv,
    booleanClockValue_inv]

/-- Boolean XOR flatness is exactly group-valued flatness of its order-two clock encoding. -/
theorem booleanEdgeFieldFlat_iff_clockCalibrationFlat
    {V : Type*} {G : SimpleGraph V} (c : V → V → Bool) :
    BooleanEdgeFieldFlat G c ↔
      ClockCalibrationFlat G (booleanClockCalibration c) := by
  constructor
  · intro hflat u p
    rw [clockWalkTransport_booleanClockCalibration, hflat u p]
    exact booleanClockValue_false
  · intro hflat u p
    have h := hflat u p
    rw [clockWalkTransport_booleanClockCalibration,
      booleanClockValue_eq_one_iff] at h
    exact h

/-- On a connected graph, Boolean flatness is exactly global order-two clock integrability. -/
theorem clockCalibrationExact_booleanClockCalibration_iff_flat
    {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (c : V → V → Bool) (hsymm : BooleanEdgeFieldSymmetric G c) :
    ClockCalibrationExact G (booleanClockCalibration c) ↔
      BooleanEdgeFieldFlat G c := by
  rw [clockCalibrationExact_iff_flat hG (booleanClockCalibration c)
    (booleanClockCalibration_reversible c hsymm)]
  exact (booleanEdgeFieldFlat_iff_clockCalibrationFlat c).symm

/-- Boolean vertex orientation and global order-two clock potential are the same exactness law. -/
theorem exists_booleanOrientation_iff_clockCalibrationExact
    {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (c : V → V → Bool) (hsymm : BooleanEdgeFieldSymmetric G c) :
    (∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
      c u v = Bool.xor (ε u) (ε v)) ↔
      ClockCalibrationExact G (booleanClockCalibration c) := by
  exact (booleanEdgeField_coboundary_iff_flat hG c hsymm).trans
    (clockCalibrationExact_booleanClockCalibration_iff_flat hG c hsymm).symm

end

end GaloisForLFunctions.HTGeometry
