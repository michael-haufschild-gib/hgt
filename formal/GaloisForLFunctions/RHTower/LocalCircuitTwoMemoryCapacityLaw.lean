import GaloisForLFunctions.HTGeometry.StaticCircuitTwoMemoryOrthogonalityLaw
import GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity

/-!
# Local-circuit heap capacity forces memory realignment

The universal two-memory collision law charges one target by the inverse size of its target
dictionary.  Local circuit dictionaries contain exact duplication: adjacent disjoint-support gates
commute and therefore produce the same endpoint.  The trace-capacity law quotients that duplication
and bounds the number of length-`ell` targets by

`choose (M + ell - 1) ell * 2^(Delta * ell)`.

This file composes the two exact laws.  Any shortcut represented by a length-`ell` trace class
forces a dynamical/preparation-memory alignment at the inverse intrinsic heap-capacity scale.  At
exact recurrence the identity trace forces the same realignment with collision one.

The result performs no physical-time averaging and claims no alignment decay.  It isolates the
quenched scalar whose suppression would prove autonomous complexity growth after carrier excision.
-/

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {α F : Type*} [Fintype α] [LinearOrder α]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Uniform preparation moment over exact partially commutative trace classes. -/
noncomputable def fixedTracePreparationMoment
    (independent : α → α → Prop) (ell : ℕ)
    (target : FixedTraceClass independent ell → F) : F := by
  letI : Fintype (FixedTraceClass independent ell) := Fintype.ofFinite _
  exact finitePreparationMoment target

/-- **Heap-normalized shortcut realignment law.** A target collision `a` at exact length `ell`
forces dynamical/preparation alignment at least `a` divided by the intrinsic trace-capacity bound,
minus the completed static baseline. -/
theorem fixedTrace_target_forces_memory_realign
    (independent : α → α → Prop) (hsymm : ∀ x y, independent x y → independent y x)
    (ell Delta : ℕ) (hdegree : ∀ a, incidentEdgeCount independent a ≤ Delta)
    (PiOp P : F →L[ℝ] F) (U : F ≃ₗᵢ[ℝ] F) (x : F)
    (target : FixedTraceClass independent ell → F)
    (i0 : FixedTraceClass independent ell)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z)
    (hPiMoment : PiOp (fixedTracePreparationMoment independent ell target) = PiOp x)
    (hnonneg : ∀ i, 0 ≤ inner ℝ (U x) (target i))
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ inner ℝ (U x) (target i0)) :
    (((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) : ℝ)⁻¹ * a -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (fixedTracePreparationMoment independent ell target))) ≤
      inner ℝ (dynamicMemory P U x)
        (preparationMemory PiOp x (fixedTracePreparationMoment independent ell target)) := by
  let I := FixedTraceClass independent ell
  letI : Nonempty I := ⟨i0⟩
  letI : Fintype I := Fintype.ofFinite _
  have hraw := one_target_forces_memory_realign PiOp P U x target i0
    hPisa hPiid hPiP hPU hPiMoment hnonneg ha
  have hcardNat : Nat.card I ≤
      (Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) :=
    natCard_fixedTraceClass_le_maxDegree independent hsymm ell Delta hdegree
  have hcard : Fintype.card I ≤
      (Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  have hIposNat : 0 < Fintype.card I := Fintype.card_pos
  have hCposNat : 0 < (Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) :=
    lt_of_lt_of_le hIposNat hcard
  have hIpos : (0 : ℝ) < Fintype.card I := by exact_mod_cast hIposNat
  have hCpos : (0 : ℝ) <
      (((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) : ℝ) := by
    exact_mod_cast hCposNat
  have hcardReal : (Fintype.card I : ℝ) ≤
      ((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) := by
    exact_mod_cast hcard
  have hinv :
      (((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) : ℝ)⁻¹ ≤
        (Fintype.card I : ℝ)⁻¹ :=
    (inv_le_inv₀ hCpos hIpos).2 hcardReal
  have hmul :
      (((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) : ℝ)⁻¹ * a ≤
        (Fintype.card I : ℝ)⁻¹ * a := mul_le_mul_of_nonneg_right hinv ha0
  simpa only [fixedTracePreparationMoment] using le_trans (sub_le_sub_right hmul _) hraw

/-- **Heap-normalized recurrence realignment law.** If the normalized seed is a target and the
evolution returns exactly, the forced alignment is one inverse intrinsic trace-capacity minus the
completed baseline. -/
theorem fixedTrace_recurrence_forces_memory_realign
    (independent : α → α → Prop) (hsymm : ∀ x y, independent x y → independent y x)
    (ell Delta : ℕ) (hdegree : ∀ a, incidentEdgeCount independent a ≤ Delta)
    (PiOp P : F →L[ℝ] F) (U : F ≃ₗᵢ[ℝ] F) (x : F)
    (target : FixedTraceClass independent ell → F)
    (i0 : FixedTraceClass independent ell)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ z, P (U z) = P z)
    (hPiMoment : PiOp (fixedTracePreparationMoment independent ell target) = PiOp x)
    (hrec : U x = x) (htarget : target i0 = x) (hnorm : ‖x‖ = 1)
    (hnonneg : ∀ i, 0 ≤ inner ℝ (U x) (target i)) :
    (((Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell) : ℕ) : ℝ)⁻¹ -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (fixedTracePreparationMoment independent ell target))) ≤
      inner ℝ (dynamicMemory P U x)
        (preparationMemory PiOp x (fixedTracePreparationMoment independent ell target)) := by
  have ha : (1 : ℝ) ≤ inner ℝ (U x) (target i0) := by
    rw [hrec, htarget, real_inner_self_eq_norm_sq, hnorm]
    norm_num
  simpa only [mul_one] using fixedTrace_target_forces_memory_realign independent hsymm ell Delta
    hdegree PiOp P U x target i0 hPisa hPiid hPiP hPU hPiMoment hnonneg
    (a := 1) zero_le_one ha

end GaloisForLFunctions.RHTower
