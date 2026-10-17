import GaloisForLFunctions.BiScaleUncertainty.FiniteGridTraceStability
import GaloisForLFunctions.BiScaleUncertainty.FinitePathSinePackets

/-!
# Attained sharp finite-grid Dirichlet constants

A longest arithmetic run supports a finite sine packet. Its positive mode and
alternating mode are actual union data and attain both stability constants.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def finiteGridRunStart (d : ℕ) (D : Finset ℕ) : ℕ :=
  Classical.choose (finiteGridRunLength_attained_in_period d D)

theorem finiteGridRunStart_lt_period (d : ℕ) (D : Finset ℕ) :
    finiteGridRunStart d D < finiteGridPeriod d D :=
  (Classical.choose_spec (finiteGridRunLength_attained_in_period d D)).1

theorem finiteGridRunStart_active (d : ℕ) (D : Finset ℕ) (j : ℕ)
    (hj : j < finiteGridRunLength d D) :
    finiteGridActive d D (finiteGridRunStart d D + j) :=
  (Classical.choose_spec (finiteGridRunLength_attained_in_period d D)).2 j hj

def finiteGridRunData (d : ℕ) (D : Finset ℕ) (x : ℕ → ℝ) : FiniteGridData d D :=
  ⟨intervalTraceData (finiteGridRunStart d D) (finiteGridRunLength d D) x, by
    apply (mem_finiteGridDataSpace_iff d D _).mpr
    intro k hk
    apply intervalTraceData_off
    intro j hj hkj
    apply hk
    rw [hkj]
    exact finiteGridRunStart_active d D j hj⟩

def finiteGridLowerPacket (d : ℕ) (D : Finset ℕ) : FiniteGridData d D :=
  finiteGridRunData d D (pathSineValue (finiteGridRunLength d D))

def finiteGridUpperPacket (d : ℕ) (D : Finset ℕ) : FiniteGridData d D :=
  finiteGridRunData d D (alternatingPathSineValue (finiteGridRunLength d D))

theorem finiteGridLowerPacket_ne_zero (d : ℕ) (D : Finset ℕ) :
    finiteGridLowerPacket d D ≠ 0 := by
  intro h
  have he := congrArg (fun v : FiniteGridData d D => v.1 (finiteGridRunStart d D)) h
  have hv : (finiteGridLowerPacket d D).1 (finiteGridRunStart d D) =
      pathSineValue (finiteGridRunLength d D) 0 := by
    change intervalTraceData _ _ _ _ = _
    simpa only [Nat.add_zero, if_pos (finiteGridRunLength_pos d D)] using
      intervalTraceData_at (finiteGridRunStart d D) (finiteGridRunLength d D) 0
        (pathSineValue (finiteGridRunLength d D))
  rw [hv] at he
  have hp := pathSineValue_first_pos _ (finiteGridRunLength_pos d D)
  exact (ne_of_gt hp) he

theorem finiteGridPackets_norm_sq (d : ℕ) (D : Finset ℕ) :
    ‖finiteGridUpperPacket d D‖^2 = ‖finiteGridLowerPacket d D‖^2 := by
  change ‖intervalTraceData _ _ (alternatingPathSineValue _)‖^2 =
    ‖intervalTraceData _ _ (pathSineValue _)‖^2
  simp only [intervalTraceData_norm_sq, alternatingPathSineValue_sq]

theorem finiteGridUpperPacket_ne_zero (d : ℕ) (D : Finset ℕ) :
    finiteGridUpperPacket d D ≠ 0 := by
  intro h
  have he := finiteGridPackets_norm_sq d D
  rw [h, norm_zero, zero_pow (by omega : 2 ≠ 0)] at he
  have hz : finiteGridLowerPacket d D = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  exact finiteGridLowerPacket_ne_zero d D hz

theorem finiteGridLowerPacket_energy (d : ℕ) (D : Finset ℕ) :
    ‖finiteGridExtension d D (finiteGridLowerPacket d D)‖^2 =
      (2 - 2 * finiteGridSineFactor d D) * ‖finiteGridLowerPacket d D‖^2 := by
  rw [finiteGridExtension_energy]
  change 2 * ‖intervalTraceData _ _ (pathSineValue _)‖^2 -
      2 * (∑' k, intervalTraceData _ _ (pathSineValue _) k *
        intervalTraceData _ _ (pathSineValue _) (k+1)) =
    (2 - 2 * finiteGridSineFactor d D) * ‖intervalTraceData _ _ (pathSineValue _)‖^2
  rw [intervalTraceData_adjacent _ _ _ (pathSineValue_end _),
    pathSineValue_adjacent, intervalTraceData_norm_sq]
  unfold finiteGridSineFactor
  ring

theorem finiteGridUpperPacket_energy (d : ℕ) (D : Finset ℕ) :
    ‖finiteGridExtension d D (finiteGridUpperPacket d D)‖^2 =
      (2 + 2 * finiteGridSineFactor d D) * ‖finiteGridUpperPacket d D‖^2 := by
  rw [finiteGridExtension_energy]
  change 2 * ‖intervalTraceData _ _ (alternatingPathSineValue _)‖^2 -
      2 * (∑' k, intervalTraceData _ _ (alternatingPathSineValue _) k *
        intervalTraceData _ _ (alternatingPathSineValue _) (k+1)) =
    (2 + 2 * finiteGridSineFactor d D) *
      ‖intervalTraceData _ _ (alternatingPathSineValue _)‖^2
  rw [intervalTraceData_adjacent _ _ _ (alternatingPathSineValue_end _),
    alternatingPathSineValue_adjacent, intervalTraceData_norm_sq]
  simp only [alternatingPathSineValue_sq]
  unfold finiteGridSineFactor
  ring

/-- Both factors are attained by nonzero concrete finite sine packets. -/
theorem finiteGridExtension_sharp (d : ℕ) (D : Finset ℕ) :
    ∃ lower upper : FiniteGridData d D, 0 < ‖lower‖^2 ∧ 0 < ‖upper‖^2 ∧
      ‖finiteGridExtension d D lower‖^2 =
        (2 - 2 * finiteGridSineFactor d D) * ‖lower‖^2 ∧
      ‖finiteGridExtension d D upper‖^2 =
        (2 + 2 * finiteGridSineFactor d D) * ‖upper‖^2 := by
  refine ⟨finiteGridLowerPacket d D, finiteGridUpperPacket d D, ?_, ?_,
    finiteGridLowerPacket_energy d D, finiteGridUpperPacket_energy d D⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr (finiteGridLowerPacket_ne_zero d D))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (finiteGridUpperPacket_ne_zero d D))

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
