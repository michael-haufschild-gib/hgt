import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells
import GaloisForLFunctions.RHTower.SteinhausPhaseRotation

/-!
# Translation-invariant mass of finite-character cells

Arbitrary coordinatewise real phase translations have measure-preserving representatives on
the product unit cube. The representative differs from the raw translation by integer phases,
which every multiplicative character ignores. Common phase translation multiplies each
character difference by a unit complex number, so every fixed finite-character cell has exactly
the same measure at every translated centre.

This handles common-height rotations without assuming the raw real translation preserves the
unit-interval measure.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Complex
namespace RHTower
open SteinhausModel

/-- A coordinatewise unit-interval representative of an arbitrary real phase translation. -/
def steinhausCoordinateRotation (a omega : Omega) : Omega := fun p =>
  if Int.fract (a p) = 0 then omega p
  else GaloisForLFunctions.RHTower.rotBy (Int.fract (a p)) (omega p)

theorem measurable_steinhausCoordinateRotation (a : Omega) :
    Measurable (steinhausCoordinateRotation a) := by
  apply measurable_pi_lambda
  intro p
  by_cases h : Int.fract (a p) = 0
  · simpa only [steinhausCoordinateRotation, h, if_true] using measurable_pi_apply p
  · simpa only [steinhausCoordinateRotation, h, if_false, Function.comp_def] using
      (GaloisForLFunctions.RHTower.measurable_rotBy (Int.fract (a p))).comp (measurable_pi_apply p)

theorem map_steinhausCoordinateRotation (a : Omega) :
    Measure.map (steinhausCoordinateRotation a) steinhausMeasure = steinhausMeasure := by
  let f : ℕ → ℝ → ℝ := fun p => if Int.fract (a p) = 0 then id
    else GaloisForLFunctions.RHTower.rotBy (Int.fract (a p))
  have hf : ∀ p, Measurable (f p) := by
    intro p
    dsimp only [f]
    split_ifs
    · exact measurable_id
    · exact GaloisForLFunctions.RHTower.measurable_rotBy _
  have heq : steinhausCoordinateRotation a = fun omega p => f p (omega p) := by
    ext omega p
    dsimp only [steinhausCoordinateRotation, f]
    split_ifs <;> rfl
  rw [heq, steinhausMeasure, Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (f := f) hf]
  congr 1
  funext p
  dsimp only [f]
  split_ifs with h
  · exact Measure.map_id
  · exact GaloisForLFunctions.RHTower.map_rotBy
      (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h)) (Int.fract_lt_one _)

private theorem coordinateRotation_eq_add_integer (a omega : Omega) (p : ℕ) :
    ∃ k : ℤ, steinhausCoordinateRotation a omega p = omega p + a p + k := by
  by_cases h0 : Int.fract (a p) = 0
  · refine ⟨-⌊a p⌋, ?_⟩
    simp only [steinhausCoordinateRotation, h0, if_true, Int.cast_neg]
    rw [Int.fract] at h0
    linarith
  · by_cases h : omega p ≤ 1 - Int.fract (a p)
    · refine ⟨-⌊a p⌋, ?_⟩
      change (if Int.fract (a p) = 0 then omega p else
        GaloisForLFunctions.RHTower.rotBy (Int.fract (a p)) (omega p)) = _
      rw [if_neg h0, GaloisForLFunctions.RHTower.rotBy, if_pos h, Int.fract]
      push_cast
      ring
    · refine ⟨-⌊a p⌋ - 1, ?_⟩
      change (if Int.fract (a p) = 0 then omega p else
        GaloisForLFunctions.RHTower.rotBy (Int.fract (a p)) (omega p)) = _
      rw [if_neg h0, GaloisForLFunctions.RHTower.rotBy, if_neg h, Int.fract]
      push_cast
      ring

theorem steinhausCharacter_coordinateRotation (n : ℕ) (a omega : Omega) :
    X n (steinhausCoordinateRotation a omega) = X n (fun p => omega p + a p) := by
  choose k hk using coordinateRotation_eq_add_integer a omega
  rw [show steinhausCoordinateRotation a omega = (fun p => (omega p + a p) + k p) from funext hk]
  exact steinhausCharacter_add_integer n _ k

theorem steinhausCharacter_add_phase (n : ℕ) (omega a : Omega) :
    X n (fun p => omega p + a p) = X n omega * X n a := by
  unfold X
  rw [← Complex.exp_add]
  congr 1
  simp_rw [mul_add, Finset.sum_add_distrib]
  push_cast
  ring

/-- Finite-character distances are unchanged by a common coordinatewise phase translation. -/
theorem norm_steinhausCharacter_sub_add_phase (n : ℕ) (omega eta a : Omega) :
    ‖X n (fun p => eta p + a p) - X n (fun p => omega p + a p)‖ =
      ‖X n eta - X n omega‖ := by
  rw [steinhausCharacter_add_phase, steinhausCharacter_add_phase, ← sub_mul,
    norm_mul, norm_X, mul_one]

/-- A fixed finite-character cell has exactly the same mass at every translated centre. -/
theorem steinhausMeasure_characterCell_add_phase (B : ℕ) (omega a : Omega) (ε : ℝ) :
    steinhausMeasure (steinhausCharacterCell B (fun p => omega p + a p) ε) =
      steinhausMeasure (steinhausCharacterCell B omega ε) := by
  have hpre : steinhausCoordinateRotation a ⁻¹'
      steinhausCharacterCell B (fun p => omega p + a p) ε =
      steinhausCharacterCell B omega ε := by
    ext eta
    simp only [Set.mem_preimage, steinhausCharacterCell, Set.mem_setOf_eq,
      steinhausCharacter_coordinateRotation, norm_steinhausCharacter_sub_add_phase]
  calc
    _ = (Measure.map (steinhausCoordinateRotation a) steinhausMeasure)
        (steinhausCharacterCell B (fun p => omega p + a p) ε) := by
      rw [map_steinhausCoordinateRotation]
    _ = steinhausMeasure (steinhausCoordinateRotation a ⁻¹'
        steinhausCharacterCell B (fun p => omega p + a p) ε) :=
      Measure.map_apply (measurable_steinhausCoordinateRotation a)
        (isOpen_steinhausCharacterCell B _ ε).measurableSet
    _ = _ := by rw [hpre]

end RHTower
