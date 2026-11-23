import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.AngularMetric
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.BinaryPhases

/-! # Eight two-valued rotations for each physical eigenphase -/
open Finset Set
namespace GaloisForLFunctions.HTGeometry.SpectralDigits
open ClockSpectrum SpectralSorting
noncomputable section

/-- The last bin includes one complete turn. -/
def angleBin (x : ℝ) : Fin (2^8) :=
  ⟨min ⌊256*x⌋₊ 255,lt_of_le_of_lt (min_le_right ..) (by decide)⟩

/-- The j-th digit contributes either the identity or a fixed rotation. -/
def digitTurn (j : Fin 8) (x : ℝ) : ℝ :=
  (2:ℝ)^j.val*(((binaryIndex 8).symm (angleBin x) j).toNat:ℝ)/256

theorem digit_values (j : Fin 8) (x : ℝ) : expTurns (digitTurn j x)=1 ∨
    expTurns (digitTurn j x)=expTurns ((2:ℝ)^j.val/256) := by
  cases h : (binaryIndex 8).symm (angleBin x) j <;> simp [digitTurn,h,expTurns]

private theorem sum_turns (x : ℝ) : ∑ j : Fin 8, digitTurn j x = ((angleBin x).val:ℝ)/256 := by
  let b := (binaryIndex 8).symm (angleBin x)
  have he : Nat.ofBits b=(angleBin x).val := congrArg Fin.val ((binaryIndex 8).apply_symm_apply _)
  rw [binary_sum] at he
  simp only [digitTurn,←Finset.sum_div]
  congr 1
  exact_mod_cast he

private theorem exp_product (s : Finset (Fin 8)) (x : ℝ) :
    ∏ j∈s, expTurns (digitTurn j x) = expTurns (∑ j∈s, digitTurn j x) := by
  simp only [expTurns,Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_mul,
    Complex.exp_sum]

/-- A common half-bin phase leaves at most half a bin of angular error
after the eight digit rotations have been multiplied. -/
theorem phase_error {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ‖expTurns x-expTurns (1/512)*(∏ j : Fin 8, expTurns (digitTurn j x))‖ ≤ Real.pi/256 := by
  have hnon : 0 ≤ 256*x := by linarith only [hx.1]
  have hlo : ((angleBin x).val:ℝ) ≤ 256*x :=
    (Nat.cast_le.mpr (min_le_left ..)).trans (Nat.floor_le hnon)
  have hhi : 256*x ≤ ((angleBin x).val:ℝ)+1 := by
    by_cases h : ⌊256*x⌋₊ ≤ 255
    · simpa only [angleBin,min_eq_left h] using (Nat.lt_floor_add_one (256*x)).le
    · rw [angleBin,min_eq_right (le_of_not_ge h)]
      push_cast
      linarith only [hx.2]
  rw [exp_product,sum_turns]
  let y := ((angleBin x).val:ℝ)/256+1/512
  have he : expTurns (1/512)*expTurns (((angleBin x).val:ℝ)/256)=expTurns y := by
    unfold expTurns
    rw [←Complex.exp_add]
    congr 1
    dsimp only [y]
    push_cast
    ring
  rw [he]
  have hd : |x-y| ≤ 1/512 := abs_le.mpr (by dsimp only [y]; constructor <;> linarith only [hlo,hhi])
  exact (expTurns_lip x y).trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))

#print axioms phase_error
end
end GaloisForLFunctions.HTGeometry.SpectralDigits
