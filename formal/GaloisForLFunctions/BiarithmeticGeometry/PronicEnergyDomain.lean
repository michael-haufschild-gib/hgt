import GaloisForLFunctions.BiarithmeticGeometry.CofactorPaymentCriterion
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite receiver bounds and total pronic energy

The positive pronic cells identify uniform finite-horizon norm bounds with
square summability. Real and imaginary parts give the corresponding complex
domain without any growth assumption on the row.
-/

noncomputable section
open Finset
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The energy of the positive cell indexed by `n`. -/
def pronicCellEnergy (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- Reindexing positive cells gives exactly the receiver's finite norm. -/
theorem sum_pronicCellEnergy_eq_norm_sq (f : ℕ → ℝ) (T : ℕ) :
    (∑ n ∈ range T, pronicCellEnergy f n) = pronicNorm f T ^ 2 := by
  have he : (∑ n ∈ range T, pronicCellEnergy f n) =
      ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
      simp only [pronicCellEnergy, Nat.cast_add, Nat.cast_one]
      rw [show (T : ℝ) + 1 + 1 = (T : ℝ) + 2 by ring]
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  exact he

/-- Uniform finite-horizon bounds are equivalent to finite total pronic energy. -/
theorem bounded_pronicNorm_iff_summable (f : ℕ → ℝ) :
    (∃ C : ℝ, ∀ T : ℕ, pronicNorm f T ≤ C) ↔ Summable (pronicCellEnergy f) := by
  constructor
  · rintro ⟨C, hC⟩
    apply summable_of_sum_range_le (fun n => by unfold pronicCellEnergy; positivity)
      (c := C ^ 2)
    intro T
    rw [sum_pronicCellEnergy_eq_norm_sq]
    exact pow_le_pow_left₀ (pronicNorm_nonneg f T) (hC T) 2
  · intro h
    refine ⟨Real.sqrt (∑' n, pronicCellEnergy f n), fun T => ?_⟩
    apply Real.le_sqrt_of_sq_le
    rw [← sum_pronicCellEnergy_eq_norm_sq]
    exact sum_le_hasSum _ (fun n _ => by unfold pronicCellEnergy; positivity) h.hasSum

/-- Multiplication by a nonzero real scalar preserves the finite-energy domain. -/
theorem bounded_pronicNorm_smul_iff (a : ℝ) (ha : a ≠ 0) (f : ℕ → ℝ) :
    (∃ C : ℝ, ∀ T : ℕ, pronicNorm (fun n => a * f n) T ≤ C) ↔
      ∃ C : ℝ, ∀ T : ℕ, pronicNorm f T ≤ C := by
  have hpos : 0 < |a| := abs_pos.mpr ha
  simp only [pronicNorm_smul]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / |a|, fun T => (le_div_iff₀ hpos).mpr ?_⟩
    simpa only [mul_comm] using hC T
  · rintro ⟨C, hC⟩
    exact ⟨|a| * C, fun T => mul_le_mul_of_nonneg_left (hC T) hpos.le⟩

/-- Receiver admission is finite total energy of the actual centered prefix. -/
theorem receiverBounded_iff_summable_pronicCellEnergy (c : ℕ → ℝ) :
    ReceiverBounded c ↔
      Summable (pronicCellEnergy (weightCenteredPrefix c (∑' d : ℕ, c d / d))) := by
  rw [← bounded_pronicNorm_iff_summable]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨Real.sqrt B, fun T => Real.sqrt_le_sqrt (hB T)⟩
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun T => ?_⟩
    rw [weightPronicEnergy_eq_sq_pronicNorm]
    exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) (hC T) 2

/-- Complex finite energy is exactly finite energy of both real components. -/
theorem summable_complex_pronicEnergy_iff (z : ℕ → ℂ) :
    Summable (fun n : ℕ => ‖z (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ↔
      Summable (pronicCellEnergy (fun n => (z n).re)) ∧
        Summable (pronicCellEnergy (fun n => (z n).im)) := by
  have he (n : ℕ) : ‖z (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      pronicCellEnergy (fun n => (z n).re) n + pronicCellEnergy (fun n => (z n).im) n := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_div]
    simp only [pronicCellEnergy, pow_two]
  constructor
  · intro h
    constructor
    · refine h.of_nonneg_of_le (fun n => by unfold pronicCellEnergy; positivity) fun n => ?_
      rw [he]
      exact le_add_of_nonneg_right (by unfold pronicCellEnergy; positivity)
    · refine h.of_nonneg_of_le (fun n => by unfold pronicCellEnergy; positivity) fun n => ?_
      rw [he]
      exact le_add_of_nonneg_left (by unfold pronicCellEnergy; positivity)
  · rintro ⟨hr, hi⟩
    exact (hr.add hi).congr fun n => (he n).symm

end GaloisForLFunctions.BiarithmeticGeometry
