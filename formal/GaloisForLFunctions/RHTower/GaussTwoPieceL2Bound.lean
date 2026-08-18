import GaloisForLFunctions.RHTower.GaussClassStep
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation

/-!
# The `L²` norm of a two-piece amplitude

A two-piece amplitude with bulk exponent above `1/2` and spike exponent above `1/2` is square
summable, with total mass `2A²Z(2θ) + 2B²I^{2c}Z(2c)` where `Z(s) = ∑_j (1+|j|)^{-s}`.  The spike
contributes `I^{2c}` because it is a band of `I` frequencies at height `B`, and the tie
`B = B₀/(1+I)^θ` converts that into `I^{2c-2θ}`.

Through Parseval this bounds the `L²` norm of a circle function by its class data.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

/-! ## The integer power total -/

theorem summable_one_div_one_add_natAbs_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun j : ℤ => 1 / (1 + (j.natAbs : ℝ)) ^ s) := by
  refine (summable_one_div_one_add_abs_rpow hs).congr fun j => ?_
  congr 2
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

/-- `Z(s) = ∑_j (1+|j|)^(-s)`, the total integer power weight. -/
def intNatAbsPowTotal (s : ℝ) : ℝ := ∑' j : ℤ, 1 / (1 + (j.natAbs : ℝ)) ^ s

theorem intNatAbsPowTotal_nonneg (s : ℝ) : 0 ≤ intNatAbsPowTotal s := by
  refine tsum_nonneg fun j => ?_
  positivity

/-- Shifting the index preserves summability over `ℤ`. -/
theorem summable_shift_int {f : ℤ → ℝ} (hf : Summable f) (n : ℤ) :
    Summable (fun l : ℤ => f (n + l)) := by
  have h := hf.comp_injective (add_right_injective n)
  simpa [Function.comp_def] using h

/-- Shifting the index preserves the sum over `ℤ`. -/
theorem tsum_shift_int (f : ℤ → ℝ) (n : ℤ) : ∑' l : ℤ, f (n + l) = ∑' r : ℤ, f r :=
  (Equiv.addLeft n).tsum_eq f

/-- Translation invariance of the total weight. -/
theorem tsum_one_div_one_add_natAbs_shift (s : ℝ) (n : ℤ) :
    ∑' l : ℤ, 1 / (1 + ((n + l).natAbs : ℝ)) ^ s = intNatAbsPowTotal s :=
  tsum_shift_int (fun r : ℤ => 1 / (1 + (r.natAbs : ℝ)) ^ s) n

theorem summable_one_div_one_add_natAbs_rpow_shift {s : ℝ} (hs : 1 < s) (n : ℤ) :
    Summable (fun l : ℤ => 1 / (1 + ((n + l).natAbs : ℝ)) ^ s) :=
  summable_shift_int (summable_one_div_one_add_natAbs_rpow hs) n

/-! ## The two pieces are square summable -/

theorem summable_sq_bulk {A θ : ℝ} (hθ : 1 / 2 < θ) :
    Summable (fun j : ℤ => (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2) := by
  have hs : (1 : ℝ) < 2 * θ := by linarith
  have hbase := (summable_one_div_one_add_natAbs_rpow hs).mul_left (A ^ 2)
  refine hbase.congr fun j => ?_
  have hp : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by positivity
  rw [div_pow, ← Real.rpow_natCast ((1 + (j.natAbs : ℝ)) ^ θ) 2, ← Real.rpow_mul hp.le]
  have hexp : θ * ((2 : ℕ) : ℝ) = 2 * θ := by push_cast; ring
  rw [hexp]
  field_simp

theorem tsum_sq_bulk {A θ : ℝ} (hθ : 1 / 2 < θ) :
    ∑' j : ℤ, (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2 = A ^ 2 * intNatAbsPowTotal (2 * θ) := by
  have hs : (1 : ℝ) < 2 * θ := by linarith
  rw [intNatAbsPowTotal, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hp : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by positivity
  rw [div_pow, ← Real.rpow_natCast ((1 + (j.natAbs : ℝ)) ^ θ) 2, ← Real.rpow_mul hp.le]
  have hexp : θ * ((2 : ℕ) : ℝ) = 2 * θ := by push_cast; ring
  rw [hexp]
  field_simp

theorem sq_spikeProfile_le {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (I : ℕ) (l : ℤ) :
    (spikeProfile B c I l) ^ 2
      ≤ B ^ 2 * (I : ℝ) ^ (2 * c) * (1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) := by
  have hp : (0 : ℝ) < 1 + (((I : ℤ) + l).natAbs : ℝ) := by positivity
  have hIn : (0 : ℝ) ≤ (I : ℝ) := by positivity
  have hval : (B * ((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ))) ^ c) ^ 2
      = B ^ 2 * (I : ℝ) ^ (2 * c) * (1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) := by
    rw [mul_pow, ← Real.rpow_natCast (((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ))) ^ c) 2,
      ← Real.rpow_mul (by positivity)]
    have hexp : c * ((2 : ℕ) : ℝ) = 2 * c := by push_cast; ring
    rw [hexp, Real.div_rpow hIn hp.le]
    field_simp
  rw [spikeProfile]
  split_ifs with h
  · rw [hval]
  · have : (0 : ℝ) ≤ B ^ 2 * (I : ℝ) ^ (2 * c)
        * (1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) := by positivity
    simpa using this

theorem summable_sq_spikeProfile {B c : ℝ} (hB : 0 ≤ B) (hc : 1 / 2 < c) (I : ℕ) :
    Summable (fun l : ℤ => (spikeProfile B c I l) ^ 2) := by
  have hs : (1 : ℝ) < 2 * c := by linarith
  have hshift : Summable (fun l : ℤ => 1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) :=
    summable_one_div_one_add_natAbs_rpow_shift hs ((I : ℤ))
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _)
    (fun l => sq_spikeProfile_le hB (by linarith) I l)
    (hshift.mul_left (B ^ 2 * (I : ℝ) ^ (2 * c)))

theorem tsum_sq_spikeProfile_le {B c : ℝ} (hB : 0 ≤ B) (hc : 1 / 2 < c) (I : ℕ) :
    ∑' l : ℤ, (spikeProfile B c I l) ^ 2
      ≤ B ^ 2 * (I : ℝ) ^ (2 * c) * intNatAbsPowTotal (2 * c) := by
  have hs : (1 : ℝ) < 2 * c := by linarith
  have hshift : Summable (fun l : ℤ => 1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) :=
    summable_one_div_one_add_natAbs_rpow_shift hs ((I : ℤ))
  calc ∑' l : ℤ, (spikeProfile B c I l) ^ 2
      ≤ ∑' l : ℤ, B ^ 2 * (I : ℝ) ^ (2 * c)
          * (1 / (1 + (((I : ℤ) + l).natAbs : ℝ)) ^ (2 * c)) := by
        refine (summable_sq_spikeProfile hB hc I).tsum_le_tsum
          (fun l => sq_spikeProfile_le hB (by linarith) I l) (hshift.mul_left _)
    _ = B ^ 2 * (I : ℝ) ^ (2 * c) * intNatAbsPowTotal (2 * c) := by
        rw [tsum_mul_left, tsum_one_div_one_add_natAbs_shift (2 * c) ((I : ℤ))]

/-! ## The class controls the total mass -/

theorem tsum_sq_norm_le_of_twoPieceAmplitude {A θ B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hθ : 1 / 2 < θ) (hc : 1 / 2 < c) {I : ℕ} {g : ℤ → ℂ}
    (h : TwoPieceAmplitude A θ B c I g) :
    ∑' j : ℤ, ‖g j‖ ^ 2
      ≤ 2 * (A ^ 2 * intNatAbsPowTotal (2 * θ))
        + 2 * (B ^ 2 * (I : ℝ) ^ (2 * c) * intNatAbsPowTotal (2 * c)) := by
  have hmaj : ∀ j : ℤ, ‖g j‖ ^ 2
      ≤ 2 * (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2 + 2 * (spikeProfile B c I j) ^ 2 := by
    intro j
    have hj := h j
    have h0 : (0 : ℝ) ≤ A / (1 + (j.natAbs : ℝ)) ^ θ := by positivity
    have h1 : (0 : ℝ) ≤ spikeProfile B c I j := spikeProfile_nonneg hB I j
    nlinarith [hj, norm_nonneg (g j), sq_nonneg
      ((A / (1 + (j.natAbs : ℝ)) ^ θ) - spikeProfile B c I j)]
  have hsummaj : Summable (fun j : ℤ =>
      2 * (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2 + 2 * (spikeProfile B c I j) ^ 2) :=
    ((summable_sq_bulk (A := A) hθ).mul_left 2).add
      ((summable_sq_spikeProfile hB hc I).mul_left 2)
  have hsumg : Summable (fun j : ℤ => ‖g j‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hmaj hsummaj
  calc ∑' j : ℤ, ‖g j‖ ^ 2
      ≤ ∑' j : ℤ, (2 * (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2
          + 2 * (spikeProfile B c I j) ^ 2) := hsumg.tsum_le_tsum hmaj hsummaj
    _ = 2 * (∑' j : ℤ, (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2)
          + 2 * (∑' j : ℤ, (spikeProfile B c I j) ^ 2) := by
        rw [Summable.tsum_add ((summable_sq_bulk (A := A) hθ).mul_left 2)
          ((summable_sq_spikeProfile hB hc I).mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * (A ^ 2 * intNatAbsPowTotal (2 * θ))
          + 2 * (B ^ 2 * (I : ℝ) ^ (2 * c) * intNatAbsPowTotal (2 * c)) := by
        have h1 : ∑' j : ℤ, (A / (1 + (j.natAbs : ℝ)) ^ θ) ^ 2
            = A ^ 2 * intNatAbsPowTotal (2 * θ) := tsum_sq_bulk hθ
        have h2 := tsum_sq_spikeProfile_le hB hc I
        linarith

/-- **Parseval form.**  A circle function whose Fourier coefficients lie in the two-piece class
has controlled `L²` norm. -/
theorem norm_sq_le_of_twoPieceAmplitude {A θ B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hθ : 1 / 2 < θ) (hc : 1 / 2 < c) {I : ℕ}
    {u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (h : TwoPieceAmplitude A θ B c I
      (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)) :
    ‖u‖ ^ 2
      ≤ 2 * (A ^ 2 * intNatAbsPowTotal (2 * θ))
        + 2 * (B ^ 2 * (I : ℝ) ^ (2 * c) * intNatAbsPowTotal (2 * c)) := by
  have hpars := norm_sq_eq_tsum_fourierCoeff u
  have hrw : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ) = x ^ 2 := by
    intro x hx
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrw _ (norm_nonneg u)] at hpars
  have hcongr : ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
      = ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 :=
    tsum_congr fun j => hrw _ (norm_nonneg _)
  rw [hcongr] at hpars
  rw [hpars]
  exact tsum_sq_norm_le_of_twoPieceAmplitude hA hB hθ hc h

end

end RHTower
