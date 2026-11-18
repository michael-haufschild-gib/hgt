import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer multiplicities from cumulative conductor weights

Taking differences of rounded cumulative masses keeps every prefix error
below one. For a signed reading, discrete summation by parts charges the
variation of the reading once, independently of the number of conductors.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

private abbrev prefixWeight (w : ℕ → ℝ) (n : ℕ) := ∑ i ∈ range n, w i

/-- Multiplicity assigned to cell i by rounding consecutive cumulative masses. -/
def cumulativeWeightMultiplicity (w : ℕ → ℝ) (i : ℕ) : ℕ :=
  ⌊prefixWeight w (i+1)⌋₊-⌊prefixWeight w i⌋₊

private theorem prefix_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (n : ℕ) : 0 ≤ prefixWeight w n :=
  sum_nonneg fun i _ => hw i

private theorem cast_multiplicity {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (i : ℕ) :
    (cumulativeWeightMultiplicity w i:ℝ)=
      (⌊prefixWeight w (i+1)⌋₊:ℝ)-(⌊prefixWeight w i⌋₊:ℝ) := by
  apply Nat.cast_sub
  apply Nat.floor_mono
  change _ ≤ ∑ j ∈ range (i+1), w j
  rw [sum_range_succ]
  exact le_add_of_nonneg_right (hw i)

/-- Integer lower and upper bounds on each weight survive cumulative rounding. -/
theorem cumulativeWeightMultiplicity_interval {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (i k K : ℕ)
    (hl : (k:ℝ) ≤ w i) (hu : w i ≤ (K:ℝ)) : k ≤ cumulativeWeightMultiplicity w i ∧
      cumulativeWeightMultiplicity w i ≤ K := by
  have hs : prefixWeight w (i+1)=prefixWeight w i+w i := sum_range_succ _ _
  have ha := Nat.floor_mono (add_le_add (le_refl (prefixWeight w i)) hl)
  have hb := Nat.floor_mono (add_le_add (le_refl (prefixWeight w i)) hu)
  rw [Nat.floor_add_natCast (prefix_nonneg hw i) k,← hs] at ha
  rw [Nat.floor_add_natCast (prefix_nonneg hw i) K,← hs] at hb
  unfold cumulativeWeightMultiplicity
  omega

/-- The error against any signed reading is at most its terminal absolute
value and its total variation over the chosen cells. -/
theorem cumulativeWeightMultiplicity_reading_error {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (f : ℕ → ℝ) (M : ℕ) :
    |∑ i ∈ range M, ((cumulativeWeightMultiplicity w i:ℝ)-w i)*f i| ≤
      |f M|+∑ i ∈ range M, |f (i+1)-f i| := by
  let d := fun i : ℕ => prefixWeight w i-(⌊prefixWeight w i⌋₊:ℝ)
  have hd (i : ℕ) : |d i| ≤ 1 := by
    have hl := Nat.floor_le (prefix_nonneg hw i)
    have hu := Nat.lt_floor_add_one (prefixWeight w i)
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    linarith only [hu]
  have hstep (i : ℕ) : (cumulativeWeightMultiplicity w i:ℝ)-w i=d i-d (i+1) := by
    rw [cast_multiplicity hw]
    have hs : prefixWeight w (i+1)=prefixWeight w i+w i := sum_range_succ _ _
    dsimp only [d]
    rw [hs]
    ring
  have hAbel (n : ℕ) : (∑ i ∈ range n, ((cumulativeWeightMultiplicity w i:ℝ)-w i)*f i) =
      -(d n*f n)+∑ i ∈ range n,d (i+1)*(f (i+1)-f i) := by
    induction n with
    | zero => simp [d,prefixWeight]
    | succ n ih => rw [sum_range_succ,sum_range_succ,ih,hstep]; ring
  have hprod (i : ℕ) (v : ℝ) : |d i*v| ≤ |v| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg v) (hd i)
  rw [hAbel]
  refine (abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using hprod M (f M)) ?_)
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hprod (i+1) _)

#print axioms cumulativeWeightMultiplicity_interval
#print axioms cumulativeWeightMultiplicity_reading_error

end GaloisForLFunctions.CountingHolography.Sections
