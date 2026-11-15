import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteDifference.BoundedRealDifferences

/-!
# Polynomial phases confined to a short arc

The highest difference of a fractional-part sequence is an integer whenever
the original phase has vanishing difference of that order. An arc shorter
than `2^(-d)` makes this integer zero. Bounded difference rigidity then
forces the phase to be constant modulo the integers.
-/

namespace GaloisForLFunctions.PrimeTorusTheory
open Function
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Fractional and integer parts split every iterated difference exactly. -/
theorem difference_fract_add_floor (f : ℕ → ℝ) (n j : ℕ) :
    (fwdDiff 1)^[n] (fun i => Int.fract (f i)) j +
      (((fwdDiff 1)^[n] (fun i => Int.floor (f i)) j : ℤ) : ℝ) =
        (fwdDiff 1)^[n] f j := by
  induction n generalizing j with
  | zero => change f j - (Int.floor (f j) : ℝ) + (Int.floor (f j) : ℝ) = f j; ring
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
    simp only [fwdDiff, Int.cast_sub]
    linear_combination ih (j + 1) - ih j

/-- Integer-valued real numbers strictly between `-1` and `1` vanish. -/
private theorem integer_cast_eq_zero_of_short (z : ℤ)
    (hlo : (-1 : ℝ) < (z : ℝ)) (hhi : (z : ℝ) < 1) : z = 0 := by
  have hlo' : (-1 : ℤ) < z := by exact_mod_cast hlo
  have hhi' : z < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- A polynomial phase confined to an arc shorter than its finite-difference
threshold is constant modulo the integers. -/
theorem short_arc_phase_constant (f : ℕ → ℝ) (d : ℕ) (L D : ℝ)
    (hf : (fwdDiff 1)^[d + 1] f = 0)
    (hb : ∀ j, L ≤ Int.fract (f j) ∧ Int.fract (f j) ≤ L + D)
    (hsize : 2 ^ d * D < 1) : ∀ j, Int.fract (f j) = Int.fract (f 0) := by
  apply (bounded_real_iterated_difference_zero_iff (fun j => Int.fract (f j)) L D hb d).mp
  funext j
  have hs := difference_fract_add_floor f (d + 1) j
  rw [hf] at hs
  have hd := real_iterated_difference_interval_bound (fun j => Int.fract (f j)) L D hb d j
  have hz : (fwdDiff 1)^[d + 1] (fun i => Int.floor (f i)) j = 0 := by
    apply integer_cast_eq_zero_of_short
    · change (fwdDiff 1)^[d + 1] (fun i => Int.fract (f i)) j +
        (((fwdDiff 1)^[d + 1] (fun i => Int.floor (f i)) j : ℤ) : ℝ) = 0 at hs
      linarith only [hs, hd.2, hsize]
    · change (fwdDiff 1)^[d + 1] (fun i => Int.fract (f i)) j +
        (((fwdDiff 1)^[d + 1] (fun i => Int.floor (f i)) j : ℤ) : ℝ) = 0 at hs
      linarith only [hs, hd.1, hsize]
  rw [hz, Int.cast_zero, add_zero] at hs
  exact hs

/-- The positive result identifies every phase difference as an integer. -/
theorem short_arc_phase_integer_differences (f : ℕ → ℝ) (d : ℕ) (L D : ℝ)
    (hf : (fwdDiff 1)^[d + 1] f = 0)
    (hb : ∀ j, L ≤ Int.fract (f j) ∧ Int.fract (f j) ≤ L + D)
    (hsize : 2 ^ d * D < 1) : ∀ j, ∃ z : ℤ, f j - f 0 = z := by
  intro j
  exact Int.fract_eq_fract.mp (short_arc_phase_constant f d L D hf hb hsize j)

private theorem real_polynomial_nat_difference_zero (P : Polynomial ℝ) :
    (fwdDiff 1)^[P.natDegree + 1] (fun j : ℕ => P.eval (j : ℝ)) = 0 := by
  have he : ∀ n j : ℕ,
      (fwdDiff 1)^[n] (fun i : ℕ => P.eval (i : ℝ)) j =
        (fwdDiff 1)^[n] (fun x : ℝ => P.eval x) (j : ℝ) := by
    intro n
    induction n with
    | zero => intro j; rfl
    | succ n ih =>
      intro j
      rw [iterate_succ_apply', iterate_succ_apply']
      change (fwdDiff 1)^[n] (fun i : ℕ => P.eval (i : ℝ)) (j + 1) -
          (fwdDiff 1)^[n] (fun i : ℕ => P.eval (i : ℝ)) j =
        (fwdDiff 1)^[n] (fun x : ℝ => P.eval x) ((j : ℝ) + 1) -
          (fwdDiff 1)^[n] (fun x : ℝ => P.eval x) (j : ℝ)
      rw [ih, ih, Nat.cast_add, Nat.cast_one]
  funext j
  rw [he, P.fwdDiff_iter_degree_add_one_eq_zero]
  rfl

/-- An actual real polynomial has short-arc values exactly when its fractional
part is constant there; no rationality of its coefficients is required. -/
theorem polynomial_short_arc_iff (P : Polynomial ℝ) (L D : ℝ)
    (hsize : 2 ^ P.natDegree * D < 1) :
    (∀ j : ℕ, L ≤ Int.fract (P.eval (j : ℝ)) ∧ Int.fract (P.eval (j : ℝ)) ≤ L + D) ↔
      (L ≤ Int.fract (P.eval 0) ∧ Int.fract (P.eval 0) ≤ L + D) ∧
        ∀ j : ℕ, ∃ z : ℤ, P.eval (j : ℝ) - P.eval 0 = z := by
  constructor
  · intro hb
    refine ⟨by simpa only [Nat.cast_zero] using hb 0, ?_⟩
    simpa only [Nat.cast_zero] using short_arc_phase_integer_differences _ _ L D
      (real_polynomial_nat_difference_zero P) hb hsize
  · rintro ⟨h0, hc⟩ j
    rw [Int.fract_eq_fract.mpr (hc j)]
    exact h0

end GaloisForLFunctions.PrimeTorusTheory

#print axioms GaloisForLFunctions.PrimeTorusTheory.difference_fract_add_floor
#print axioms GaloisForLFunctions.PrimeTorusTheory.short_arc_phase_constant
#print axioms GaloisForLFunctions.PrimeTorusTheory.short_arc_phase_integer_differences
#print axioms GaloisForLFunctions.PrimeTorusTheory.polynomial_short_arc_iff
