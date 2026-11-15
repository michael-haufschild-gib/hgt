import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A projective spectral coordinate for finite Kesten sections

The determinant divided by the dimension-th power of the trace is unchanged
by similarity and nonzero scalar multiplication. For the Kesten precision
matrix of dimension `n+1`, this ratio is the rational function below.
Its logarithmic derivative is strictly positive for `n>0` on the positive
half-line, so it distinguishes the prime parameter even after rescaling.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass.Primon

/-- The numerator obtained by clearing the reciprocal in the precision trace. -/
def kestenPrecisionTraceNumerator (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) + 1) * x ^ 2 + x + n

/-- The determinant-to-trace ratio in reciprocal-free coordinates. -/
def kestenProjectiveShape (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * n + 1) * (x + 1) / kestenPrecisionTraceNumerator n x ^ (n + 1)

/-- Logarithmic coordinates avoid differentiating powers with depth-dependent exponent. -/
def kestenProjectiveLogShape (n : ℕ) (x : ℝ) : ℝ :=
  (2 * (n : ℝ) + 1) * Real.log x + Real.log (x + 1) -
    ((n : ℝ) + 1) * Real.log (kestenPrecisionTraceNumerator n x)

theorem kestenPrecisionTraceNumerator_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < kestenPrecisionTraceNumerator n x := by
  unfold kestenPrecisionTraceNumerator
  positivity

theorem kestenProjectiveShape_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < kestenProjectiveShape n x :=
  div_pos (mul_pos (pow_pos hx _) (add_pos hx zero_lt_one))
    (pow_pos (kestenPrecisionTraceNumerator_pos n hx) _)

theorem kestenProjectiveShape_log (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log (kestenProjectiveShape n x) = kestenProjectiveLogShape n x := by
  rw [kestenProjectiveShape,
    Real.log_div (mul_ne_zero (pow_ne_zero _ hx.ne') (add_pos hx zero_lt_one).ne')
      (pow_ne_zero _ (kestenPrecisionTraceNumerator_pos n hx).ne'),
    Real.log_mul (pow_ne_zero _ hx.ne') (add_pos hx zero_lt_one).ne',
    Real.log_pow, Real.log_pow]
  simp only [kestenProjectiveLogShape, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]

/-- Cancellation leaves a positive rational logarithmic derivative at every positive depth. -/
theorem hasDerivAt_kestenProjectiveLogShape (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (kestenProjectiveLogShape n)
      ((n : ℝ) * ((2 * (n : ℝ) + 3) * x + (2 * (n : ℝ) + 1)) /
        (x * (x + 1) * kestenPrecisionTraceNumerator n x)) x := by
  have hx1 : 0 < x + 1 := add_pos hx zero_lt_one
  have hs := kestenPrecisionTraceNumerator_pos n hx
  have hd : HasDerivAt (kestenPrecisionTraceNumerator n)
      (2 * ((n : ℝ) + 1) * x + 1) x := by
    refine (((((hasDerivAt_id x).pow 2).const_mul ((n : ℝ) + 1)).add
      (hasDerivAt_id x)).add_const (n : ℝ)).congr_deriv ?_
    dsimp only [id]
    ring
  refine (((((hasDerivAt_id x).log hx.ne').const_mul (2 * (n : ℝ) + 1)).add
    (((hasDerivAt_id x).add_const 1).log hx1.ne')).sub
      ((hd.log hs.ne').const_mul ((n : ℝ) + 1))).congr_deriv ?_
  dsimp only [id]
  unfold kestenPrecisionTraceNumerator at hs ⊢
  field_simp [hx.ne', hx1.ne', hs.ne']
  ring

theorem strictMonoOn_kestenProjectiveLogShape (n : ℕ) (hn : 0 < n) :
    StrictMonoOn (kestenProjectiveLogShape n) (Set.Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro x hx
    exact (hasDerivAt_kestenProjectiveLogShape n hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(hasDerivAt_kestenProjectiveLogShape n hx').deriv]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hs := kestenPrecisionTraceNumerator_pos n hx'
    positivity

theorem strictMonoOn_kestenProjectiveShape (n : ℕ) (hn : 0 < n) :
    StrictMonoOn (kestenProjectiveShape n) (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  apply (Real.log_lt_log_iff (kestenProjectiveShape_pos n hx)
    (kestenProjectiveShape_pos n hy)).mp
  rw [kestenProjectiveShape_log n hx, kestenProjectiveShape_log n hy]
  exact strictMonoOn_kestenProjectiveLogShape n hn hx hy hxy

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.hasDerivAt_kestenProjectiveLogShape
#print axioms GaloisForLFunctions.SelbergClass.Primon.strictMonoOn_kestenProjectiveShape
