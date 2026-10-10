import GaloisForLFunctions.HTGeometry.PaperRotationNormRate
import GaloisForLFunctions.RHTower.PaperPrimeRotationIdealTrace

/-!
# Prime logarithms recovered from rotation commutator norms

The scaled norm of a prime word commutator converges to signed-area magnitude times `log p`.
The primitive pair therefore recovers the prime from its first-order commutation defect. The
same coefficient classifies the paper's extended ideal-trace cost at every positive clock step.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry Filter Topology
open scoped ENNReal Classical

/-- First-order size of the literal prime word commutator. -/
def paperPrimeRotationNormSlope (p : Nat.Primes) (a b c d : ℤ) : ℝ :=
  |((c * b - a * d : ℤ) : ℝ)| * Real.log p

theorem paperPrimeRotationNormSlope_nonneg (p : Nat.Primes) (a b c d : ℤ) :
    0 ≤ paperPrimeRotationNormSlope p a b c d :=
  mul_nonneg (abs_nonneg _) p.2.log_pos.le

theorem paperPrimeRotationNormSlope_eq_zero (p : Nat.Primes) (a b c d : ℤ) :
    paperPrimeRotationNormSlope p a b c d = 0 ↔ c * b = a * d := by
  simp only [paperPrimeRotationNormSlope, mul_eq_zero, abs_eq_zero,
    Int.cast_eq_zero, p.2.log_ne_zero, or_false, sub_eq_zero]

theorem paperPrimeRotationNormSlope_pos (p : Nat.Primes) (a b c d : ℤ) :
    0 < paperPrimeRotationNormSlope p a b c d ↔ c * b ≠ a * d := by
  constructor
  · intro h hz
    exact (ne_of_gt h) ((paperPrimeRotationNormSlope_eq_zero p a b c d).2 hz)
  · intro h
    refine lt_of_le_of_ne (paperPrimeRotationNormSlope_nonneg p a b c d) ?_
    intro hz
    exact h ((paperPrimeRotationNormSlope_eq_zero p a b c d).1 hz.symm)

private theorem norm_succ (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    ‖paperPrimeRotationCommutator p (q + 1) a b c d‖ =
      ‖paperRotationPhase (-(((c * b - a * d : ℤ) : ℝ) * Real.log p) /
        ((q : ℝ) + 1)) - 1‖ := by
  rw [paperPrimeRotationCommutator_norm, paperPrimeRotationFrequency_eq,
    Nat.cast_add, Nat.cast_one]
  congr 3
  ring

/-- Exact finite-clock correction to the limiting arithmetic coefficient. -/
theorem paperPrimeRotationCommutator_scaled_norm_sinc
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    ((q : ℝ) + 1) * ‖paperPrimeRotationCommutator p (q + 1) a b c d‖ =
      paperPrimeRotationNormSlope p a b c d *
        |Real.sinc ((((c * b - a * d : ℤ) : ℝ) * Real.log p) /
          (2 * ((q : ℝ) + 1)))| := by
  rw [norm_succ, paperRotationPhase_scaled_norm]
  simp only [neg_div, Real.sinc_neg, abs_neg, abs_mul, abs_of_pos p.2.log_pos,
    paperPrimeRotationNormSlope]

/-- A bound valid at every positive clock denominator. -/
theorem paperPrimeRotationCommutator_scaled_norm_le
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    ((q : ℝ) + 1) * ‖paperPrimeRotationCommutator p (q + 1) a b c d‖ ≤
      paperPrimeRotationNormSlope p a b c d := by
  rw [paperPrimeRotationCommutator_scaled_norm_sinc]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _)
    (paperPrimeRotationNormSlope_nonneg p a b c d)

theorem paperPrimeRotationCommutator_norm_le_rate
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    ‖paperPrimeRotationCommutator p (q + 1) a b c d‖ ≤
      paperPrimeRotationNormSlope p a b c d / ((q : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : 0 < (q : ℝ) + 1)).2
  simpa only [mul_comm] using paperPrimeRotationCommutator_scaled_norm_le p q a b c d

/-- The first-order limit keeps both the prime logarithm and the integer signed-area magnitude. -/
theorem paperPrimeRotationCommutator_scaled_norm_tendsto
    (p : Nat.Primes) (a b c d : ℤ) :
    Tendsto (fun q : ℕ => ((q : ℝ) + 1) *
      ‖paperPrimeRotationCommutator p (q + 1) a b c d‖)
      atTop (𝓝 (paperPrimeRotationNormSlope p a b c d)) := by
  simpa only [norm_succ, abs_neg, abs_mul, abs_of_pos p.2.log_pos,
    paperPrimeRotationNormSlope] using
    paperRotationPhase_scaled_norm_tendsto (-(((c * b - a * d : ℤ) : ℝ) * Real.log p))

/-- Zero first-order coefficient is equivalent to exact compactness at every genuine clock. -/
theorem paperPrimeRotationCommutator_compact_iff_slope_zero
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    IsCompactOperator (paperPrimeRotationCommutator p (q + 1) a b c d) ↔
      paperPrimeRotationNormSlope p a b c d = 0 := by
  simp only [paperPrimeRotationCommutator_compact_iff, Nat.add_one_ne_zero, false_or,
    paperPrimeRotationNormSlope_eq_zero]

/-- The quantitative norm invariant detects the exact extended ideal-trace dichotomy. -/
theorem paperPrimeRotationCommutator_traceCost_eq_slope
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p (q + 1) a b c d) =
        if paperPrimeRotationNormSlope p a b c d = 0 then 0 else ∞ := by
  simp only [paperPrimeRotationCommutator_traceCost_succ, paperPrimeRotationNormSlope_eq_zero]

/-- Compact changes preserve the ideal cost detected by the unperturbed norm coefficient. -/
theorem paperPrimeRotationCommutator_traceCost_add_compact_eq_slope
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p (q + 1) a b c d + K.1) =
        if paperPrimeRotationNormSlope p a b c d = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperPrimeRotationCommutator_traceCost_eq_slope]

/-- The primitive generator pair reads the prime logarithm in its norm decay. -/
theorem paperPrimeRotationPrimitive_scaled_norm_tendsto (p : Nat.Primes) :
    Tendsto (fun q : ℕ => ((q : ℝ) + 1) *
      ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖) atTop (𝓝 (Real.log p)) := by
  simpa [paperPrimeRotationNormSlope] using
    paperPrimeRotationCommutator_scaled_norm_tendsto p 0 1 1 0

/-- The primitive first-order invariant distinguishes every pair of primes. -/
theorem paperPrimeRotationPrimitive_slope_injective :
    Function.Injective (fun p : Nat.Primes => paperPrimeRotationNormSlope p 0 1 1 0) := by
  intro p r h
  have hl : Real.log (p : ℝ) = Real.log (r : ℝ) := by
    simpa [paperPrimeRotationNormSlope] using h
  have hr : (p : ℝ) = (r : ℝ) :=
    Real.log_injOn_pos
      (by change (0 : ℝ) < (p : ℝ); exact_mod_cast p.2.pos)
      (by change (0 : ℝ) < (r : ℝ); exact_mod_cast r.2.pos) hl
  apply Subtype.ext
  exact_mod_cast hr

/-- The coefficient is the least uniform bound on all scaled commutator norms. -/
theorem paperPrimeRotationCommutator_scaled_norm_bound_iff
    (p : Nat.Primes) (a b c d : ℤ) (B : ℝ) :
    (∀ q : ℕ, ((q : ℝ) + 1) *
      ‖paperPrimeRotationCommutator p (q + 1) a b c d‖ ≤ B) ↔
        paperPrimeRotationNormSlope p a b c d ≤ B := by
  constructor
  · exact le_of_tendsto' (paperPrimeRotationCommutator_scaled_norm_tendsto p a b c d)
  · intro h q
    exact (paperPrimeRotationCommutator_scaled_norm_le p q a b c d).trans h

/-- Faster than reciprocal-clock norm decay occurs precisely for commuting word directions. -/
theorem paperPrimeRotationCommutator_scaled_norm_tendsto_zero_iff
    (p : Nat.Primes) (a b c d : ℤ) :
    Tendsto (fun q : ℕ => ((q : ℝ) + 1) *
      ‖paperPrimeRotationCommutator p (q + 1) a b c d‖) atTop (𝓝 0) ↔
        c * b = a * d := by
  constructor
  · intro h
    exact (paperPrimeRotationNormSlope_eq_zero p a b c d).1
      (tendsto_nhds_unique (paperPrimeRotationCommutator_scaled_norm_tendsto p a b c d) h)
  · intro h
    have hz := (paperPrimeRotationNormSlope_eq_zero p a b c d).2 h
    simpa only [hz] using paperPrimeRotationCommutator_scaled_norm_tendsto p a b c d

/-- The entire primitive norm profile determines the prime, without observing complex phases. -/
theorem paperPrimeRotationPrimitive_norm_profile_eq_iff (p r : Nat.Primes) :
    (∀ q : ℕ, ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ =
      ‖paperPrimeRotationCommutator r (q + 1) 0 1 1 0‖) ↔ p = r := by
  constructor
  · intro h
    apply paperPrimeRotationPrimitive_slope_injective
    have hp := paperPrimeRotationCommutator_scaled_norm_tendsto p 0 1 1 0
    have hr := paperPrimeRotationCommutator_scaled_norm_tendsto r 0 1 1 0
    have he : (fun q : ℕ => ((q : ℝ) + 1) *
        ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖) =
        (fun q : ℕ => ((q : ℝ) + 1) *
        ‖paperPrimeRotationCommutator r (q + 1) 0 1 1 0‖) := by
      funext q
      rw [h q]
    rw [he] at hp
    exact tendsto_nhds_unique hp hr
  · rintro rfl
    exact fun _ => rfl

end

end RHTower
