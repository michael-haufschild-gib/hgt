import GaloisForLFunctions.HTGeometry.PaperRotationCommutatorIdealTrace
import GaloisForLFunctions.RHTower.PrimeIrrationalRotationKZeroRH

/-!
# Prime rotation phases in the paper's extended ideal trace

The actual IRK prime phase is realized by bilateral Weyl operators. For a nonzero clock
denominator, their commutator is compact exactly when the integer signed area vanishes. Every
nonzero-area commutator has infinite compact-ideal trace cost, although the entire family tends
to zero in operator norm as the clock denominator grows. This is an exact operator/ideal result;
it does not construct an arithmetic Xi module or identify a horizontal-zero multiplicity.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry Filter Topology
open scoped ENNReal Classical

/-- The signed angular frequency of the corpus-native prime rotation multiplier. -/
def paperPrimeRotationFrequency (p : Nat.Primes) (q : ℕ) : ℝ :=
  -2 * primeRotationParameter p q * Real.pi

theorem paperPrimeRotationFrequency_eq (p : Nat.Primes) (q : ℕ) :
    paperPrimeRotationFrequency p q = -Real.log p / (q : ℝ) := by
  by_cases hq : q = 0
  · simp [hq, paperPrimeRotationFrequency, primeRotationParameter]
  · unfold paperPrimeRotationFrequency primeRotationParameter
    field_simp [Real.pi_ne_zero, hq]

/-- Exact agreement with the native rank-one algebraic prime-Weyl determinant phase. -/
theorem paperPrimeRotationPhase_eq_native (p : Nat.Primes) (q : ℕ) :
    paperRotationPhase (paperPrimeRotationFrequency p q) =
      primeAlgebraicWeylDeterminantPhase p 1 q := by
  by_cases hq : q = 0
  · simp [hq, paperPrimeRotationFrequency, primeRotationParameter,
      primeAlgebraicWeylDeterminantPhase]
  · rw [primeAlgebraicWeylDeterminantPhase_one_eq_rotationMultiplier p hq]
    change Complex.exp (((-2 * primeRotationParameter p q * Real.pi : ℝ) : ℂ) *
      Complex.I) = _
    rw [Complex.ofReal_mul]

/-- Irrationality removes every nonzero integer signed-area phase at a genuine clock step. -/
theorem paperPrimeRotationPhase_int_eq_one (p : Nat.Primes) (q : ℕ) (k : ℤ) :
    paperRotationPhase (k * paperPrimeRotationFrequency p q) = 1 ↔ q = 0 ∨ k = 0 := by
  by_cases hq : q = 0
  · simp [hq, paperPrimeRotationFrequency, primeRotationParameter]
  · simp only [hq, false_or]
    constructor
    · intro h
      have hc : Circle.exp (k * paperPrimeRotationFrequency p q) = 1 :=
        Circle.coe_eq_one.mp h
      obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hc
      have hz : (-2 * Real.pi) *
          ((k : ℝ) * primeRotationParameter p q + (n : ℝ)) = 0 := by
        dsimp only [paperPrimeRotationFrequency] at hn
        nlinarith [hn]
      have hl : (k : ℝ) * primeRotationParameter p q + (n : ℝ) = 0 :=
        (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      have ht : irrationalRotationKZeroTrace (primeRotationParameter p q) 0 k = (-n : ℤ) := by
        unfold irrationalRotationKZeroTrace
        push_cast
        linarith
      exact chern_eq_zero_of_irrationalRotationKZeroTrace_eq_integer
        (primeRotationParameter_irrational p hq) ht
    · rintro rfl
      simp

/-- Commutator of the integer words `(a,b)` and `(c,d)` in the native prime rotation phase. -/
def paperPrimeRotationCommutator (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  paperRotationCommutator a c (b * paperPrimeRotationFrequency p q)
    (d * paperPrimeRotationFrequency p q)

private theorem scaled_area (a b c d : ℤ) (t : ℝ) :
    (c : ℝ) * ((b : ℝ) * t) - (a : ℝ) * ((d : ℝ) * t) =
      ((c * b - a * d : ℤ) : ℝ) * t := by
  push_cast
  ring

/-- Literal norm of the prime commutator, retaining the integer signed area. -/
theorem paperPrimeRotationCommutator_norm (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    ‖paperPrimeRotationCommutator p q a b c d‖ =
      ‖paperRotationPhase (((c * b - a * d : ℤ) : ℝ) *
        paperPrimeRotationFrequency p q) - 1‖ := by
  simp only [paperPrimeRotationCommutator, paperRotationCommutator_norm, scaled_area]

/-- The full compactness classification includes the degenerate zero clock denominator. -/
theorem paperPrimeRotationCommutator_compact_iff (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    IsCompactOperator (paperPrimeRotationCommutator p q a b c d) ↔
      q = 0 ∨ c * b = a * d := by
  simp only [paperPrimeRotationCommutator, paperRotationCommutator_compact_iff,
    scaled_area, paperPrimeRotationPhase_int_eq_one, sub_eq_zero]

/-- Exact paper trace-cone application: commuting lattice directions cost zero; every other
genuine prime-rotation commutator has infinite compact-ideal cost. -/
theorem paperPrimeRotationCommutator_traceCost (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p q a b c d) =
        if q = 0 ∨ c * b = a * d then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperPrimeRotationCommutator_compact_iff]
  split_ifs <;> rfl

/-- Compact corrections preserve that exact arithmetic classification. -/
theorem paperPrimeRotationCommutator_traceCost_add_compact
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p q a b c d + K.1) =
        if q = 0 ∨ c * b = a * d then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperPrimeRotationCommutator_traceCost]

/-- Every positive clock denominator reads only the signed area for exact compactness. -/
theorem paperPrimeRotationCommutator_traceCost_succ
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p (q + 1) a b c d) =
        if c * b = a * d then 0 else ∞ := by
  simp only [paperPrimeRotationCommutator_traceCost, Nat.add_one_ne_zero, false_or]

/-- In particular, the two primitive generators have infinite cost at every positive step. -/
theorem paperPrimeRotationPrimitive_traceCost (p : Nat.Primes) (q : ℕ) :
    compactOperatorTraceCost PaperRotationHilbert
      (paperPrimeRotationCommutator p (q + 1) 0 1 1 0) = ∞ := by
  simp [paperPrimeRotationCommutator_traceCost_succ]

theorem paperPrimeRotationFrequency_tendsto (p : Nat.Primes) :
    Tendsto (paperPrimeRotationFrequency p) atTop (𝓝 0) := by
  change Tendsto (fun q : ℕ => paperPrimeRotationFrequency p q) atTop (𝓝 0)
  simp_rw [paperPrimeRotationFrequency_eq]
  exact Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop

/-- All fixed prime word commutators tend to zero in operator norm. Infinite ideal-trace cost
therefore persists along the nonzero-area families even in this genuine norm-small limit. -/
theorem paperPrimeRotationCommutator_tendsto_zero (p : Nat.Primes) (a b c d : ℤ) :
    Tendsto (fun q => paperPrimeRotationCommutator p q a b c d) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto
      (fun q => ((c * b - a * d : ℤ) : ℝ) * paperPrimeRotationFrequency p q)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (paperPrimeRotationFrequency_tendsto p)
  have hc : Continuous (fun t : ℝ => ‖paperRotationPhase t - 1‖) := by
    unfold paperRotationPhase
    fun_prop
  have h := (hc.tendsto 0).comp ht
  simpa only [Function.comp_def, paperPrimeRotationCommutator_norm, paperRotationPhase_zero,
    sub_self, norm_zero] using h

end

end RHTower
