import GaloisForLFunctions.RHTower.PrimeLogThetaPrecompletionWeightedBoundary

/-!
# Prime-log theta precompletion all-jet boundary

The four retained precompletion boundary coordinates are honest Hilbert reporters, but that fact
cannot be extrapolated to the full Wronskian jet.  At one prime with `log p > 1`, the squared
norms of the literal degree reporters form a positive geometric sequence with ratio
`log(p)^(2 : ℕ) > 1`.  Thus the all-degree reporter family is not an `ℓ²` vector in its degree index.

This gives a sharp architectural consequence of the Route P/C1 boundary change: a boundary
object preserving the full Xi filtration cannot be a bounded analysis map into a Hilbert direct
sum of the level coordinates.  In particular, the finite four-level landing is a finite
certificate, not a candidate completion.  The required object must instead retain an unbounded
or projective jet direction before any source-to-divisor formation theorem is attempted.

No connection to escape multiplicity is asserted here.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The complete literal real-axis reporter jet at one prime, indexed by Wronskian degree. -/
def primeLogThetaPrecompletionWeightedBoundaryAllJet
    (x : ℝ) (p : Nat.Primes) : ℕ → ℂ :=
  fun n => primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p

/-- Coordinate formula for the all-jet boundary. -/
theorem primeLogThetaPrecompletionWeightedBoundaryAllJet_apply
    (x : ℝ) (p : Nat.Primes) (n : ℕ) :
    primeLogThetaPrecompletionWeightedBoundaryAllJet x p n =
      primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p := rfl

/-- At a prime whose logarithm exceeds one, the full boundary reporter jet cannot be an
`ℓ²` degree vector.  This is the exact Bessel obstruction to an all-level Hilbert-target reader. -/
theorem not_memℓp_primeLogThetaPrecompletionWeightedBoundaryAllJet
    (x : ℝ) (p : Nat.Primes) (hlog : 1 < Real.log (p : ℝ)) :
    ¬ Memℓp (primeLogThetaPrecompletionWeightedBoundaryAllJet x p) 2 := by
  intro hmem
  have hraw := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hmem
  have hsum : Summable (fun n : ℕ =>
      4 * Real.log (p : ℝ) ^ (2 * n + 4) / (p : ℝ) ^ 2) := by
    refine hraw.congr fun n => ?_
    change ‖primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p‖ ^
      (2 : ℝ) = _
    rw [Real.rpow_two]
    exact norm_sq_primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p
  let c : ℝ := 4 * Real.log (p : ℝ) ^ 4 / (p : ℝ) ^ 2
  let r : ℝ := Real.log (p : ℝ) ^ 2
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog0 : 0 < Real.log (p : ℝ) := by linarith
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hfactor (n : ℕ) :
      4 * Real.log (p : ℝ) ^ (2 * n + 4) / (p : ℝ) ^ 2 = c * r ^ n := by
    dsimp [c, r]
    rw [show 2 * n + 4 = 4 + 2 * n by omega, pow_add, ← pow_mul]
    ring
  have hgeo : Summable (fun n : ℕ => r ^ n) := by
    apply (summable_mul_left_iff hc).mp
    exact hsum.congr hfactor
  have hrlt : ‖r‖ < 1 := summable_geometric_iff_norm_lt_one.mp hgeo
  dsimp [r] at hrlt
  rw [abs_of_nonneg (sq_nonneg _)] at hrlt
  nlinarith

/-- The prime `3` already lies beyond the all-jet Hilbert threshold. -/
private theorem one_lt_log_three : 1 < Real.log (3 : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- Concrete non-Bessel witness for the all-degree literal boundary family. -/
theorem not_memℓp_primeLogThetaPrecompletionWeightedBoundaryAllJet_three
    (x : ℝ) :
    ¬ Memℓp (primeLogThetaPrecompletionWeightedBoundaryAllJet x
      (⟨3, by norm_num⟩ : Nat.Primes)) 2 := by
  apply not_memℓp_primeLogThetaPrecompletionWeightedBoundaryAllJet x
  simpa using one_lt_log_three

end

end RHTower
