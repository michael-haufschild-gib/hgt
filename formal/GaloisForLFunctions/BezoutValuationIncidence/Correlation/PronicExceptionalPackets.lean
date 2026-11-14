import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.HilbertMetric.Correlation.ExceptionalEnergy

/-!
# Exceptional packets in the pronic receiver

The pronic norm is realized by an explicit finite Euclidean vector. Deleting
arbitrary coherent source rows inherits the sharp Hilbert-space deletion law.
The resulting cardinality bound measures how many exceptional rows are needed
to account for an observed loss of receiver energy.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
open HilbertMetric
noncomputable section

/-- Weighted Euclidean realization of the finite pronic receiver. -/
def pronicFeature (T : ℕ) (v : ℕ → ℝ) : EuclideanSpace ℝ ↥(Icc 1 T) :=
  WithLp.toLp 2 fun n => v n * Real.sqrt (1 / ((n : ℝ) * ((n : ℝ) + 1)))

/-- The Euclidean feature has exactly the original pronic norm. -/
theorem norm_pronicFeature_sq (T : ℕ) (v : ℕ → ℝ) :
    ‖pronicFeature T v‖ ^ 2 = pronicNorm T v ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, pronicNorm_sq]
  calc
    _ = ∑ n : ↥(Icc 1 T), v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_congr rfl
      intro n _
      change ‖v n * Real.sqrt (1 / ((n : ℝ) * ((n : ℝ) + 1)))‖ ^ 2 = _
      rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity), mul_one_div]
    _ = _ := Finset.sum_coe_sort _ _

private theorem pronicFeature_sum {ι : Type*} (T : ℕ) (s : Finset ι) (v : ι → ℕ → ℝ) :
    pronicFeature T (fun n => ∑ i ∈ s, v i n) = ∑ i ∈ s, pronicFeature T (v i) := by
  ext n
  simp [pronicFeature, Finset.sum_mul]

/-- Coherent packet energy in the receiver is the Hilbert packet energy. -/
theorem pronic_packetEnergy {ι : Type*} (T : ℕ) (s : Finset ι) (v : ι → ℕ → ℝ) :
    packetEnergy s (fun i => pronicFeature T (v i)) =
      pronicNorm T (fun n => ∑ i ∈ s, v i n) ^ 2 := by
  rw [packetEnergy, ← pronicFeature_sum, norm_pronicFeature_sq]

/-- Sharp centered exceptional-source bound for the actual pronic receiver. -/
theorem pronic_deletion_centered {ι : Type*} [DecidableEq ι]
    (T : ℕ) (s e : Finset ι) (v : ι → ℕ → ℝ) :
    (pronicNorm T (fun n => ∑ i ∈ s \ e, v i n) ^ 2 -
      pronicNorm T (fun n => ∑ i ∈ s, v i n) ^ 2 -
      pronicNorm T (fun n => ∑ i ∈ s ∩ e, v i n) ^ 2) ^ 2 ≤
      4 * pronicNorm T (fun n => ∑ i ∈ s, v i n) ^ 2 *
        pronicNorm T (fun n => ∑ i ∈ s ∩ e, v i n) ^ 2 := by
  simpa only [pronic_packetEnergy] using
    packetEnergy_deletion_centered s e (fun i => pronicFeature T (v i))

/-- Receiver loss forces cardinality-weighted energy among the exceptional rows. -/
theorem pronic_deletion_cardinality {ι : Type*} [DecidableEq ι]
    (T : ℕ) (s e : Finset ι) (v : ι → ℕ → ℝ) :
    (pronicNorm T (fun n => ∑ i ∈ s, v i n) -
      pronicNorm T (fun n => ∑ i ∈ s \ e, v i n)) ^ 2 ≤
      ((s ∩ e).card : ℝ) * ∑ i ∈ s ∩ e, pronicNorm T (v i) ^ 2 := by
  simpa only [pronic_packetEnergy, norm_pronicFeature_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pronicNorm_nonneg _ _)] using
    packetEnergy_deletion_cardinality s e (fun i => pronicFeature T (v i))

end
end GaloisForLFunctions.BezoutValuationIncidence

#print axioms GaloisForLFunctions.BezoutValuationIncidence.pronic_deletion_centered
#print axioms GaloisForLFunctions.BezoutValuationIncidence.pronic_deletion_cardinality
