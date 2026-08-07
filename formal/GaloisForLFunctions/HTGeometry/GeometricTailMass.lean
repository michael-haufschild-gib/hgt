import Mathlib.Probability.Distributions.Geometric

/-!
# The tail mass of a geometric law

A geometric law with success probability `p` needs at least `m` further failures with probability
exactly `(1 - p)^m`.  The proof is the one-step recursion `μ {k | m ≤ k} = μ {m} + μ {k | m+1 ≤ k}`
solved along the atoms, so it needs no summation of the tail series.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

/-- **The geometric tail mass is a power of the failure probability.** -/
theorem geometricMeasure_Ici {p : unitInterval} (hp : p ≠ 0) (m : ℕ) :
    geometricMeasure p {k : ℕ | m ≤ k} = ENNReal.ofReal ((1 - (p : ℝ)) ^ m) := by
  have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by
    have := p.2.2
    linarith
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  induction m with
  | zero =>
      have huniv : {k : ℕ | 0 ≤ k} = Set.univ := by
        ext k
        simp
      rw [huniv, pow_zero, ENNReal.ofReal_one]
      exact measure_univ
  | succ m ih =>
      have hsplit : {k : ℕ | m ≤ k} = {m} ∪ {k : ℕ | m + 1 ≤ k} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        omega
      have hdisj : Disjoint ({m} : Set ℕ) {k : ℕ | m + 1 ≤ k} := by
        rw [Set.disjoint_left]
        intro a ha hb
        rw [Set.mem_singleton_iff] at ha
        rw [Set.mem_setOf_eq] at hb
        omega
      have hunion : geometricMeasure p {k : ℕ | m ≤ k} =
          geometricMeasure p {m} + geometricMeasure p {k : ℕ | m + 1 ≤ k} := by
        rw [hsplit, measure_union hdisj MeasurableSet.of_discrete]
      rw [ih, geometricMeasure_singleton hp] at hunion
      have hid : ENNReal.ofReal ((1 - (p : ℝ)) ^ m) =
          ENNReal.ofReal ((1 - (p : ℝ)) ^ m * (p : ℝ)) +
            ENNReal.ofReal ((1 - (p : ℝ)) ^ (m + 1)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      exact WithTop.add_left_cancel ENNReal.ofReal_ne_top (hunion.symm.trans hid)

end GaloisForLFunctions.HTGeometry
