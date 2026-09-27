import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Polynomial heat control retaining the full lower spectral rate

Expand about the lower endpoint before applying the factorial bound. Every
binomial term remains in the finite envelope; no fraction of the endpoint
exponential decay is spent on the polynomial weight.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

def shiftedFactorialHeatEnvelope (k : ℕ) (G : {G : ℝ // 0 ≤ G})
    (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (G : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j.factorial : ℝ) / (t : ℝ) ^ j)

theorem shiftedFactorialHeatEnvelope_nonneg (k : ℕ) (G : {G : ℝ // 0 ≤ G})
    (t : {t : ℝ // 0 < t}) : 0 ≤ shiftedFactorialHeatEnvelope k G t := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (pow_nonneg G.property _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (pow_nonneg t.property.le _))

theorem pow_mul_exp_neg_le_shiftedFactorial (k : ℕ) (G : {G : ℝ // 0 ≤ G})
    (t : {t : ℝ // 0 < t}) (A : {A : ℝ // (G : ℝ) ≤ A}) :
    (A : ℝ) ^ k * Real.exp (-((t : ℝ) * (A : ℝ))) ≤
      Real.exp (-((t : ℝ) * (G : ℝ))) * shiftedFactorialHeatEnvelope k G t := by
  let u : ℝ := (A : ℝ) - (G : ℝ)
  have hu : 0 ≤ u := sub_nonneg.mpr A.property
  have he : Real.exp (-((t : ℝ) * (A : ℝ))) =
      Real.exp (-((t : ℝ) * (G : ℝ))) * Real.exp (-((t : ℝ) * u)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [u]
    ring
  calc
    _ = Real.exp (-((t : ℝ) * (G : ℝ))) *
        ∑ j ∈ Finset.range (k + 1),
          (u ^ j * Real.exp (-((t : ℝ) * u))) * (G : ℝ) ^ (k - j) * (k.choose j : ℝ) := by
      rw [he, show (A : ℝ) = u + (G : ℝ) by dsimp only [u]; ring, add_pow,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_right (pow_mul_exp_neg_le t.property j hu)
        (mul_nonneg (pow_nonneg G.property (k - j)) (Nat.cast_nonneg (k.choose j)))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end
end GaloisForLFunctions.HTGeometry
