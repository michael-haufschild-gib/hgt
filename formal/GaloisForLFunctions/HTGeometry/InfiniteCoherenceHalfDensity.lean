import GaloisForLFunctions.HTGeometry.CoherenceHalfDensity
import GaloisForLFunctions.HTGeometry.CoherenceLocalTailSaturation

/-!
# Infinite half-density coherence identities

This module extends the pointwise dephasing identities to countable summable
half-density carriers.  It proves the exact squared-distance and overlap
formulas used by the coherence-local saturation theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every signed half-density has pointwise squared mass `p`. -/
theorem booleanHalfDensity_sq {I : Type*} (p : I → ℝ) (epsilon : I → Bool)
    (hp : ∀ i, 0 ≤ p i) (i : I) :
    booleanHalfDensity p epsilon i ^ (2 : ℕ) = p i := by
  rw [booleanHalfDensity]
  cases epsilon i <;> simp [primeDirichletRealSign]
  all_goals nlinarith [Real.sq_sqrt (hp i)]

/-- Pointwise squared Hilbert distance is four times the diagonal mass exactly
on mismatching signs. -/
theorem booleanHalfDensity_sub_sq {I : Type*} (p : I → ℝ)
    (a b : I → Bool) (i : I) :
    (booleanHalfDensity p a i - booleanHalfDensity p b i) ^ (2 : ℕ) =
      if a i = b i then 0 else 4 * Real.sqrt (p i) ^ (2 : ℕ) := by
  rw [booleanHalfDensity, booleanHalfDensity]
  cases a i <;> cases b i <;>
    simp [primeDirichletRealSign] <;> ring

/-- Exact infinite-carrier form of the half-density distance identity. -/
theorem weightedOrientationDistanceSq_sqrt_eq_halfDensity_sub_sq
    {I : Type*} (p : I → ℝ) (a b : I → Bool) :
    weightedOrientationDistanceSq (fun i => Real.sqrt (p i)) a b =
      ∑' i, (booleanHalfDensity p a i - booleanHalfDensity p b i) ^ (2 : ℕ) := by
  unfold weightedOrientationDistanceSq
  congr 1
  funext i
  exact (booleanHalfDensity_sub_sq p a b i).symm

/-- Total squared mass of every sign lift equals the total diagonal mass. -/
theorem tsum_booleanHalfDensity_sq
    {I : Type*} (p : I → ℝ) (epsilon : I → Bool) (hp : ∀ i, 0 ≤ p i) :
    (∑' i, booleanHalfDensity p epsilon i ^ (2 : ℕ)) = ∑' i, p i := by
  apply tsum_congr
  exact booleanHalfDensity_sq p epsilon hp

/-- Every sign lift of a probability mass has unit squared norm. -/
theorem tsum_booleanHalfDensity_sq_eq_one
    {I : Type*} (p : I → ℝ) (epsilon : I → Bool) (hp : ∀ i, 0 ≤ p i)
    (hprob : (∑' i, p i) = 1) :
    (∑' i, booleanHalfDensity p epsilon i ^ (2 : ℕ)) = 1 := by
  rw [tsum_booleanHalfDensity_sq p epsilon hp, hprob]

/-- Pointwise overlap equals mass minus twice the mass on a sign mismatch. -/
theorem booleanHalfDensity_overlap_pointwise
    {I : Type*} (p : I → ℝ) (a b : I → Bool) (hp : ∀ i, 0 ≤ p i) (i : I) :
    booleanHalfDensity p a i * booleanHalfDensity p b i =
      p i - 2 * (if a i ≠ b i then p i else 0) := by
  rw [booleanHalfDensity, booleanHalfDensity]
  cases a i <;> cases b i <;>
    simp [primeDirichletRealSign] <;>
    nlinarith [Real.sq_sqrt (hp i)]

/-- Exact infinite-carrier overlap formula for every summable nonnegative mass. -/
theorem tsum_booleanHalfDensity_overlap
    {I : Type*} (p : I → ℝ) (a b : I → Bool) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) :
    (∑' i, booleanHalfDensity p a i * booleanHalfDensity p b i) =
      (∑' i, p i) - 2 * ∑' i, if a i ≠ b i then p i else 0 := by
  classical
  let q : I → ℝ := fun i => if a i ≠ b i then p i else 0
  have hq : Summable q := by
    have hqnonneg : ∀ i, 0 ≤ q i := by
      intro i
      by_cases h : a i ≠ b i
      · simp [q, h, hp i]
      · have heq : a i = b i := not_ne_iff.mp h
        simp [q, heq]
    have hqle : ∀ i, q i ≤ p i := by
      intro i
      by_cases h : a i ≠ b i
      · simp [q, h]
      · have heq : a i = b i := not_ne_iff.mp h
        simp [q, heq, hp i]
    exact Summable.of_nonneg_of_le hqnonneg hqle hsum
  calc
    (∑' i, booleanHalfDensity p a i * booleanHalfDensity p b i) =
        ∑' i, (p i - 2 * q i) := by
      apply tsum_congr
      intro i
      exact booleanHalfDensity_overlap_pointwise p a b hp i
    _ = (∑' i, p i) - ∑' i, 2 * q i := hsum.tsum_sub (hq.mul_left 2)
    _ = (∑' i, p i) - 2 * ∑' i, q i := by rw [tsum_mul_left]
    _ = (∑' i, p i) - 2 * ∑' i, if a i ≠ b i then p i else 0 := rfl

/-- Probability-normalized overlap is one minus twice the mismatch mass. -/
theorem tsum_booleanHalfDensity_overlap_eq_one_sub
    {I : Type*} (p : I → ℝ) (a b : I → Bool) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (hprob : (∑' i, p i) = 1) :
    (∑' i, booleanHalfDensity p a i * booleanHalfDensity p b i) =
      1 - 2 * ∑' i, if a i ≠ b i then p i else 0 := by
  rw [tsum_booleanHalfDensity_overlap p a b hp hsum, hprob]

end

end GaloisForLFunctions.HTGeometry
