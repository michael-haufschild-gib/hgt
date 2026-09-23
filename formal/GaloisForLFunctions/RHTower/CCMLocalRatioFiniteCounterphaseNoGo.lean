import GaloisForLFunctions.RHTower.CCMLocalRatioCompleted

/-!
# Finite factorized counterphases cannot cancel the local-ratio anomaly

A finite family of local scalar channels can make its aggregate first jet vanish.  It cannot at the
same time remove the quadratic covariance anomaly: the surviving coefficient is one half of the sum
of the squared real first-jet charges.  Thus any repair within this factorized scalar class must
be replaced by a direct nonfactorized pair (or higher) interaction before scalarization.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter
open scoped Topology

/-- Neutralizing the aggregate linear charge of finitely many factorized local channels leaves the
sum-of-squares quadratic covariance anomaly. -/
theorem tendsto_covarianceAnomaly_div_sq_of_neutral_imaginary {ι : Type*} [DecidableEq ι]
    {u : ι → ℝ → ℂ} {b : ι → ℝ} (hu : ∀ v, u v 0 = 1)
    (hd : ∀ v, HasDerivAt (u v) (-Complex.I * ((b v : ℝ) : ℂ)) 0) (s : Finset ι)
    (hneutral : ∑ v ∈ s, b v = 0) :
    Tendsto (fun t : ℝ => covarianceAnomaly s u t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((((∑ v ∈ s, b v ^ (2 : ℕ)) / 2 : ℝ) : ℂ))) := by
  have h := tendsto_covarianceAnomaly_div_sq_of_imaginary hu hd s
  rw [hneutral] at h
  have hvalue : (((∑ v ∈ s, b v ^ (2 : ℕ)) / 2 : ℝ) : ℂ)
      = -((((0 : ℝ) ^ (2 : ℕ) - ∑ v ∈ s, b v ^ (2 : ℕ)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hvalue]
  exact h

/-- A nonzero finite real first-jet family has strictly positive total square. -/
theorem sum_sq_pos_of_exists_mem_ne_zero {ι : Type*} [DecidableEq ι] {b : ι → ℝ}
    (s : Finset ι) (hnonzero : ∃ v ∈ s, b v ≠ 0) : 0 < ∑ v ∈ s, b v ^ (2 : ℕ) := by
  obtain ⟨v, hv, hb⟩ := hnonzero
  refine lt_of_lt_of_le (sq_pos_of_ne_zero hb) ?_
  exact Finset.single_le_sum (fun w _ => sq_nonneg (b w)) hv

/-- Under a neutral aggregate first jet, every nontrivial finite factorized family has a strictly
positive quadratic covariance-anomaly coefficient. -/
theorem exists_pos_quadratic_covarianceAnomaly_of_neutral_imaginary
    {ι : Type*} [DecidableEq ι] {u : ι → ℝ → ℂ} {b : ι → ℝ}
    (hu : ∀ v, u v 0 = 1)
    (hd : ∀ v, HasDerivAt (u v) (-Complex.I * ((b v : ℝ) : ℂ)) 0) (s : Finset ι)
    (hneutral : ∑ v ∈ s, b v = 0) (hnonzero : ∃ v ∈ s, b v ≠ 0) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℝ => covarianceAnomaly s u t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ))
        (𝓝 (L : ℂ)) := by
  refine ⟨(∑ v ∈ s, b v ^ (2 : ℕ)) / 2, ?_, ?_⟩
  · exact half_pos (sum_sq_pos_of_exists_mem_ne_zero s hnonzero)
  · exact tendsto_covarianceAnomaly_div_sq_of_neutral_imaginary hu hd s hneutral

end GaloisForLFunctions.RHTower
