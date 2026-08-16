import GaloisForLFunctions.RHTower.Matveev.PerturbedPower

/-!
# The approximate kernel of the auxiliary construction

With an exactly vanishing relation the auxiliary matrix kernel makes every normalized derivative of
the auxiliary exponential polynomial vanish at every sample.  With a *small* form the same kernel
leaves exactly one residue, proportional to the form itself:

```text
| Σ_m η_m (b_pivot ω_m)^k e^{ω_m s} |  ≤  k M^{k−1} |Λ| · Σ_m |η_m| |m_pivot| e^{ω_m s}.
```

The exact construction is the case `Λ = 0`.  Everything downstream — extrapolation, the zero
estimate, and the terminal contradiction — has to carry this one residue, and the effective bound is
the statement that it cannot stay this small.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The approximate kernel estimate.**  If the exact-normalization combination vanishes, the
normalized frequency combination is bounded by the size of the form. -/
theorem abs_perturbedSum_le (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η : ι → ℝ) (w : ι → ℝ) {M : ℝ}
    (h₁ : ∀ t, |(b pivot : ℝ) * primeLogForm p (m t)| ≤ M)
    (h₂ : ∀ t, |directionForm p b pivot (m t)| ≤ M)
    (hw : ∀ t, 0 ≤ w t) (k : ℕ)
    (hker : ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t = 0) :
    |∑ t, η t * ((b pivot : ℝ) * primeLogForm p (m t)) ^ k * w t|
      ≤ (k : ℝ) * M ^ (k - 1) * |primeLogForm p b|
        * ∑ t, |η t| * |((m t) pivot : ℝ)| * w t := by
  have hdiff : ∑ t, η t * ((b pivot : ℝ) * primeLogForm p (m t)) ^ k * w t
      = ∑ t, η t * (((b pivot : ℝ) * primeLogForm p (m t)) ^ k
          - (directionForm p b pivot (m t)) ^ k) * w t := by
    have hsum : ∑ t, η t * (((b pivot : ℝ) * primeLogForm p (m t)) ^ k
          - (directionForm p b pivot (m t)) ^ k) * w t
        = (∑ t, η t * ((b pivot : ℝ) * primeLogForm p (m t)) ^ k * w t)
          - ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hsum, hker, sub_zero]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hpow := abs_pivotFrequency_pow_sub_directionForm_pow_le p b pivot (m t) (h₁ t) (h₂ t) k
  have hterm : |η t * (((b pivot : ℝ) * primeLogForm p (m t)) ^ k
        - (directionForm p b pivot (m t)) ^ k) * w t|
      = |η t| * |((b pivot : ℝ) * primeLogForm p (m t)) ^ k
          - (directionForm p b pivot (m t)) ^ k| * w t := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hw t)]
  rw [hterm]
  have hbound : |η t| * |((b pivot : ℝ) * primeLogForm p (m t)) ^ k
        - (directionForm p b pivot (m t)) ^ k| * w t
      ≤ |η t| * ((k : ℝ) * M ^ (k - 1) * (|((m t) pivot : ℝ)| * |primeLogForm p b|)) * w t := by
    refine mul_le_mul_of_nonneg_right ?_ (hw t)
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  refine hbound.trans (le_of_eq ?_)
  ring

/-- **The exact case.**  With a vanishing form the residue is zero: the classical statement that the
auxiliary kernel annihilates every normalized derivative. -/
theorem perturbedSum_eq_zero_of_form_eq_zero (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η : ι → ℝ) (w : ι → ℝ) {M : ℝ}
    (h₁ : ∀ t, |(b pivot : ℝ) * primeLogForm p (m t)| ≤ M)
    (h₂ : ∀ t, |directionForm p b pivot (m t)| ≤ M)
    (hw : ∀ t, 0 ≤ w t) (k : ℕ)
    (hker : ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t = 0)
    (hzero : primeLogForm p b = 0) :
    ∑ t, η t * ((b pivot : ℝ) * primeLogForm p (m t)) ^ k * w t = 0 := by
  have h := abs_perturbedSum_le p b pivot m η w h₁ h₂ hw k hker
  rw [hzero, abs_zero, mul_zero, zero_mul] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end GaloisForLFunctions.RHTower.Matveev
