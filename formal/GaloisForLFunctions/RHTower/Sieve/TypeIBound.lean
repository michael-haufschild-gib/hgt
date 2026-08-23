import GaloisForLFunctions.RHTower.Sieve.TypeIIEnergyBound

/-!
# The type-I bound

For a fixed short variable `d` the inner sum of a type-I form is a near-diagonal sum at the scaled
offset `r/d`, by the dilation identity.  The type-I form is therefore bounded term by term, with no
Cauchy--Schwarz and no new derivative test.
-/

namespace RHTower.Sieve

open Complex RHTower

noncomputable section

theorem sum_ndExp_eq_dilated (T r : ℝ) (d A B : ℕ) :
    (∑ m ∈ Finset.Ico A B, ndExp T r m d)
      = ∑ m ∈ Finset.Ico A B,
          Complex.exp (((2 * Real.pi * nearDiagonalPhase T r ((d : ℝ) * (m : ℝ)) : ℝ) : ℂ)
            * Complex.I) := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ndExp, phaseExp, mul_comm ((m : ℝ)) ((d : ℝ))]

/-- **The type-I inner sum.** -/
theorem norm_sum_ndExp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {d : ℕ} (hd : 1 ≤ d)
    (A B : ℕ) (hA : 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam : nearDiagonalLambda T (r / d) (A : ℝ) ≤ 1) :
    ‖∑ m ∈ Finset.Ico A B, ndExp T r m d‖
      ≤ 2500 * Real.sqrt (T * (r / d) / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * (r / d))) * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [sum_ndExp_eq_dilated]
  exact norm_dilated_nearDiagonalSum_le hT hr hd0 A B hA hrA hlam

/-- **The type-I form.**  Term by term, with the coefficients pulled out. -/
theorem norm_typeI_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (Ds : Finset ℕ) (a : ℕ → ℂ)
    (A B : ℕ) (hA : 1 ≤ A)
    (hd : ∀ d ∈ Ds, 1 ≤ d ∧ r / d ≤ (A : ℝ) ∧ nearDiagonalLambda T (r / d) (A : ℝ) ≤ 1) :
    ‖∑ d ∈ Ds, a d * ∑ m ∈ Finset.Ico A B, ndExp T r m d‖
      ≤ ∑ d ∈ Ds, ‖a d‖
          * (2500 * Real.sqrt (T * (r / d) / (36 * Real.pi * A))
              + 22 * Real.sqrt (36 * Real.pi / (T * (r / d))) * Real.sqrt (((B : ℝ)) ^ 3)) := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun d hdmem => ?_
  obtain ⟨hd1, hrA, hlam⟩ := hd d hdmem
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_ndExp_le hT hr hd1 A B hA hrA hlam)
    (norm_nonneg _)

end

end RHTower.Sieve
