import GaloisForLFunctions.RHTower.Sieve.CurvedPhaseBlockSum

/-!
# The type-II bilinear form: Cauchy--Schwarz and the correlation expansion

The type-II half of Vaughan's identity is a bilinear form `Σ_d a_d Σ_m b_m z_{d,m}`.  Cauchy--Schwarz
in `d` removes the unknown coefficients `a_d`, and expanding the resulting square exchanges the
roles of the variables: what remains is a correlation sum `Σ_d z_{d,m₁} conj z_{d,m₂}` over the
long variable, for each pair `(m₁, m₂)` of the short one.  Nothing about the phases is used here.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **Cauchy--Schwarz on the outer variable.** -/
theorem norm_bilinear_sq_le (D : Finset ℕ) (a G : ℕ → ℂ) :
    ‖∑ d ∈ D, a d * G d‖ ^ 2
      ≤ (∑ d ∈ D, ‖a d‖ ^ 2) * (∑ d ∈ D, ‖G d‖ ^ 2) := by
  have htri : ‖∑ d ∈ D, a d * G d‖ ≤ ∑ d ∈ D, ‖a d‖ * ‖G d‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun d _ => norm_mul _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D (fun d => ‖a d‖) (fun d => ‖G d‖)
  have hnn : (0 : ℝ) ≤ ∑ d ∈ D, ‖a d‖ * ‖G d‖ :=
    Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [htri, hcs, norm_nonneg (∑ d ∈ D, a d * G d)]

/-- **The correlation expansion.**  The energy of the inner sums is the double correlation sum. -/
theorem sum_normSq_inner_eq (D M : Finset ℕ) (b : ℕ → ℂ) (z : ℕ → ℕ → ℂ) :
    ((∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ)
      = ∑ m₁ ∈ M, ∑ m₂ ∈ M,
          b m₁ * (starRingEnd ℂ) (b m₂) * ∑ d ∈ D, z d m₁ * (starRingEnd ℂ) (z d m₂) := by
  have hstep : ∀ d : ℕ, ((‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ)
      = ∑ m₁ ∈ M, ∑ m₂ ∈ M,
          (b m₁ * (starRingEnd ℂ) (b m₂)) * (z d m₁ * (starRingEnd ℂ) (z d m₂)) := by
    intro d
    have hsq : ((‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ)
        = (∑ m ∈ M, b m * z d m) * (starRingEnd ℂ) (∑ m ∈ M, b m * z d m) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    rw [map_mul]
    ring
  calc ((∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ)
      = ∑ d ∈ D, ((‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ) := Complex.ofReal_sum _ _
    _ = ∑ d ∈ D, ∑ m₁ ∈ M, ∑ m₂ ∈ M,
          (b m₁ * (starRingEnd ℂ) (b m₂)) * (z d m₁ * (starRingEnd ℂ) (z d m₂)) :=
        Finset.sum_congr rfl fun d _ => hstep d
    _ = ∑ m₁ ∈ M, ∑ m₂ ∈ M, ∑ d ∈ D,
          (b m₁ * (starRingEnd ℂ) (b m₂)) * (z d m₁ * (starRingEnd ℂ) (z d m₂)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    _ = ∑ m₁ ∈ M, ∑ m₂ ∈ M,
          b m₁ * (starRingEnd ℂ) (b m₂) * ∑ d ∈ D, z d m₁ * (starRingEnd ℂ) (z d m₂) :=
        Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
          (Finset.mul_sum _ _ _).symm

/-- **The energy bound.**  The energy of the inner sums is at most the weighted total of the
correlation sums. -/
theorem sum_normSq_inner_le (D M : Finset ℕ) (b : ℕ → ℂ) (z : ℕ → ℕ → ℂ) :
    (∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2)
      ≤ ∑ m₁ ∈ M, ∑ m₂ ∈ M,
          ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ D, z d m₁ * (starRingEnd ℂ) (z d m₂)‖ := by
  have hnn : (0 : ℝ) ≤ ∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2 :=
    Finset.sum_nonneg fun d _ => sq_nonneg _
  have heq := sum_normSq_inner_eq D M b z
  have hnorm : (∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2)
      = ‖((∑ d ∈ D, ‖∑ m ∈ M, b m * z d m‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, heq]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m₁ _ => ?_
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m₂ _ => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj]

end

end RHTower.Sieve
