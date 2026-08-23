import GaloisForLFunctions.RHTower.Sieve.TypeIICorrelation

/-!
# The type-II energy bound

Cauchy--Schwarz on the long variable, the correlation expansion, and the difference-phase estimate
combine into a single bound for the type-II bilinear form: the diagonal contributes the length of
the long range, and every off-diagonal pair contributes a curved-phase sum at the scale
`T·|r/m₁ − r/m₂|`.
-/

namespace RHTower.Sieve

open Complex RHTower

noncomputable section

/-- The unimodular summand of the type-II form. -/
def ndExp (T r : ℝ) (m d : ℕ) : ℂ := phaseExp (nearDiagonalPhase T r ((m : ℝ) * (d : ℝ)))

theorem norm_ndExp (T r : ℝ) (m d : ℕ) : ‖ndExp T r m d‖ = 1 := by
  rw [ndExp, phaseExp, Complex.norm_exp]
  simp

/-- The diagonal correlation is the length of the long range. -/
theorem sum_corr_self (T r : ℝ) (m A B : ℕ) :
    (∑ d ∈ Finset.Ico A B, ndExp T r m d * (starRingEnd ℂ) (ndExp T r m d))
      = ((B - A : ℕ) : ℂ) := by
  have hterm : ∀ d : ℕ, ndExp T r m d * (starRingEnd ℂ) (ndExp T r m d) = 1 := by
    intro d
    rw [ndExp, phaseExp_mul_conj, sub_self, phaseExp]
    simp
  rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    mul_one]

/-- The correlation is conjugate-symmetric in the pair. -/
theorem sum_corr_conj (T r : ℝ) (m₁ m₂ A B : ℕ) :
    (∑ d ∈ Finset.Ico A B, ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d))
      = (starRingEnd ℂ)
          (∑ d ∈ Finset.Ico A B, ndExp T r m₂ d * (starRingEnd ℂ) (ndExp T r m₁ d)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- **The off-diagonal correlation bound**, in either order of the pair. -/
theorem norm_sum_corr_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {m₁ m₂ A B : ℕ}
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂) (hA : 1 ≤ A)
    (h4₁ : 4 * (r / m₁) ≤ (A : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (A : ℝ))
    (hlam : curvedLambda (T * |r / m₁ - r / m₂|) (A : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico A B, ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d)‖
      ≤ 2500 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * |r / m₁ - r / m₂|))
            * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hm₁0 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hm₂0 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcast : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hlt
    have hslt : r / m₂ < r / m₁ := by
      rw [div_lt_div_iff₀ hm₂0 hm₁0]
      nlinarith [hr, hcast]
    have habs : |r / m₁ - r / m₂| = r / m₁ - r / m₂ := abs_of_pos (by linarith)
    rw [habs] at hlam ⊢
    exact norm_sum_correlation_le hT hr hm₁ hlt hA h4₁ hlam
  · have hcast : (m₂ : ℝ) < (m₁ : ℝ) := by exact_mod_cast hgt
    have hslt : r / m₁ < r / m₂ := by
      rw [div_lt_div_iff₀ hm₁0 hm₂0]
      nlinarith [hr, hcast]
    have habs : |r / m₁ - r / m₂| = r / m₂ - r / m₁ := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [habs] at hlam ⊢
    rw [sum_corr_conj, RCLike.norm_conj]
    exact norm_sum_correlation_le hT hr hm₂ hgt hA h4₂ hlam

/-- **The type-II energy bound.** -/
theorem norm_typeII_sq_le (T r : ℝ) (A B : ℕ) (Ms : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B, a d * ∑ m ∈ Ms, b m * ndExp T r m d‖ ^ 2
      ≤ (∑ d ∈ Finset.Ico A B, ‖a d‖ ^ 2)
        * ∑ m₁ ∈ Ms, ∑ m₂ ∈ Ms, ‖b m₁‖ * ‖b m₂‖
            * ‖∑ d ∈ Finset.Ico A B, ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d)‖ := by
  refine le_trans (norm_bilinear_sq_le (Finset.Ico A B) a
    (fun d => ∑ m ∈ Ms, b m * ndExp T r m d)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun d _ => sq_nonneg _)
  exact sum_normSq_inner_le (Finset.Ico A B) Ms b (fun d m => ndExp T r m d)

end

end RHTower.Sieve
