import GaloisForLFunctions.RHTower.Sieve.OffDiagonalCorrelationBounds

/-!
# Hybrid exponent-pair correlation bound

The `(1/2,1/2)` exponent-pair estimate is the second-derivative bound above first-derivative
resonance and Kuzmin--Landau below it.  Combining the regimes replaces the weak reciprocal
square-root remainder by the required full reciprocal remainder.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Above first-derivative resonance, the reciprocal square-root term is absorbed by the growing
second-derivative term on a dyadic block. -/
theorem secondDerivative_reciprocal_term_le_first {Y : ℝ} {P Q : ℕ}
    (hY : 0 < Y) (hP : 1 ≤ P) (hQ2P : Q ≤ 2 * P)
    (hhigh : 1 / 2 < Y / (2 * Real.pi * (P : ℝ) ^ 2)) :
    22 * Real.sqrt (36 * Real.pi / Y) * Real.sqrt ((Q : ℝ) ^ 3)
      ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * P)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hYlower : Real.pi * (P : ℝ) ^ 2 < Y := by
    rw [lt_div_iff₀ (by positivity)] at hhigh
    nlinarith
  have hYsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ Real.pi * (P : ℝ) ^ 2) hYlower.le
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hQ3 : (Q : ℝ) ^ 3 ≤ (2 * (P : ℝ)) ^ 3 := by gcongr
  have hrad : 36 * Real.pi / Y * (Q : ℝ) ^ 3
      ≤ (2500 / 22 : ℝ) ^ 2 * (Y / (36 * Real.pi * P)) := by
    calc
      36 * Real.pi / Y * (Q : ℝ) ^ 3
          ≤ 36 * Real.pi / Y * (2 * (P : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left hQ3 (by positivity)
      _ ≤ (2500 / 22 : ℝ) ^ 2 * (Y / (36 * Real.pi * P)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp
        nlinarith [hYsq]
  have hsqrt := Real.sqrt_le_sqrt hrad
  have hright : Real.sqrt ((2500 / 22 : ℝ) ^ 2 * (Y / (36 * Real.pi * P)))
      = (2500 / 22 : ℝ) * Real.sqrt (Y / (36 * Real.pi * P)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hright] at hsqrt
  calc
    22 * Real.sqrt (36 * Real.pi / Y) * Real.sqrt ((Q : ℝ) ^ 3)
        = 22 * Real.sqrt (36 * Real.pi / Y * (Q : ℝ) ^ 3) := by
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 36 * Real.pi / Y)]
          ring
    _ ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * P)) := by nlinarith [hsqrt]

/-- Uniform `(1/2,1/2)` correlation estimate, obtained by a complete split at first-derivative
resonance. -/
theorem norm_masked_correlation_offdiag_hybrid_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ2P : Q ≤ 2 * P)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂)
    (h4₁ : 4 * (r / m₁) ≤ (P : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (P : ℝ))
    (hlam : curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
      ≤ 5000 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P))
        + 75 * Real.pi * (Q : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|)) + 1 := by
  have hm₁0 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hm₂0 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  have hdivne : r / (m₁ : ℝ) ≠ r / (m₂ : ℝ) := by
    intro heq
    field_simp at heq
    have hcast : (m₁ : ℝ) = (m₂ : ℝ) := by nlinarith
    exact hne (Nat.cast_inj.mp hcast)
  have hY : 0 < T * |r / m₁ - r / m₂| :=
    mul_pos hT (abs_pos.mpr (sub_ne_zero.mpr hdivne))
  have hrec0 : 0 ≤ 75 * Real.pi * (Q : ℝ) ^ 2 /
      (16 * (T * |r / m₁ - r / m₂|)) := by positivity
  by_cases hsmall : T * |r / m₁ - r / m₂| / (2 * Real.pi * (P : ℝ) ^ 2) ≤ 1 / 2
  · have hmain := norm_masked_correlation_offdiag_kuzminLandau_le (Q := Q) hT hr hA hB hP
      hm₁ hm₂ hne h4₁ h4₂ hsmall hY
    exact hmain.trans (by
      nlinarith [Real.sqrt_nonneg
        (T * |r / m₁ - r / m₂| / (36 * Real.pi * (P : ℝ)))])
  · have hmain := norm_masked_correlation_offdiag_secondDeriv_le (Q := Q) hT hr hA hB hP
      hm₁ hm₂ hne h4₁ h4₂ hlam
    have hdom := secondDerivative_reciprocal_term_le_first hY hP hQ2P (lt_of_not_ge hsmall)
    calc
      ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
          ≤ 2500 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P))
            + 22 * Real.sqrt (36 * Real.pi / (T * |r / m₁ - r / m₂|))
              * Real.sqrt ((Q : ℝ) ^ 3) := hmain
      _ ≤ 5000 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P)) := by
        nlinarith [hdom]
      _ ≤ 5000 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P))
          + 75 * Real.pi * (Q : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|)) + 1 := by
        nlinarith

end

end RHTower.Sieve
