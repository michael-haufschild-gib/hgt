import GaloisForLFunctions.RHTower.DivisorReesGradedMetric

/-!
# The continued channel is the graded symbol twisted by the divisor

The graded symbol is not a replacement for the continued radical channel: it *is* that channel,
written in the Rees coordinates that divide out the divisor.

Concretely, the ungraded Gram of the continued channel at a divisor point of multiplicity `d` is
the graded Gram conjugated by the diagonal twist `diag(t ^ d, t⁻¹)`.  Conjugation is a congruence,
so it transports positivity in both directions, and it exhibits the completion entry of the
ungraded channel as the graded completion divided by `t ^ (2 : ℕ)`.  That inverse square is exactly the
blow-up that forbids a uniformly bounded ungraded completion, and it is exactly what the twist
removes.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The Rees divisor twist: the diagonal change of coordinates that turns graded data into
ungraded data at a divisor point of multiplicity `d`. -/
def divisorTwist (d : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t ^ d, 0; 0, t⁻¹]

theorem divisorTwist_transpose (d : ℕ) (t : ℝ) :
    (divisorTwist d t)ᵀ = divisorTwist d t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [divisorTwist]

/-- **The continued channel is the graded symbol twisted by the divisor.**  The ungraded Gram at a
divisor point, with completion entry `C / t ^ (2 : ℕ)`, is the congruence of the graded Gram with
completion `C` by the divisor twist. -/
theorem divisorReesGram_monomial_eq_twist_graded (d : ℕ) {t : ℝ} (ht : t ≠ 0) (C : ℝ) :
    divisorReesGram (monomialDivisorOverlap d t) (monomialDivisorFisherNumerator d t)
        (C / t ^ (2 : ℕ))
      = divisorTwist d t *
          divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t) C *
          divisorTwist d t := by
  have hpow : ∀ m : ℕ, 0 < m → t ^ m * t⁻¹ = t ^ (m - 1) := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [Nat.succ_sub_one, pow_succ, mul_assoc, mul_inv_cancel₀ ht, mul_one]
  have hoff : (d : ℝ) * t ^ (d - 1) = t ^ d * (d : ℝ) * t⁻¹ := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [mul_comm (t ^ d) ((d : ℝ)), mul_assoc, hpow d hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [divisorReesGram, divisorTwist, Matrix.mul_apply, Fin.sum_univ_succ,
      monomialDivisorOverlap, monomialDivisorFisherNumerator,
      gradedDivisorOverlap_eq_one ht, gradedDivisorFisherNumerator_eq ht, hoff] <;>
    field_simp

/-- **Positivity transports along the twist.**  Whenever the graded Gram is positive, so is the
ungraded Gram whose completion entry is the graded one divided by `t ^ (2 : ℕ)`. -/
theorem divisorReesGram_monomial_posSemidef (d : ℕ) {t : ℝ} (ht : t ≠ 0) {C : ℝ}
    (hC : (divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
      C).PosSemidef) :
    (divisorReesGram (monomialDivisorOverlap d t) (monomialDivisorFisherNumerator d t)
      (C / t ^ (2 : ℕ))).PosSemidef := by
  rw [divisorReesGram_monomial_eq_twist_graded d ht C]
  have h := hC.conjTranspose_mul_mul_same (divisorTwist d t)
  rwa [show (divisorTwist d t)ᴴ = divisorTwist d t from divisorTwist_transpose d t] at h

/-- **The continued channel is positive at every point off the divisor.**  Taking the graded
completion supplied by the graded metric, the ungraded channel is positive with completion
`d ^ (2 : ℕ) / t ^ (2 : ℕ)` — the inverse square that no uniform bound can absorb, and exactly the quantity the
twist removes. -/
theorem divisorReesGram_monomial_posSemidef_sq (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (divisorReesGram (monomialDivisorOverlap d t) (monomialDivisorFisherNumerator d t)
      ((d : ℝ) ^ (2 : ℕ) / t ^ (2 : ℕ))).PosSemidef :=
  divisorReesGram_monomial_posSemidef d ht (gradedDivisorReesGram_posSemidef d ht)

end

end RHTower
