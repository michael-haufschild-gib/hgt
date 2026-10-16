import GaloisForLFunctions.HTGeometry.MomentHankelNormalBlocks

/-!
# Polynomial recurrence across singular moment blocks

Consecutive regular heads obey a three-term recurrence even when every
intermediate Hankel pivot vanishes. The diagonal entry is a monic polynomial
whose degree is the entire gap. The edge is the ratio of the two first
surviving moment couplings, so it never vanishes.

Monic division leaves a remainder orthogonal to all but the last row of the
current regular section. The preceding admission spans this complement;
its final coupling determines the remainder exactly.
-/

open Polynomial
namespace HTGeometry
noncomputable section

/-- First surviving coupling of a normal block. -/
def momentBlockCoupling (s : ℕ → ℝ) (n d : ℕ) : ℝ :=
  momentFunctional s (X ^ (n + d - 1) * monicMomentAdmissionPolynomial s n)

/-- Euclidean quotient between the two regular heads of a block. -/
def momentBlockQuotient (s : ℕ → ℝ) (n d : ℕ) : ℝ[X] :=
  monicMomentAdmissionPolynomial s (n + d) /ₘ monicMomentAdmissionPolynomial s n

theorem momentBlockQuotient_monic (s : ℕ → ℝ) (n d : ℕ) :
    (momentBlockQuotient s n d).Monic := by
  unfold momentBlockQuotient Monic
  rw [leadingCoeff_divByMonic_of_monic (monicMomentAdmissionPolynomial_monic s n)]
  · exact (monicMomentAdmissionPolynomial_monic s (n + d)).leadingCoeff
  · simp only [degree_eq_natDegree (monicMomentAdmissionPolynomial_monic _ _).ne_zero,
      monicMomentAdmissionPolynomial_natDegree]
    exact_mod_cast Nat.le_add_right n d

theorem momentBlockQuotient_natDegree (s : ℕ → ℝ) (n d : ℕ) :
    (momentBlockQuotient s n d).natDegree = d := by
  rw [momentBlockQuotient, natDegree_divByMonic _ (monicMomentAdmissionPolynomial_monic s n),
    monicMomentAdmissionPolynomial_natDegree, monicMomentAdmissionPolynomial_natDegree]
  omega

theorem MomentNormalBlock.coupling_ne {s : ℕ → ℝ} {n d : ℕ}
    (h : MomentNormalBlock s n d) : momentBlockCoupling s n d ≠ 0 :=
  h.coupling_ne_zero

/-- Exact transfer between three consecutive regular heads. No scalar
intermediate pivot or positivity assumption is needed. -/
theorem MomentNormalBlock.admission_recurrence {s : ℕ → ℝ} {m d e : ℕ}
    (h₀ : MomentNormalBlock s m d) (h₁ : MomentNormalBlock s (m + d) e) :
    monicMomentAdmissionPolynomial s (m + d + e) =
      momentBlockQuotient s (m + d) e * monicMomentAdmissionPolynomial s (m + d) -
        C (momentBlockCoupling s (m + d) e / momentBlockCoupling s m d) *
          monicMomentAdmissionPolynomial s m := by
  let P := monicMomentAdmissionPolynomial s m
  let Q := monicMomentAdmissionPolynomial s (m + d)
  let T := monicMomentAdmissionPolynomial s (m + d + e)
  let A := momentBlockQuotient s (m + d) e
  let R := T %ₘ Q
  let b := momentBlockCoupling s (m + d) e / momentBlockCoupling s m d
  have hP : P.Monic := monicMomentAdmissionPolynomial_monic _ _
  have hQ : Q.Monic := monicMomentAdmissionPolynomial_monic _ _
  have hA : A.Monic := momentBlockQuotient_monic _ _ _
  have hAd : A.natDegree = e := momentBlockQuotient_natDegree _ _ _
  have hPd : P.degree = (m : WithBot ℕ) := by
    rw [degree_eq_natDegree hP.ne_zero, monicMomentAdmissionPolynomial_natDegree]
  have hQd : Q.degree = ((m + d : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hQ.ne_zero, monicMomentAdmissionPolynomial_natDegree]
  have hdivide : R + Q * A = T := modByMonic_add_div T Q
  have hrows (i : ℕ) (hi : i < m + d) :
      momentFunctional s (X ^ i * R) + momentFunctional s (X ^ i * (Q * A)) = 0 := by
    rw [← momentFunctional_add, ← mul_add, hdivide]
    exact momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero
      h₁.next_regular ⟨i, by omega⟩
  have hzero : R + b • P = 0 := by
    apply momentSectionKernel_eq_zero_of_det_ne_zero h₁.head_regular
    refine ⟨(degree_add_le _ _).trans_lt (max_lt ?_ ?_), ?_⟩
    · exact (degree_modByMonic_lt T hQ).trans_eq hQd
    · apply (degree_smul_le b P).trans_lt
      rw [hPd]
      exact_mod_cast (show m < m + d from Nat.lt_add_of_pos_right h₀.length_pos)
    · intro i hi
      rw [mul_add, momentFunctional_add, mul_smul_comm, momentFunctional_smul]
      have hr := hrows i hi
      by_cases hil : i < m + d - 1
      · have hqa : momentFunctional s (X ^ i * (Q * A)) = 0 := by
          apply momentFunctional_X_pow_mul_mul_eq_zero h₁.vanishing
          intro j hj
          have hj' := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
          rw [hAd] at hj'
          omega
        rw [hqa, add_zero] at hr
        rw [hr, h₀.vanishing i hil, mul_zero, add_zero]
      · have hie : i = m + d - 1 := by omega
        subst i
        have hqa : momentFunctional s (X ^ (m + d - 1) * (Q * A)) =
            momentBlockCoupling s (m + d) e := by
          rw [momentFunctional_X_pow_mul_mul_first h₁.vanishing
            (by rw [hAd]; have := h₀.length_pos; omega), hA.leadingCoeff, one_mul]
          rfl
        rw [hqa] at hr
        change momentFunctional s (X ^ (m + d - 1) * R) +
          b * momentBlockCoupling s m d = 0
        rw [show b * momentBlockCoupling s m d = momentBlockCoupling s (m + d) e from
          div_mul_cancel₀ _ h₀.coupling_ne]
        exact hr
  rw [smul_eq_C_mul] at hzero
  change T = A * Q - C b * P
  linear_combination hzero - hdivide

/-- The Euclidean algorithm recovers the preceding regular head, with a
nonzero scalar normalization supplied by the moment couplings. -/
theorem MomentNormalBlock.admission_remainder {s : ℕ → ℝ} {m d e : ℕ}
    (h₀ : MomentNormalBlock s m d) (h₁ : MomentNormalBlock s (m + d) e) :
    monicMomentAdmissionPolynomial s (m + d + e) %ₘ
        monicMomentAdmissionPolynomial s (m + d) =
      -C (momentBlockCoupling s (m + d) e / momentBlockCoupling s m d) *
        monicMomentAdmissionPolynomial s m := by
  rw [modByMonic_eq_sub_mul_div]
  change monicMomentAdmissionPolynomial s (m + d + e) -
    monicMomentAdmissionPolynomial s (m + d) * momentBlockQuotient s (m + d) e = _
  rw [h₀.admission_recurrence h₁]
  ring

end
end HTGeometry
