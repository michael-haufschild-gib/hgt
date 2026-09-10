import GaloisForLFunctions.HTGeometry.GomesPolynomialDifferentialDegree

/-!
# Unique division by a polynomial connection operator

Every polynomial forcing splits into a first-order connection output and a unique
remainder below the coefficient degree. Ordinary polynomial division supplies the
induction step; its quotient derivative strictly lowers the unresolved forcing degree.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every forcing admits differential division with a remainder below the coefficient degree. -/
theorem gomesPolynomialFirstOrder_division_exists
    (A : GomesNonconstantPolynomialCoefficient) (Q : ℝ[X]) :
    ∃ B R : ℝ[X], R.natDegree < A.val.natDegree ∧
      Q = gomesPolynomialFirstOrderOperator A.val B + R := by
  have hA := gomesNonconstantPolynomialCoefficient_degree_pos A
  have hall : ∀ n : ℕ, ∀ Q : ℝ[X], Q.natDegree = n →
      ∃ B R : ℝ[X], R.natDegree < A.val.natDegree ∧
        Q = gomesPolynomialFirstOrderOperator A.val B + R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hQ
      by_cases hsmall : Q.natDegree < A.val.natDegree
      · exact ⟨0, Q, hsmall, by simp [gomesPolynomialFirstOrderOperator]⟩
      · have hle : A.val.natDegree ≤ Q.natDegree := le_of_not_gt hsmall
        have hQpos : 0 < Q.natDegree := hA.trans_le hle
        let S := Q / A.val
        let Z := Q % A.val + S.derivative
        have hS : S.natDegree ≤ Q.natDegree :=
          natDegree_le_natDegree (degree_div_le Q A.val)
        have hSd : S.derivative.natDegree < Q.natDegree := by
          by_cases hs : S.natDegree = 0
          · rw [derivative_of_natDegree_zero hs, natDegree_zero]
            exact hQpos
          · exact (natDegree_derivative_lt hs).trans_le hS
        have hZlt : Z.natDegree < Q.natDegree :=
          (natDegree_add_le _ _).trans_lt
            (max_lt ((natDegree_mod_lt Q (ne_of_gt hA)).trans_le hle) hSd)
        obtain ⟨B, R, hR, hZ⟩ := ih Z.natDegree (hQ ▸ hZlt) Z rfl
        refine ⟨B - S, R, hR, ?_⟩
        have hdiv := EuclideanDomain.div_add_mod Q A.val
        change A.val * S + Q % A.val = Q at hdiv
        change Q % A.val + S.derivative = gomesPolynomialFirstOrderOperator A.val B + R at hZ
        unfold gomesPolynomialFirstOrderOperator at hZ ⊢
        simp only [derivative_sub, mul_sub]
        linear_combination -hdiv + hZ
  exact hall Q.natDegree Q rfl

/-- Assembling a polynomial connection output and a low-degree remainder is linear. -/
def gomesPolynomialDifferentialAssembly (A : GomesNonconstantPolynomialCoefficient) :
    (ℝ[X] × degreeLT ℝ A.val.natDegree) →ₗ[ℝ] ℝ[X] where
  toFun BR := gomesPolynomialFirstOrderOperator A.val BR.1 + BR.2.val
  map_add' := by
    rintro ⟨B, R⟩ ⟨D, S⟩
    change gomesPolynomialFirstOrderOperator A.val (B + D) + (R.val + S.val) = _
    simp only [gomesPolynomialFirstOrderOperator, derivative_add, mul_add]
    ring
  map_smul' := by
    intro r BR
    change gomesPolynomialFirstOrderOperator A.val (r • BR.1) + r • BR.2.val = _
    simp [gomesPolynomialFirstOrderOperator, smul_sub, smul_add]

/-- The remainder and the source polynomial are jointly unique. -/
theorem gomesPolynomialDifferentialAssembly_injective (A : GomesNonconstantPolynomialCoefficient) :
    Function.Injective (gomesPolynomialDifferentialAssembly A) := by
  rintro ⟨B, R⟩ ⟨D, S⟩ h
  change gomesPolynomialFirstOrderOperator A.val B + R.val =
    gomesPolynomialFirstOrderOperator A.val D + S.val at h
  have hd : gomesPolynomialFirstOrderOperator A.val (B - D) = S.val - R.val := by
    unfold gomesPolynomialFirstOrderOperator at h ⊢
    simp only [derivative_sub, mul_sub]
    linear_combination h
  have hz := (gomesPolynomialFirstOrder_low_degree_iff A (B - D)).mp
    (hd ▸ (degreeLT ℝ A.val.natDegree).sub_mem S.property R.property)
  have hb := sub_eq_zero.mp hz
  subst D
  exact Prod.ext rfl (Subtype.ext (add_left_cancel h))

/-- Differential assembly covers every polynomial forcing. -/
theorem gomesPolynomialDifferentialAssembly_surjective (A : GomesNonconstantPolynomialCoefficient) :
    Function.Surjective (gomesPolynomialDifferentialAssembly A) := by
  intro Q
  obtain ⟨B, R, hR, hQ⟩ := gomesPolynomialFirstOrder_division_exists A Q
  exact ⟨(B, ⟨R, (gomesPolynomial_below_coefficient_degree_iff A R).mpr hR⟩), hQ.symm⟩

/-- Differential division is an actual linear equivalence, including its unique source and remainder. -/
def gomesPolynomialDifferentialDivisionEquiv (A : GomesNonconstantPolynomialCoefficient) :
    ℝ[X] ≃ₗ[ℝ] (ℝ[X] × degreeLT ℝ A.val.natDegree) :=
  (LinearEquiv.ofBijective (gomesPolynomialDifferentialAssembly A)
    ⟨gomesPolynomialDifferentialAssembly_injective A,
      gomesPolynomialDifferentialAssembly_surjective A⟩).symm

/-- The exact decomposition recovered by differential division. -/
theorem gomesPolynomialDifferentialDivisionEquiv_reconstruct
    (A : GomesNonconstantPolynomialCoefficient) (Q : ℝ[X]) :
    Q = gomesPolynomialFirstOrderOperator A.val (gomesPolynomialDifferentialDivisionEquiv A Q).1 +
      (gomesPolynomialDifferentialDivisionEquiv A Q).2.val :=
  ((LinearEquiv.ofBijective (gomesPolynomialDifferentialAssembly A)
    ⟨gomesPolynomialDifferentialAssembly_injective A,
      gomesPolynomialDifferentialAssembly_surjective A⟩).apply_symm_apply Q).symm

/-- Dividing an assembled source and remainder recovers that same pair. -/
theorem gomesPolynomialDifferentialDivisionEquiv_assemble
    (A : GomesNonconstantPolynomialCoefficient) (B : ℝ[X]) (R : degreeLT ℝ A.val.natDegree) :
    gomesPolynomialDifferentialDivisionEquiv A (gomesPolynomialFirstOrderOperator A.val B + R.val) =
      (B, R) :=
  (LinearEquiv.ofBijective (gomesPolynomialDifferentialAssembly A)
    ⟨gomesPolynomialDifferentialAssembly_injective A,
      gomesPolynomialDifferentialAssembly_surjective A⟩).symm_apply_apply (B, R)

end GaloisForLFunctions.HTGeometry
