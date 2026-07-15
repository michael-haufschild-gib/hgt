import GaloisForLFunctions.RHTower.SoninSemilocalJacobiTransform

/-!
# Orthonormality of the archimedean Gamma-Jacobi family

The exact zero-frequency transform makes every positive-degree member mean-zero.  Symmetry of
multiplication by the coordinate and the cached three-term recurrence then propagate this to full
pairwise orthogonality and unit norm.  The same recurrence fixes exact degree and positive leading
coefficient, identifying the constructed family with the paper's orthonormal polynomials.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set

namespace RHTower

def semilocalArchimedeanJacobiGram (n m : ℕ) : ℝ :=
  ∫ s : ℝ,
    (semilocalArchimedeanJacobiPolynomial n).eval s *
      (semilocalArchimedeanJacobiPolynomial m).eval s
      ∂semilocalArchimedeanGammaMeasure

def semilocalArchimedeanJacobiShiftGram (n m : ℕ) : ℝ :=
  ∫ s : ℝ,
    s * (semilocalArchimedeanJacobiPolynomial n).eval s *
      (semilocalArchimedeanJacobiPolynomial m).eval s
      ∂semilocalArchimedeanGammaMeasure

theorem integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (p q : ℝ[X]) :
    Integrable (fun s : ℝ => p.eval s * q.eval s)
      semilocalArchimedeanGammaMeasure := by
  have h := (integrable_coe_eval_semilocalArchimedeanGammaMeasure (p * q)).re
  apply h.congr
  filter_upwards with s
  simp

theorem integrable_id_mul_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (p q : ℝ[X]) :
    Integrable (fun s : ℝ => s * p.eval s * q.eval s)
      semilocalArchimedeanGammaMeasure := by
  have h :=
    (integrable_coe_eval_semilocalArchimedeanGammaMeasure (X * p * q)).re
  apply h.congr
  filter_upwards with s
  simp

theorem semilocalArchimedeanJacobiGram_comm (n m : ℕ) :
    semilocalArchimedeanJacobiGram n m =
      semilocalArchimedeanJacobiGram m n := by
  apply integral_congr_ae
  filter_upwards with s
  exact mul_comm _ _

theorem semilocalArchimedeanJacobiShiftGram_comm (n m : ℕ) :
    semilocalArchimedeanJacobiShiftGram n m =
      semilocalArchimedeanJacobiShiftGram m n := by
  apply integral_congr_ae
  filter_upwards with s
  ring

theorem semilocalArchimedeanJacobiShiftGram_succ_recurrence (n m : ℕ) :
    semilocalArchimedeanJacobiShiftGram (n + 1) m =
      semilocalArchimedeanJacobiCoefficient n *
          semilocalArchimedeanJacobiGram n m +
        semilocalArchimedeanJacobiCoefficient (n + 1) *
          semilocalArchimedeanJacobiGram (n + 2) m := by
  have hn := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial n)
    (semilocalArchimedeanJacobiPolynomial m)
  have hn2 := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial (n + 2))
    (semilocalArchimedeanJacobiPolynomial m)
  unfold semilocalArchimedeanJacobiShiftGram
  calc
    (∫ s : ℝ,
        s * (semilocalArchimedeanJacobiPolynomial (n + 1)).eval s *
          (semilocalArchimedeanJacobiPolynomial m).eval s
          ∂semilocalArchimedeanGammaMeasure) =
        ∫ s : ℝ,
          semilocalArchimedeanJacobiCoefficient n *
              ((semilocalArchimedeanJacobiPolynomial n).eval s *
                (semilocalArchimedeanJacobiPolynomial m).eval s) +
            semilocalArchimedeanJacobiCoefficient (n + 1) *
              ((semilocalArchimedeanJacobiPolynomial (n + 2)).eval s *
                (semilocalArchimedeanJacobiPolynomial m).eval s)
            ∂semilocalArchimedeanGammaMeasure := by
      apply integral_congr_ae
      filter_upwards with s
      rw [semilocalArchimedeanJacobiPolynomial_eval_recurrence]
      ring
    _ = semilocalArchimedeanJacobiCoefficient n *
          semilocalArchimedeanJacobiGram n m +
        semilocalArchimedeanJacobiCoefficient (n + 1) *
          semilocalArchimedeanJacobiGram (n + 2) m := by
      rw [integral_add (hn.const_mul _) (hn2.const_mul _),
        integral_const_mul, integral_const_mul]
      rfl

theorem semilocalArchimedeanJacobiShiftGram_zero_recurrence (n : ℕ) :
    semilocalArchimedeanJacobiShiftGram n 0 =
      semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiGram n 1 := by
  rw [semilocalArchimedeanJacobiShiftGram,
    semilocalArchimedeanJacobiGram, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [semilocalArchimedeanJacobiPolynomial_eval_zero,
    semilocalArchimedeanJacobiPolynomial_eval_one]
  have ha : semilocalArchimedeanJacobiCoefficient 0 ≠ 0 :=
    (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
  field_simp [ha]

theorem integral_semilocalArchimedeanJacobiPolynomial_succ_eq_zero (n : ℕ) :
    (∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial (n + 1)).eval s
      ∂semilocalArchimedeanGammaMeasure) = 0 := by
  have h := semilocalArchimedeanJacobiFourier_eq_closedForm (n + 1) 0
  rw [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier] at h
  simp [semilocalArchimedeanJacobiFourierClosedForm] at h
  exact_mod_cast h

theorem semilocalArchimedeanJacobiGram_zero_zero :
    semilocalArchimedeanJacobiGram 0 0 = 1 := by
  have h := semilocalArchimedeanJacobiFourier_eq_closedForm 0 0
  rw [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier] at h
  simp [semilocalArchimedeanJacobiFourierClosedForm,
    semilocalArchimedeanJacobiNormalization,
    semilocalArchimedeanCharacteristic,
    semilocalArchimedeanJacobiGram] at h ⊢
  exact_mod_cast h

theorem semilocalArchimedeanJacobiGram_succ_zero (n : ℕ) :
    semilocalArchimedeanJacobiGram (n + 1) 0 = 0 := by
  simpa [semilocalArchimedeanJacobiGram] using
    integral_semilocalArchimedeanJacobiPolynomial_succ_eq_zero n

theorem semilocalArchimedeanJacobiGram_eq_zero_of_lt
    {m n : ℕ} (hmn : m < n) :
    semilocalArchimedeanJacobiGram n m = 0 := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases m with
      | zero =>
          cases n with
          | zero => omega
          | succ n => exact semilocalArchimedeanJacobiGram_succ_zero n
      | succ m =>
          cases m with
          | zero =>
              cases n with
              | zero => omega
              | succ n =>
                  cases n with
                  | zero => omega
                  | succ r =>
                      have hshift :
                          semilocalArchimedeanJacobiShiftGram (r + 2) 0 = 0 := by
                        rw [show r + 2 = (r + 1) + 1 by omega,
                          semilocalArchimedeanJacobiShiftGram_succ_recurrence]
                        rw [show r + 1 = r + 1 by rfl,
                          semilocalArchimedeanJacobiGram_succ_zero r]
                        rw [show r + 1 + 2 = (r + 2) + 1 by omega,
                          semilocalArchimedeanJacobiGram_succ_zero (r + 2)]
                        ring
                      rw [semilocalArchimedeanJacobiShiftGram_zero_recurrence] at hshift
                      exact (mul_eq_zero.mp hshift).resolve_left
                        (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
          | succ m =>
              cases n with
              | zero => omega
              | succ r =>
                  have hr : m + 1 < r := by omega
                  have hfirst :=
                    semilocalArchimedeanJacobiShiftGram_succ_recurrence r (m + 1)
                  have hrLeft :
                      semilocalArchimedeanJacobiGram r (m + 1) = 0 :=
                    ih (m + 1) (by omega) hr
                  have hrRight :
                      semilocalArchimedeanJacobiGram (r + 2) (m + 1) = 0 :=
                    ih (m + 1) (by omega) (by omega)
                  rw [hrLeft, hrRight, mul_zero, mul_zero, add_zero] at hfirst
                  have hsecond :
                      semilocalArchimedeanJacobiShiftGram (r + 1) (m + 1) =
                        semilocalArchimedeanJacobiCoefficient m *
                            semilocalArchimedeanJacobiGram (r + 1) m +
                          semilocalArchimedeanJacobiCoefficient (m + 1) *
                            semilocalArchimedeanJacobiGram (r + 1) (m + 2) := by
                    rw [semilocalArchimedeanJacobiShiftGram_comm,
                      semilocalArchimedeanJacobiShiftGram_succ_recurrence,
                      semilocalArchimedeanJacobiGram_comm m (r + 1),
                      semilocalArchimedeanJacobiGram_comm (m + 2) (r + 1)]
                  have hmLower :
                      semilocalArchimedeanJacobiGram (r + 1) m = 0 :=
                    ih m (by omega) (by omega)
                  rw [hsecond, hmLower, mul_zero, zero_add] at hfirst
                  exact (mul_eq_zero.mp hfirst).resolve_left
                    (semilocalArchimedeanJacobiCoefficient_pos (m + 1)).ne'

theorem semilocalArchimedeanJacobiGram_succ_self_eq (n : ℕ) :
    semilocalArchimedeanJacobiGram (n + 1) (n + 1) =
      semilocalArchimedeanJacobiGram n n := by
  cases n with
  | zero =>
      have h := semilocalArchimedeanJacobiShiftGram_succ_recurrence 0 0
      rw [semilocalArchimedeanJacobiShiftGram_zero_recurrence,
        semilocalArchimedeanJacobiGram_zero_zero,
        semilocalArchimedeanJacobiGram_eq_zero_of_lt (by omega : 0 < 2)] at h
      norm_num only [Nat.zero_add] at h
      rw [semilocalArchimedeanJacobiGram_zero_zero]
      apply mul_left_cancel₀
        (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
      simpa using h
  | succ m =>
      have hleft :=
        semilocalArchimedeanJacobiShiftGram_succ_recurrence (m + 1) (m + 1)
      have hright :=
        semilocalArchimedeanJacobiShiftGram_succ_recurrence m (m + 2)
      have hoffLeft :
          semilocalArchimedeanJacobiGram (m + 3) (m + 1) = 0 :=
        semilocalArchimedeanJacobiGram_eq_zero_of_lt (by omega)
      have hoffRight :
          semilocalArchimedeanJacobiGram m (m + 2) = 0 := by
        rw [semilocalArchimedeanJacobiGram_comm]
        exact semilocalArchimedeanJacobiGram_eq_zero_of_lt (by omega)
      rw [semilocalArchimedeanJacobiShiftGram_comm,
        hoffLeft, mul_zero, add_zero] at hleft
      rw [hoffRight, mul_zero, zero_add] at hright
      have hprod :
          semilocalArchimedeanJacobiCoefficient (m + 1) *
              semilocalArchimedeanJacobiGram (m + 1) (m + 1) =
            semilocalArchimedeanJacobiCoefficient (m + 1) *
              semilocalArchimedeanJacobiGram (m + 2) (m + 2) :=
        hleft.symm.trans hright
      exact (mul_left_cancel₀
        (semilocalArchimedeanJacobiCoefficient_pos (m + 1)).ne' hprod).symm

theorem semilocalArchimedeanJacobiGram_self (n : ℕ) :
    semilocalArchimedeanJacobiGram n n = 1 := by
  induction n with
  | zero => exact semilocalArchimedeanJacobiGram_zero_zero
  | succ n ih =>
      rw [semilocalArchimedeanJacobiGram_succ_self_eq, ih]

/-- The recursively selected Gamma-Jacobi polynomials are genuinely orthonormal. -/
theorem semilocalArchimedeanJacobiGram_eq_ite (n m : ℕ) :
    semilocalArchimedeanJacobiGram n m = if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst m
    simp [semilocalArchimedeanJacobiGram_self]
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [semilocalArchimedeanJacobiGram_comm]
      exact semilocalArchimedeanJacobiGram_eq_zero_of_lt hlt
    · exact semilocalArchimedeanJacobiGram_eq_zero_of_lt hgt

theorem semilocalArchimedeanJacobiPolynomial_natDegree (n : ℕ) :
    (semilocalArchimedeanJacobiPolynomial n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      exact natDegree_C_mul_X _
        (inv_ne_zero
          (semilocalArchimedeanJacobiCoefficient_pos 0).ne')
  | more n hn hn1 =>
      rw [semilocalArchimedeanJacobiPolynomial]
      have haN : semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
        (semilocalArchimedeanJacobiCoefficient_pos n).ne'
      have haN1 : semilocalArchimedeanJacobiCoefficient (n + 1) ≠ 0 :=
        (semilocalArchimedeanJacobiCoefficient_pos (n + 1)).ne'
      have hp1 : semilocalArchimedeanJacobiPolynomial (n + 1) ≠ 0 := by
        intro hzero
        rw [hzero, natDegree_zero] at hn1
        omega
      have hleft :
          (X * semilocalArchimedeanJacobiPolynomial (n + 1)).natDegree =
            n + 2 := by
        rw [natDegree_X_mul hp1, hn1]
      have hright :
          (C (semilocalArchimedeanJacobiCoefficient n) *
              semilocalArchimedeanJacobiPolynomial n).natDegree = n := by
        rw [natDegree_C_mul haN, hn]
      rw [natDegree_C_mul (inv_ne_zero haN1),
        natDegree_sub_eq_left_of_natDegree_lt (by omega), hleft]

theorem semilocalArchimedeanJacobiPolynomial_leadingCoeff_pos (n : ℕ) :
    0 < (semilocalArchimedeanJacobiPolynomial n).leadingCoeff := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      simp only [semilocalArchimedeanJacobiPolynomial_one,
        leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
      exact inv_pos.mpr (semilocalArchimedeanJacobiCoefficient_pos 0)
  | more n hn hn1 =>
      rw [semilocalArchimedeanJacobiPolynomial, leadingCoeff_mul,
        leadingCoeff_C]
      have haN : semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
        (semilocalArchimedeanJacobiCoefficient_pos n).ne'
      have hp1 : semilocalArchimedeanJacobiPolynomial (n + 1) ≠ 0 := by
        exact leadingCoeff_ne_zero.mp hn1.ne'
      have hdegree :
          degree
              (C (semilocalArchimedeanJacobiCoefficient n) *
                semilocalArchimedeanJacobiPolynomial n) <
            degree (X * semilocalArchimedeanJacobiPolynomial (n + 1)) := by
        apply degree_lt_degree
        rw [natDegree_C_mul haN,
          semilocalArchimedeanJacobiPolynomial_natDegree,
          natDegree_X_mul hp1,
          semilocalArchimedeanJacobiPolynomial_natDegree]
        omega
      rw [leadingCoeff_sub_of_degree_lt hdegree,
        leadingCoeff_mul, leadingCoeff_X, one_mul]
      exact mul_pos
        (inv_pos.mpr
          (semilocalArchimedeanJacobiCoefficient_pos (n + 1))) hn1

end RHTower
