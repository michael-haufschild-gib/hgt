import GaloisForLFunctions.ThetaCuspSections.LegendrePolynomialKernel

/-!
# Polynomial evaluation from a parabolic interval energy

Multiplying by the parabolic weight raises degree by two. The general
Legendre kernel then bounds every exterior evaluation by the retained
weighted energy, with the original polynomial's growth exponent.
-/

open MeasureTheory Set Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections

/-- The squared polynomial energy retained by a parabolic core of radius `R`. -/
def parabolicEnergyAt (R : ℝ) (P : ℝ[X]) : ℝ :=
  ∫ b in -R..R, ((1 - b ^ 2 / R ^ 2) * P.eval b) ^ 2

theorem parabolicEnergyAt_nonneg {R : ℝ} (hR : 0 ≤ R) (P : ℝ[X]) :
    0 ≤ parabolicEnergyAt R P :=
  intervalIntegral.integral_nonneg (by linarith only [hR]) fun _ _ => sq_nonneg _

/-- Every degree has an exterior envelope paid by its complete parabolic energy. -/
theorem polynomial_sq_le_parabolicEnergy {R : ℝ} (hR : 0 < R) {P : ℝ[X]}
    {n : ℕ} (hdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ))
    {b : ℝ} (hb : 10 * R ≤ |b|) :
    P.eval b ^ 2 ≤
      (16 / 15 * (100 / 99) ^ 2 * (((n + 2 : ℕ) : ℝ) + 1 / 2) *
        legendreLead (n + 2) ^ 2 / R) * (|b| / R) ^ (2 * n) * parabolicEnergyAt R P := by
  by_cases hP : P = 0
  · subst P
    simp [parabolicEnergyAt]
  have hPN := (natDegree_lt_iff_degree_lt hP).mpr hdeg
  let Q : ℝ[X] := (1 - X ^ 2) * P.comp (C R * X)
  have hQdeg : Q.degree < ((n + 3 : ℕ) : WithBot ℕ) := by
    have hW : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (by norm_num)
    have hlin : (C R * X).natDegree = 1 := by simp [hR.ne']
    have hQN : Q.natDegree ≤ n + 2 := by
      have hh := natDegree_mul_le (p := (1 - X ^ 2 : ℝ[X])) (q := P.comp (C R * X))
      rw [natDegree_comp, hlin, mul_one] at hh
      dsimp only [Q]
      omega
    exact (degree_le_natDegree (p := Q)).trans_lt
      (by exact_mod_cast (show Q.natDegree < n + 3 by omega))
  have hQeval (x : ℝ) : Q.eval x = (1 - x ^ 2) * P.eval (R * x) := by
    simp only [Q, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_comp, eval_C]
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun b : ℝ => ((1 - b ^ 2 / R ^ 2) * P.eval b) ^ 2)
    (a := -1) (b := 1) (c := R) (d := 0)
  have hscaled (x : ℝ) : ((1 - (R * x + 0) ^ 2 / R ^ 2) * P.eval (R * x + 0)) ^ 2 =
      Q.eval x ^ 2 := by
    simp only [hQeval, add_zero, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hR.ne')]
  simp_rw [hscaled] at hcov
  simp only [mul_neg, mul_one, add_zero] at hcov
  have hI : (∫ x in (-1 : ℝ)..1, Q.eval x ^ 2) = parabolicEnergyAt R P / R := by
    apply (eq_div_iff hR.ne').mpr
    rw [mul_comm]
    exact hcov
  have hval : Q.eval (b / R) = (1 - b ^ 2 / R ^ 2) * P.eval b := by
    rw [hQeval, show R * (b / R) = b by field_simp [hR.ne'], div_pow]
  have hpoint := polynomial_sq_le_legendreKernel (n + 3) Q hQdeg (b / R)
  rw [hval, mul_pow, hI] at hpoint
  let x : ℝ := |b| / R
  have hx : 10 ≤ x := (le_div_iff₀ hR).mpr hb
  have hx0 : 0 < x := by linarith only [hx]
  have habs : |b / R| = x := by rw [abs_div, abs_of_pos hR]
  have hx2 : x ^ 2 = b ^ 2 / R ^ 2 := by
    dsimp only [x]
    rw [div_pow, sq_abs]
  have hk := legendreKernel_le_abs (x := b / R) (by rw [habs]; linarith only [hx]) (n + 2)
  rw [habs] at hk
  have hx100 : 100 ≤ x ^ 2 := by nlinarith only [hx]
  have hw : 99 / 100 * x ^ 2 ≤ x ^ 2 - 1 := by linarith only [hx100]
  have hws := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 99 / 100 * x ^ 2) hw 2
  have hw' : (99 / 100 : ℝ) ^ 2 * x ^ 4 ≤ (1 - b ^ 2 / R ^ 2) ^ 2 := by
    rw [← hx2]
    nlinarith only [hws]
  have hE := parabolicEnergyAt_nonneg hR.le P
  let C : ℝ := 16 / 15 * (100 / 99) ^ 2 * (((n + 2 : ℕ) : ℝ) + 1 / 2) *
    legendreLead (n + 2) ^ 2 / R
  have hpay : ((99 / 100 : ℝ) ^ 2 * x ^ 4) * P.eval b ^ 2 ≤
      ((99 / 100 : ℝ) ^ 2 * x ^ 4) * (C * x ^ (2 * n) * parabolicEnergyAt R P) := by
    calc
      _ ≤ (1 - b ^ 2 / R ^ 2) ^ 2 * P.eval b ^ 2 :=
        mul_le_mul_of_nonneg_right hw' (sq_nonneg _)
      _ ≤ legendreKernel (n + 3) (b / R) * (parabolicEnergyAt R P / R) := hpoint
      _ ≤ (16 / 15 * (((n + 2 : ℕ) : ℝ) + 1 / 2) * legendreLead (n + 2) ^ 2 *
          x ^ (2 * (n + 2))) * (parabolicEnergyAt R P / R) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by
        have hp : x ^ (2 * (n + 2)) = x ^ 4 * x ^ (2 * n) := by
          rw [show 2 * (n + 2) = 4 + 2 * n by omega, pow_add]
        rw [hp]
        dsimp only [C]
        ring
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (99 / 100 : ℝ) ^ 2 * x ^ 4)).mp hpay

/-- Every nonzero polynomial retains strictly positive energy in every positive-radius core. -/
theorem parabolicEnergyAt_pos {R : ℝ} (hR : 0 < R) {P : ℝ[X]} (hP : P ≠ 0) :
    0 < parabolicEnergyAt R P := by
  refine lt_of_le_of_ne (parabolicEnergyAt_nonneg hR.le P) fun h0 => hP ?_
  refine eq_zero_of_infinite_isRoot P ((Ici_infinite (10 * R)).mono fun b hb => ?_)
  have hdeg : P.degree < ((P.natDegree + 1 : ℕ) : WithBot ℕ) :=
    (degree_le_natDegree (p := P)).trans_lt (by exact_mod_cast Nat.lt_succ_self P.natDegree)
  have hh := polynomial_sq_le_parabolicEnergy hR hdeg (hb.trans (le_abs_self b))
  rw [← h0, mul_zero] at hh
  exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hh (sq_nonneg _))

#print axioms polynomial_sq_le_parabolicEnergy
#print axioms parabolicEnergyAt_pos

end GaloisForLFunctions.ThetaCuspSections
