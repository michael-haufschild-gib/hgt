import GaloisForLFunctions.ThetaCuspSections.LegendrePolynomialKernel

/-!
# Polynomial evaluation from power-weighted core energy

Multiplying by any integer power of the parabolic weight raises the
Legendre cutoff by twice that power. Outside four core radii, division by
the weight recovers the original polynomial's growth exponent.
-/

open MeasureTheory Set Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections

/-- Polynomial energy retained by an integer power of a parabolic core. -/
def parabolicPowerEnergy (R : ℝ) (m : ℕ) (P : ℝ[X]) : ℝ :=
  ∫ b in -R..R, ((1 - b ^ 2 / R ^ 2) ^ m * P.eval b) ^ 2

theorem parabolicPowerEnergy_nonneg {R : ℝ} (hR : 0 ≤ R) (m : ℕ) (P : ℝ[X]) :
    0 ≤ parabolicPowerEnergy R m P :=
  intervalIntegral.integral_nonneg (by linarith only [hR]) fun _ _ => sq_nonneg _

private theorem even_power_weight (t : ℝ) (m : ℕ) :
    ((1 - t) ^ m) ^ 2 = (t - 1) ^ (2 * m) := by
  calc
    _ = ((1 - t) ^ 2) ^ m := by rw [← pow_mul, ← pow_mul, Nat.mul_comm m 2]
    _ = ((t - 1) ^ 2) ^ m := by congr 1; ring
    _ = _ := by rw [pow_mul]

/-- An exterior envelope valid for every polynomial degree and every core power. -/
theorem polynomial_sq_le_parabolicPowerEnergy {R : ℝ} (hR : 0 < R) (m : ℕ)
    {P : ℝ[X]} {n : ℕ} (hdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ))
    {b : ℝ} (hb : 4 * R ≤ |b|) :
    P.eval b ^ 2 ≤
      (16 / 15 * (16 / 15) ^ (2 * m) * (((n + 2 * m : ℕ) : ℝ) + 1 / 2) *
        legendreLead (n + 2 * m) ^ 2 / R) *
      (|b| / R) ^ (2 * n) * parabolicPowerEnergy R m P := by
  by_cases hP : P = 0
  · subst P
    simp [parabolicPowerEnergy]
  have hPN := (natDegree_lt_iff_degree_lt hP).mpr hdeg
  let Q : ℝ[X] := (1 - X ^ 2) ^ m * P.comp (C R * X)
  have hQdeg : Q.degree < ((n + 2 * m + 1 : ℕ) : WithBot ℕ) := by
    have hW : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (by norm_num)
    have hlin : (C R * X).natDegree = 1 := by simp [hR.ne']
    have hQN : Q.natDegree ≤ n + 2 * m := by
      have hh := natDegree_mul_le (p := (1 - X ^ 2 : ℝ[X]) ^ m)
        (q := P.comp (C R * X))
      rw [natDegree_pow, natDegree_comp, hlin, mul_one] at hh
      have hw := Nat.mul_le_mul_right m hW
      dsimp only [Q]
      omega
    exact (degree_le_natDegree (p := Q)).trans_lt
      (by exact_mod_cast (show Q.natDegree < n + 2 * m + 1 by omega))
  have hQeval (x : ℝ) : Q.eval x = (1 - x ^ 2) ^ m * P.eval (R * x) := by
    simp only [Q, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_comp, eval_C]
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun b : ℝ => ((1 - b ^ 2 / R ^ 2) ^ m * P.eval b) ^ 2)
    (a := -1) (b := 1) (c := R) (d := 0)
  have hscaled (x : ℝ) :
      ((1 - (R * x + 0) ^ 2 / R ^ 2) ^ m * P.eval (R * x + 0)) ^ 2 = Q.eval x ^ 2 := by
    simp only [hQeval, add_zero, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hR.ne')]
  simp_rw [hscaled] at hcov
  simp only [mul_neg, mul_one, add_zero] at hcov
  have hI : (∫ x in (-1 : ℝ)..1, Q.eval x ^ 2) = parabolicPowerEnergy R m P / R := by
    apply (eq_div_iff hR.ne').mpr
    rw [mul_comm]
    exact hcov
  have hval : Q.eval (b / R) = (1 - b ^ 2 / R ^ 2) ^ m * P.eval b := by
    rw [hQeval, show R * (b / R) = b by field_simp [hR.ne'], div_pow]
  have hpoint := polynomial_sq_le_legendreKernel (n + 2 * m + 1) Q hQdeg (b / R)
  rw [hval, mul_pow, hI] at hpoint
  let x : ℝ := |b| / R
  have hx : 4 ≤ x := (le_div_iff₀ hR).mpr hb
  have hx0 : 0 < x := by linarith only [hx]
  have habs : |b / R| = x := by rw [abs_div, abs_of_pos hR]
  have hx2 : x ^ 2 = b ^ 2 / R ^ 2 := by
    dsimp only [x]
    rw [div_pow, sq_abs]
  have hk := legendreKernel_le_abs (x := b / R) (by rwa [habs]) (n + 2 * m)
  rw [habs] at hk
  have hx16 : 16 ≤ x ^ 2 := by nlinarith only [hx]
  have hw : 15 / 16 * x ^ 2 ≤ x ^ 2 - 1 := by linarith only [hx16]
  have hws := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 15 / 16 * x ^ 2) hw (2 * m)
  have hw' : (15 / 16 : ℝ) ^ (2 * m) * x ^ (4 * m) ≤
      ((1 - b ^ 2 / R ^ 2) ^ m) ^ 2 := by
    rw [← hx2, even_power_weight]
    simpa only [mul_pow, ← pow_mul, show 2 * (2 * m) = 4 * m by omega] using hws
  have hE := parabolicPowerEnergy_nonneg hR.le m P
  let C : ℝ := 16 / 15 * (16 / 15) ^ (2 * m) * (((n + 2 * m : ℕ) : ℝ) + 1 / 2) *
    legendreLead (n + 2 * m) ^ 2 / R
  have hinv : (15 / 16 : ℝ) ^ (2 * m) * (16 / 15 : ℝ) ^ (2 * m) = 1 := by
    rw [← mul_pow]
    norm_num
  have hpay : ((15 / 16 : ℝ) ^ (2 * m) * x ^ (4 * m)) * P.eval b ^ 2 ≤
      ((15 / 16 : ℝ) ^ (2 * m) * x ^ (4 * m)) *
        (C * x ^ (2 * n) * parabolicPowerEnergy R m P) := by
    calc
      _ ≤ ((1 - b ^ 2 / R ^ 2) ^ m) ^ 2 * P.eval b ^ 2 :=
        mul_le_mul_of_nonneg_right hw' (sq_nonneg _)
      _ ≤ legendreKernel (n + 2 * m + 1) (b / R) * (parabolicPowerEnergy R m P / R) := hpoint
      _ ≤ (16 / 15 * (((n + 2 * m : ℕ) : ℝ) + 1 / 2) * legendreLead (n + 2 * m) ^ 2 *
          x ^ (2 * (n + 2 * m))) * (parabolicPowerEnergy R m P / R) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by
        have hp : x ^ (2 * (n + 2 * m)) = x ^ (4 * m) * x ^ (2 * n) := by
          rw [show 2 * (n + 2 * m) = 4 * m + 2 * n by omega, pow_add]
        rw [hp]
        dsimp only [C]
        linear_combination -(16 / 15 * (((n + 2 * m : ℕ) : ℝ) + 1 / 2) *
          legendreLead (n + 2 * m) ^ 2 / R * x ^ (4 * m) * x ^ (2 * n) *
          parabolicPowerEnergy R m P) * hinv
  exact (mul_le_mul_iff_right₀
    (by positivity : (0 : ℝ) < (15 / 16 : ℝ) ^ (2 * m) * x ^ (4 * m))).mp hpay

/-- Every nonzero polynomial retains positive energy for every core power. -/
theorem parabolicPowerEnergy_pos {R : ℝ} (hR : 0 < R) (m : ℕ)
    {P : ℝ[X]} (hP : P ≠ 0) : 0 < parabolicPowerEnergy R m P := by
  refine lt_of_le_of_ne (parabolicPowerEnergy_nonneg hR.le m P) fun h0 => hP ?_
  refine eq_zero_of_infinite_isRoot P ((Ici_infinite (4 * R)).mono fun b hb => ?_)
  have hdeg : P.degree < ((P.natDegree + 1 : ℕ) : WithBot ℕ) :=
    (degree_le_natDegree (p := P)).trans_lt (by exact_mod_cast Nat.lt_succ_self P.natDegree)
  have hh := polynomial_sq_le_parabolicPowerEnergy hR m hdeg (hb.trans (le_abs_self b))
  rw [← h0, mul_zero] at hh
  exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hh (sq_nonneg _))

#print axioms polynomial_sq_le_parabolicPowerEnergy
#print axioms parabolicPowerEnergy_pos

end GaloisForLFunctions.ThetaCuspSections
