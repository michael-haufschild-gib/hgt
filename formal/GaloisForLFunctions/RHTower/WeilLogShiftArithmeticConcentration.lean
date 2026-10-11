import GaloisForLFunctions.RHTower.WeilLogShiftBinomialSecondMoment

/-! Concentration of the normalized arithmetic annihilator around its central index. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilArithmeticAbsProfile (r : ℕ) (i : Fin (r + 2)) : ℝ :=
  |finiteWeilNormalizedMomentDual (finiteWeilArithmeticNodes r) i|

def finiteWeilArithmeticCenter (r : ℕ) : Fin (r + 2) := ⟨(r + 1) / 2, by omega⟩

theorem finiteWeilArithmeticAbsProfile_pos (r : ℕ) (i : Fin (r + 2)) :
    0 < finiteWeilArithmeticAbsProfile r i :=
  abs_pos.mpr (finiteWeilNormalizedMomentDual_ne_zero _
    (finiteWeilArithmeticNodes_injective r) i)

theorem finiteWeilArithmeticAbsProfile_le_one (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilArithmeticAbsProfile r i ≤ 1 := by
  have h := norm_le_pi_norm (finiteWeilNormalizedMomentDual (finiteWeilArithmeticNodes r)) i
  simpa only [finiteWeilArithmeticAbsProfile, Real.norm_eq_abs, finiteWeilNormalizedMomentDual_norm _
    (finiteWeilArithmeticNodes_injective r)] using h

theorem finiteWeilArithmeticAbsProfile_eq_binomial (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilArithmeticAbsProfile r i =
      ((r + 1).choose ((r + 1) / 2) : ℝ)⁻¹ * ((r + 1).choose (i : ℕ) : ℝ) := by
  simp only [finiteWeilArithmeticAbsProfile, finiteWeilArithmeticDual_eq_binomial,
    Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((r + 1).choose ((r + 1) / 2) : ℝ)),
    finiteWeilBinomialDual_abs]

theorem finiteWeilArithmeticAbsProfile_center (r : ℕ) :
    finiteWeilArithmeticAbsProfile r (finiteWeilArithmeticCenter r) = 1 := by
  rw [finiteWeilArithmeticAbsProfile_eq_binomial]
  change _⁻¹ * ((r + 1).choose ((r + 1) / 2) : ℝ) = 1
  rw [← finiteWeilBinomialDual_norm, inv_mul_cancel₀ (finiteWeilBinomialDual_norm_pos r).ne']

theorem finiteWeilArithmeticAbsProfile_sum (r : ℕ) :
    ∑ i, finiteWeilArithmeticAbsProfile r i = finiteWeilArithmeticMass r := rfl

theorem finiteWeilArithmeticAbsProfile_half_second_moment (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      ((i : ℕ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) =
      ((r + 1 : ℕ) : ℝ) / 4 * finiteWeilArithmeticMass r := by
  simp only [finiteWeilArithmeticAbsProfile_eq_binomial, mul_assoc, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ) *
    ((i : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) (r + 2),
    finiteWeil_binomial_half_centered_second_moment, finiteWeilArithmeticMass_eq_binomial]
  ring

theorem finiteWeilArithmeticAbsProfile_center_second_moment (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      ((i : ℕ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ) : ℝ) ^ 2) ≤
      (((r + 1 : ℕ) : ℝ) + 1) / 2 * finiteWeilArithmeticMass r := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let c : ℝ := ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)
  have hcl : 2 * c ≤ n := by
    dsimp [c, n, finiteWeilArithmeticCenter]
    exact_mod_cast (show 2 * ((r + 1) / 2) ≤ r + 1 by omega)
  have hcu : n ≤ 2 * c + 1 := by
    dsimp [c, n, finiteWeilArithmeticCenter]
    exact_mod_cast (show r + 1 ≤ 2 * ((r + 1) / 2) + 1 by omega)
  have hv : (n / 2 - c) ^ 2 ≤ 1 / 4 := by
    have h := mul_nonneg (show 0 ≤ n / 2 - c by linarith)
      (show 0 ≤ 1 / 2 - (n / 2 - c) by linarith)
    nlinarith only [h, hcl, hcu]
  have hi (i : Fin (r + 2)) : ((i : ℕ) - c : ℝ) ^ 2 ≤
      2 * ((i : ℕ) - n / 2 : ℝ) ^ 2 + 1 / 2 := by
    nlinarith only [hv, sq_nonneg (((i : ℕ) : ℝ) - n / 2 - (n / 2 - c))]
  calc
    _ ≤ ∑ i, finiteWeilArithmeticAbsProfile r i *
        (2 * ((i : ℕ) - n / 2 : ℝ) ^ 2 + 1 / 2) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hi i) (finiteWeilArithmeticAbsProfile_pos r i).le
    _ = 2 * (∑ i, finiteWeilArithmeticAbsProfile r i * ((i : ℕ) - n / 2 : ℝ) ^ 2) +
        (∑ i, finiteWeilArithmeticAbsProfile r i) / 2 := by
      simp only [div_eq_mul_inv]
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [finiteWeilArithmeticAbsProfile_half_second_moment,
        finiteWeilArithmeticAbsProfile_sum]
      ring

theorem finiteWeilArithmeticAbsProfile_center_first_moment (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) ≤
      finiteWeilArithmeticMass r * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let q := finiteWeilArithmeticAbsProfile r
  let d := fun i : Fin (r + 2) =>
    ((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)
  let G := finiteWeilArithmeticMass r
  let V : ℝ := (((r + 1 : ℕ) : ℝ) + 1) / 2
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 2)))
    (r := fun i => q i * |d i|) (f := q) (g := fun i => q i * d i ^ 2)
    (fun i _ => (finiteWeilArithmeticAbsProfile_pos r i).le)
    (fun i _ => mul_nonneg (finiteWeilArithmeticAbsProfile_pos r i).le (sq_nonneg _))
    (fun i _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
  have hT := finiteWeilArithmeticAbsProfile_center_second_moment r
  change (∑ i, q i * d i ^ 2) ≤ V * G at hT
  rw [finiteWeilArithmeticAbsProfile_sum] at hcs
  have hbound := mul_le_mul_of_nonneg_left hT hG.le
  have hs := Real.sq_sqrt hV
  have hs0 := Real.sqrt_nonneg V
  have hsq : (∑ i, q i * |d i|) ^ 2 ≤ (G * Real.sqrt V) ^ 2 := by
    calc
      _ ≤ G * (V * G) := hcs.trans hbound
      _ = _ := by rw [mul_pow, hs]; ring
  change (∑ i, q i * |d i|) ≤ G * Real.sqrt V
  nlinarith only [hsq, mul_nonneg hG.le hs0]

theorem finiteWeilArithmeticAbsProfile_center_pointwise (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilArithmeticAbsProfile r i *
      |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| ≤
      Real.sqrt (((((r + 1 : ℕ) : ℝ) + 1) / 2) * finiteWeilArithmeticMass r) := by
  let d := fun j : Fin (r + 2) =>
    ((j : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)
  have hq := finiteWeilArithmeticAbsProfile_pos r i
  have hq1 := finiteWeilArithmeticAbsProfile_le_one r i
  have hsingle := Finset.single_le_sum
    (s := Finset.univ) (f := fun j => finiteWeilArithmeticAbsProfile r j * d j ^ 2)
    (fun j _ => mul_nonneg (finiteWeilArithmeticAbsProfile_pos r j).le (sq_nonneg _))
    (Finset.mem_univ i)
  have hT := finiteWeilArithmeticAbsProfile_center_second_moment r
  change (∑ j, finiteWeilArithmeticAbsProfile r j * d j ^ 2) ≤ _ at hT
  apply (Real.le_sqrt (mul_nonneg hq.le (abs_nonneg _)) (by
    have := finiteWeilArithmeticMass_ge_two r
    positivity)).mpr
  rw [mul_pow, sq_abs]
  calc
    _ ≤ finiteWeilArithmeticAbsProfile r i * d i ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hq, hq1]) (sq_nonneg _)
    _ ≤ _ := hsingle.trans hT

end RHTower
