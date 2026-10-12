import GaloisForLFunctions.RHTower.XiGaussianHeatPhysicalRealForm

/-!
# Every even polynomial–Gaussian of width `√a` is a physical heat test

For `a > 0` the map `P ↦ heatPolyR a P` sends real polynomials of degree `≤ m` onto the even real
polynomials of degree `≤ 2m` (`exists_heatPolyR_eq`).  The `k`-th basis element
`heatPolyR a Xᵏ = (2πa)^{-1/2} (−1)ᵏ ∂^{2k}`-factor has degree exactly `2k` with leading coefficient
`(2πa)^{-1/2} (−1)ᵏ (−1/a)^{2k}` (`coeff_gaussDerivPolyR_self`), so the family is triangular and
an even polynomial is reduced degree by degree.
-/

open scoped Real
open Polynomial

namespace RHTower

noncomputable section

theorem coeff_comp_neg_X_real (Q : ℝ[X]) (k : ℕ) : (Q.comp (-X)).coeff k = (-1) ^ k * Q.coeff k := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq]; ring
  | monomial i c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, ← mul_assoc,
      show ((-1 : ℝ[X]) ^ i) = C ((-1 : ℝ) ^ i) by simp, ← C_mul, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · ring

theorem coeff_odd_eq_zero_of_even {Q : ℝ[X]} (hQ : Q.comp (-X) = Q) {k : ℕ} (hk : Odd k) :
    Q.coeff k = 0 := by
  have h := coeff_comp_neg_X_real Q k
  rw [hQ, hk.neg_one_pow] at h
  linarith

theorem coeff_gaussDerivPolyR_self (b : ℝ) (m : ℕ) :
    (gaussDerivPolyR b m).coeff m = (-(2 * b)) ^ m := by
  induction m with
  | zero => simp [gaussDerivPolyR]
  | succ m ih =>
    rw [gaussDerivPolyR, coeff_sub, coeff_derivative,
      coeff_eq_zero_of_natDegree_lt ((natDegree_gaussDerivPolyR_le b m).trans_lt (by omega)),
      zero_mul, zero_sub, mul_assoc, coeff_C_mul, coeff_X_mul, ih, pow_succ]
    ring

/-- `heatPolyR` with a longer coefficient range. -/
theorem heatPolyR_eq_sum_range (a : ℝ) (P : ℝ[X]) {M : ℕ} (hM : P.natDegree ≤ M) :
    heatPolyR a P = C ((2 * π * a) ^ (-(1 / 2 : ℝ))) * ∑ k ∈ Finset.range (M + 1),
      C (P.coeff k * (-1) ^ k) * gaussDerivPolyR (1 / (2 * a)) (2 * k) := by
  rw [heatPolyR]
  congr 1
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, C_0, zero_mul]

theorem heatPolyR_add (a : ℝ) (P R : ℝ[X]) :
    heatPolyR a (P + R) = heatPolyR a P + heatPolyR a R := by
  set M := max (max P.natDegree R.natDegree) (P + R).natDegree
  rw [heatPolyR_eq_sum_range a (P + R) (le_max_right _ _),
    heatPolyR_eq_sum_range a P ((le_max_left _ _).trans (le_max_left _ _)),
    heatPolyR_eq_sum_range a R ((le_max_right _ _).trans (le_max_left _ _)), ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_add, add_mul, C_add, add_mul]

theorem heatPolyR_C_mul_X_pow (a c : ℝ) (m : ℕ) :
    heatPolyR a (C c * X ^ m) = C ((2 * π * a) ^ (-(1 / 2 : ℝ)) * (c * (-1) ^ m)) *
      gaussDerivPolyR (1 / (2 * a)) (2 * m) := by
  rw [heatPolyR_eq_sum_range a _ (natDegree_C_mul_X_pow_le c m), Finset.sum_eq_single m]
  · rw [coeff_C_mul_X_pow, if_pos rfl, ← mul_assoc, ← C_mul]
  · intro k _ hk
    rw [coeff_C_mul_X_pow, if_neg hk, zero_mul, C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self m)) h

/-- **Surjectivity onto even polynomials.** -/
theorem exists_heatPolyR_eq {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∀ Q : ℝ[X], Q.comp (-X) = Q → Q.natDegree ≤ 2 * m →
      ∃ P : ℝ[X], P.natDegree ≤ m ∧ heatPolyR a P = Q := by
  set κ := (2 * π * a) ^ (-(1 / 2 : ℝ)) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  set b := 1 / (2 * a) with hb
  have hb0 : 0 < b := by positivity
  induction m with
  | zero =>
    intro Q _ hQ
    rw [Nat.mul_zero] at hQ
    rw [eq_C_of_natDegree_le_zero hQ]
    refine ⟨C (Q.coeff 0 / κ), by simp, ?_⟩
    rw [show C (Q.coeff 0 / κ) = C (Q.coeff 0 / κ) * X ^ 0 by simp, heatPolyR_C_mul_X_pow]
    simp only [pow_zero, mul_one, gaussDerivPolyR]
    congr 1
    field_simp
    rw [hκ]
    ring
  | succ m ih =>
    intro Q hQe hQd
    set lead := (-(2 * b)) ^ (2 * (m + 1)) with hlead
    have hlead0 : lead ≠ 0 := pow_ne_zero _ (by linarith)
    set c := Q.coeff (2 * (m + 1)) / (κ * (-1) ^ (m + 1) * lead) with hc
    set Q' := Q - heatPolyR a (C c * X ^ (m + 1)) with hQ'
    have hbasis := heatPolyR_C_mul_X_pow a c (m + 1)
    have hbdeg : (heatPolyR a (C c * X ^ (m + 1))).natDegree ≤ 2 * (m + 1) := by
      rw [hbasis]
      exact (natDegree_C_mul_le _ _).trans (natDegree_gaussDerivPolyR_le _ _)
    have hQ'e : Q'.comp (-X) = Q' := by
      rw [hQ', sub_comp, hQe, heatPolyR_comp_neg]
    have htop : Q'.coeff (2 * (m + 1)) = 0 := by
      rw [hQ', coeff_sub, hbasis, coeff_C_mul, coeff_gaussDerivPolyR_self, ← hb, ← hlead, hc]
      have hne : κ * (-1 : ℝ) ^ (m + 1) * lead ≠ 0 :=
        mul_ne_zero (mul_ne_zero hκ0.ne' (pow_ne_zero _ (by norm_num))) hlead0
      field_simp
      ring
    have hQ'd : Q'.natDegree ≤ 2 * m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rcases (show N = 2 * m + 1 ∨ N = 2 * (m + 1) ∨ 2 * (m + 1) < N by omega) with h | h | h
      · exact coeff_odd_eq_zero_of_even hQ'e ⟨m, by omega⟩
      · rw [h]; exact htop
      · have hd : Q'.natDegree ≤ 2 * (m + 1) :=
          (natDegree_sub_le _ _).trans (max_le hQd hbdeg)
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd h)
    obtain ⟨P', hP'd, hP'⟩ := ih Q' hQ'e hQ'd
    refine ⟨P' + C c * X ^ (m + 1), ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le (hP'd.trans (by omega))
        ((natDegree_C_mul_X_pow_le c _).trans le_rfl))
    · rw [heatPolyR_add, hP', hQ', sub_add_cancel]

end

end RHTower
