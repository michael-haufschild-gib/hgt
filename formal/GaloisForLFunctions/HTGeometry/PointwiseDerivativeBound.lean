import GaloisForLFunctions.HTGeometry.TopCoefficientBound

/-!
# A pointwise derivative bound from an autonomous algebraic relation

Wherever `‖F z‖` is large, the relation `∑ C_k(F)(F′)^k = 0` bounds `‖F′ z‖` by a fixed power of
`‖F z‖`.  The top coefficient dominates the rest once `‖F′‖ ≥ 1`, and the coefficient magnitudes are
controlled above and below by powers of `‖F z‖`.

The exponent and the constant depend only on the coefficient polynomials, not on the point.  That is
the significant part: unlike the two-sided Newton estimate, which selects an index pair that may vary
with the radius, this bound involves **no branch choice at all** and therefore transfers directly
from one radius to another.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **A pointwise derivative bound from an autonomous algebraic relation.**  Wherever `‖F z‖` is
large, the relation `∑ C_k(F) (F′)^k = 0` bounds `‖F′ z‖` by a fixed power of `‖F z‖`.  The exponent
and constant depend only on the coefficients, not on the point — there is no branch to choose. -/
theorem exists_norm_deriv_le_of_relation {m : ℕ} {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0)
    {F : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (F z) * (deriv F z) ^ k = 0) :
    ∃ K R₀ : ℝ, 0 < K ∧ 1 ≤ R₀ ∧ ∀ z : ℂ, R₀ ≤ ‖F z‖ →
      ‖deriv F z‖ ≤ max 1 (K * ‖F z‖ ^ (∑ j ∈ Finset.range (m + 1), (C j).natDegree)) := by
  classical
  obtain ⟨R₁, hR₁, hlow⟩ := exists_le_norm_eval (C m) hCm
  set d : ℕ := ∑ j ∈ Finset.range (m + 1), (C j).natDegree with hd
  have hlc : 0 < ‖(C m).leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hCm)
  set K : ℝ := (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖)
    * (2 / ‖(C m).leadingCoeff‖) + 1 with hK
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
        ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖ :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
    have h2 : (0 : ℝ) < 2 / ‖(C m).leadingCoeff‖ := by positivity
    rw [hK]
    nlinarith [h1, h2]
  refine ⟨K, R₁, hKpos, hR₁, fun z hz => ?_⟩
  set Y : ℂ := F z with hY
  set t : ℝ := ‖deriv F z‖ with ht
  have hY1 : (1 : ℝ) ≤ ‖Y‖ := le_trans hR₁ hz
  rcases le_or_gt t 1 with hle | hgt
  · exact le_trans hle (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    -- the top term is dominated
    have hdom : ‖(C m).eval Y‖ * t ^ m ≤ ∑ j ∈ Finset.range m, ‖(C j).eval Y‖ * t ^ j := by
      have hsplit : (C m).eval Y * (deriv F z) ^ m
          = -∑ j ∈ Finset.range m, (C j).eval Y * (deriv F z) ^ j := by
        have h := hrel z
        rw [Finset.sum_range_succ] at h
        linear_combination h
      have hnorm : ‖(C m).eval Y‖ * t ^ m = ‖(C m).eval Y * (deriv F z) ^ m‖ := by
        rw [norm_mul, norm_pow, ht]
      rw [hnorm, hsplit, norm_neg]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_pow, ht]
    have hstep := mul_le_sum_of_top_dominated (A := fun j => ‖(C j).eval Y‖)
      (fun j => norm_nonneg _) hgt.le hdom
    -- bound the ratio
    have hupper : ∑ j ∈ Finset.range m, ‖(C j).eval Y‖
        ≤ (∑ j ∈ Finset.range m,
            ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖) * ‖Y‖ ^ d := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : j < m := Finset.mem_range.mp hj
      refine le_trans (norm_eval_le_mul_pow (C j) hY1) ?_
      refine mul_le_mul_of_nonneg_left ?_
        (Finset.sum_nonneg fun i _ => norm_nonneg _)
      refine pow_le_pow_right₀ hY1 ?_
      rw [hd]
      exact Finset.single_le_sum (f := fun j => (C j).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hlowY : ‖(C m).leadingCoeff‖ / 2 * ‖Y‖ ^ (C m).natDegree ≤ ‖(C m).eval Y‖ :=
      hlow Y hz
    have hlowY' : ‖(C m).leadingCoeff‖ / 2 ≤ ‖(C m).eval Y‖ := by
      have h1 : (1 : ℝ) ≤ ‖Y‖ ^ (C m).natDegree := one_le_pow₀ hY1
      nlinarith [hlowY, hlc, h1]
    have hYd : (0 : ℝ) < ‖Y‖ ^ d := by positivity
    have hfinal : ‖(C m).leadingCoeff‖ / 2 * t
        ≤ (∑ j ∈ Finset.range m,
            ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖) * ‖Y‖ ^ d := by
      have : ‖(C m).leadingCoeff‖ / 2 * t ≤ ‖(C m).eval Y‖ * t := by
        nlinarith [hlowY', hgt]
      linarith [this, hstep, hupper]
    rw [hK]
    have hlc2 : (0 : ℝ) < ‖(C m).leadingCoeff‖ / 2 := by positivity
    have hexp : ((∑ j ∈ Finset.range m,
        ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖) * (2 / ‖(C m).leadingCoeff‖))
        * ‖Y‖ ^ d
        = ((∑ j ∈ Finset.range m,
            ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖) * ‖Y‖ ^ d)
          / (‖(C m).leadingCoeff‖ / 2) := by
      field_simp
    have hdiv : t ≤ ((∑ j ∈ Finset.range m,
        ∑ i ∈ Finset.range ((C j).natDegree + 1), ‖(C j).coeff i‖) * ‖Y‖ ^ d)
        / (‖(C m).leadingCoeff‖ / 2) := by
      rw [le_div_iff₀ hlc2]
      linarith [hfinal]
    rw [add_mul, one_mul]
    nlinarith [hdiv, hexp, hYd]

end GaloisForLFunctions.HTGeometry
