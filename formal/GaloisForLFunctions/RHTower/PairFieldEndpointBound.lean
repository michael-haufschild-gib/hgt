import GaloisForLFunctions.RHTower.PairFieldDividedDifference

/-!
# The pair field is bounded by the one-sided fields at the two zeros

The pair field of a consecutive pair is a pointwise value of the regular field somewhere inside the
gap. That value is bounded without knowing where: each term of the regular field is monotone across
the gap in the direction of its own zero, so the left-hand terms are largest at the left endpoint and
the right-hand terms largest at the right endpoint. Hence

  `Δ ≤ Σ_{y < x₁} (x₁ - y)⁻² + Σ_{y > x₂} (x₂ - y)⁻²`,

the one-sided regular fields evaluated at the two zeros themselves. Neither sum has a near-singular
term: the closest contribution on each side is at the distance of the neighbouring gap. So the pair
field of a close pair is controlled by ordinary local spacing data on either side of it, with the
pair's own singularity absent by construction.
-/

namespace RHTower

noncomputable section

/-- A regular term is largest at the endpoint nearest its own zero. -/
theorem regTerm_le_left {y x₁ z : ℝ} (hy : y < x₁) (hz : x₁ ≤ z) :
    ((z - y) ^ (2 : ℕ))⁻¹ ≤ ((x₁ - y) ^ (2 : ℕ))⁻¹ := by
  have h1 : (0 : ℝ) < x₁ - y := sub_pos.mpr hy
  have h2 : (0 : ℝ) < z - y := by linarith
  have hA : (0 : ℝ) < (x₁ - y) ^ (2 : ℕ) := by positivity
  have hB : (0 : ℝ) < (z - y) ^ (2 : ℕ) := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, le_div_iff₀ hA, div_mul_eq_mul_div, div_le_iff₀ hB]
  nlinarith

/-- The mirror bound on the right. -/
theorem regTerm_le_right {y x₂ z : ℝ} (hy : x₂ < y) (hz : z ≤ x₂) :
    ((z - y) ^ (2 : ℕ))⁻¹ ≤ ((x₂ - y) ^ (2 : ℕ))⁻¹ := by
  have h1 : (0 : ℝ) < y - x₂ := sub_pos.mpr hy
  have h2 : (0 : ℝ) < y - z := by linarith
  have hA : (0 : ℝ) < (x₂ - y) ^ (2 : ℕ) := pow_two_pos_of_ne_zero (ne_of_lt (by linarith))
  have hB : (0 : ℝ) < (z - y) ^ (2 : ℕ) := pow_two_pos_of_ne_zero (ne_of_lt (by linarith))
  rw [inv_eq_one_div, inv_eq_one_div, le_div_iff₀ hA, div_mul_eq_mul_div, div_le_iff₀ hB]
  nlinarith

/-- **Endpoint bound for the regular field across a gap.** -/
theorem regField_le_endpoints {S : Finset ℝ} {x₁ x₂ z : ℝ}
    (hS : ∀ y ∈ S, y < x₁ ∨ x₂ < y) (hz1 : x₁ ≤ z) (hz2 : z ≤ x₂) :
    regField S z
      ≤ regField (S.filter (fun y => y < x₁)) x₁
        + regField (S.filter (fun y => ¬ y < x₁)) x₂ := by
  classical
  rw [regField, regField, regField,
    ← Finset.sum_filter_add_sum_filter_not S (fun y => y < x₁)]
  refine add_le_add (Finset.sum_le_sum fun y hy => ?_) (Finset.sum_le_sum fun y hy => ?_)
  · exact regTerm_le_left (Finset.mem_filter.mp hy).2 hz1
  · obtain ⟨hyS, hnot⟩ := Finset.mem_filter.mp hy
    have hy2 : x₂ < y := (hS y hyS).resolve_left hnot
    exact regTerm_le_right hy2 hz2

/-- **The pair field is bounded by the one-sided fields at the two zeros.** -/
theorem pairRegField_le_endpoints {S : Finset ℝ} {x₁ x₂ : ℝ} (hlt : x₁ < x₂)
    (hS : ∀ y ∈ S, y < x₁ ∨ x₂ < y) :
    pairRegField S x₁ x₂
      ≤ regField (S.filter (fun y => y < x₁)) x₁
        + regField (S.filter (fun y => ¬ y < x₁)) x₂ := by
  classical
  obtain ⟨ξ, hξ, heq⟩ := exists_pairRegField_eq_regField hlt hS
  rw [heq]
  exact regField_le_endpoints hS hξ.1.le hξ.2.le

end

end RHTower
