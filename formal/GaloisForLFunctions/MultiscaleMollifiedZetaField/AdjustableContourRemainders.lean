import GaloisForLFunctions.RHTower.ZetaGateFarPairError

/-!
# Adjustable contour remainders for twisted moments

At coefficient length `T^θ`, moving the contour to depth `A` saves
`T^(-(1-2θ)A)`. The dual remainder costs at most one additional power,
uniformly throughout the displacement range used by the product formula.
-/

noncomputable section
open RHTower RHTower.ZetaGateProductAFE
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The original quotient scale retains the exact gap to square-root length. -/
theorem rpow_le_scale_quotient {T c θ : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hcT : c ≤ T ^ (2 * θ)) : T ^ (1 - 2 * θ) ≤ T / c := by
  apply (le_div_iff₀ hc).mpr
  calc
    T ^ (1 - 2 * θ) * c ≤ T ^ (1 - 2 * θ) * T ^ (2 * θ) :=
      mul_le_mul_of_nonneg_left hcT (Real.rpow_nonneg hT.le _)
    _ = T := by
      rw [← Real.rpow_add hT, show 1 - 2 * θ + 2 * θ = (1 : ℝ) by ring, Real.rpow_one]

/-- The smooth diagonal remainder has arbitrary contour depth, uniformly in
both the displacement and the reduced coefficient product. -/
theorem exists_smoothLeft_rpow_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T c θ d : ℝ),
      1 ≤ T → 0 < c → c ≤ T ^ (2 * θ) → 0 < d → d ≤ 1 / 20 →
      ‖smoothLeft (1 / 2 - d) c T‖ ≤ C * T ^ (-(1 - 2 * θ) * farDepth j) := by
  obtain ⟨C, hC, hc⟩ := exists_norm_smoothLeft_le_far j
  refine ⟨C, hC, ?_⟩
  intro T c θ d hT hc0 hcT hd hd20
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  refine (hc (1 / 2 - d) c T (by linarith only [hd20])
    (by linarith only [hd]) hc0 hT0).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  calc
    (T / c) ^ (-farDepth j) ≤ (T ^ (1 - 2 * θ)) ^ (-farDepth j) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _)
        (rpow_le_scale_quotient hT0 hc0 hcT) (by linarith only [one_le_farDepth j])
    _ = _ := by rw [← Real.rpow_mul hT0.le]; congr 1; ring

/-- The dual contour remainder has the same length gap. Its mild dependence
on the displacement is bounded by one extra power of the height. -/
theorem exists_dualLeft_rpow_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T c θ d τ : ℝ),
      8 ≤ T → 1 ≤ c → c ≤ T ^ (2 * θ) → 0 < d → d ≤ 1 / 20 →
      T / 2 ≤ |τ| →
      ‖dualLeft d c T τ‖ ≤ C * T ^ (-(1 - 2 * θ) * farDepth j + 1) := by
  obtain ⟨C, hC, hc⟩ := exists_norm_dualLeft_le_far j
  refine ⟨C * 2 ^ (2 * farDepth j), mul_nonneg hC (by positivity), ?_⟩
  intro T c θ d τ hT hc1 hcT hd hd20 hτ
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hA : 0 ≤ farDepth j := (show 0 ≤ (1 : ℝ) by norm_num).trans (one_le_farDepth j)
  have hdec : -(2 * farDepth j - 2 * d) ≤ 0 := by linarith only [one_le_farDepth j, hd20]
  have hct : 1 ≤ c * T := by nlinarith only [hc1, hT1]
  have hct' : c * T ≤ T ^ (2 * θ + 1) := by
    calc
      c * T ≤ T ^ (2 * θ) * T := mul_le_mul_of_nonneg_right hcT hT0.le
      _ = _ := by rw [Real.rpow_add hT0, Real.rpow_one]
  have hsize : (c * T) ^ farDepth j ≤ T ^ ((2 * θ + 1) * farDepth j) := by
    rw [Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow (by positivity) hct' hA
  have hheight : (1 + |τ|) ^ (-(2 * farDepth j - 2 * d)) ≤
      2 ^ (2 * farDepth j) * T ^ (-(2 * farDepth j) + 1) := by
    calc
      _ ≤ (T / 2) ^ (-(2 * farDepth j - 2 * d)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hτ]) hdec
      _ = 2 ^ (2 * farDepth j - 2 * d) * T ^ (-(2 * farDepth j - 2 * d)) := by
        rw [Real.div_rpow hT0.le (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
        field_simp
      _ ≤ 2 ^ (2 * farDepth j) * T ^ (-(2 * farDepth j) + 1) := by
        exact mul_le_mul
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hd]))
          (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hd20]))
          (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg (by norm_num) _)
  refine (hc d c T τ hd hd20 hc0 hT0 hct (by linarith only [hT, hτ])).trans ?_
  calc
    _ ≤ C * T ^ ((2 * θ + 1) * farDepth j) *
        (2 ^ (2 * farDepth j) * T ^ (-(2 * farDepth j) + 1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsize hC) hheight
        (Real.rpow_nonneg (by positivity) _) (mul_nonneg hC (Real.rpow_nonneg hT0.le _))
    _ = (C * 2 ^ (2 * farDepth j)) *
        (T ^ ((2 * θ + 1) * farDepth j) * T ^ (-(2 * farDepth j) + 1)) := by ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2; ring

/-- Both actual diagonal contour remainders have arbitrary power saving
strictly below square-root coefficient length. -/
theorem exists_contour_power_saving {θ : ℝ} (hθ : θ < 1 / 2) (B : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (T c d : ℝ),
      8 ≤ T → 1 ≤ c → c ≤ T ^ (2 * θ) → 0 < d → d ≤ 1 / 20 →
      ‖smoothLeft (1 / 2 - d) c T‖ ≤ C₁ * T ^ (-B) ∧
      ∀ τ : ℝ, T / 2 ≤ |τ| → ‖dualLeft d c T τ‖ ≤ C₂ * T ^ (-B) := by
  have hgap : 0 < 1 - 2 * θ := by linarith only [hθ]
  obtain ⟨j, hj⟩ := exists_nat_gt ((B + 1) / (1 - 2 * θ))
  have hsave : -(1 - 2 * θ) * farDepth j + 1 ≤ -B := by
    have hh := (div_lt_iff₀ hgap).mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    unfold farDepth
    nlinarith only [hh, hgap, hj0]
  obtain ⟨C₁, hC₁, hs⟩ := exists_smoothLeft_rpow_bound j
  obtain ⟨C₂, hC₂, hd⟩ := exists_dualLeft_rpow_bound j
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro T c d hT hc hcT hd0 hd20
  have hT1 : 1 ≤ T := by linarith only [hT]
  constructor
  · exact (hs T c θ d hT1 (lt_of_lt_of_le zero_lt_one hc) hcT hd0 hd20).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hsave])) hC₁)
  · intro τ hτ
    exact (hd T c θ d τ hT hc hcT hd0 hd20 hτ).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hsave) hC₂)

end GaloisForLFunctions.MultiscaleMollifiedZetaField

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_contour_power_saving
