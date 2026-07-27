import GaloisForLFunctions.RHTower.ZetaZeroFreeRegion

/-!
# Lower bounds for ζ right of the one-line

From the 3-4-1 inequality against the pole cube and the height-`2t`
growth:

`x³/(756·log|t|) ≤ ‖ζ(1+x+it)‖⁴`  (0 < x ≤ 1, |t| ≥ 9),

stated in fourth-power form to stay root-free; and the two-point
segment estimate `‖ζ(σ'+it) − ζ(β+it)‖ ≤ 112·log²|t|·(σ'−β)` — the
bridge that will carry the lower bound left of the one-line into the
zero-free region, where it feeds the `ζ′/ζ` bounds of the Perron
contour.
-/

noncomputable section

namespace RHTower

open Set

/-- **Two-point segment estimate** inside the derivative-growth
region. -/
theorem norm_riemannZeta_sub_le_segment {β σ' t : ℝ} (ht : 9 ≤ |t|)
    (hβ1 : 1 - 1 / (4 * Real.log |t|) ≤ β) (hβσ : β < σ')
    (hσ2 : σ' ≤ 3 / 2) :
    ‖riemannZeta (↑σ' + ↑t * Complex.I)
        - riemannZeta (↑β + ↑t * Complex.I)‖
      ≤ 112 * Real.log |t| ^ 2 * (σ' - β) := by
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hf : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => riemannZeta (↑v + ↑t * Complex.I))
      (deriv riemannZeta (↑u + ↑t * Complex.I)) u := by
    intro u
    have hne : (↑u + ↑t * Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.im h
      simp [Complex.add_im, Complex.mul_im] at h2
      exact htne h2
    have h1 : HasDerivAt (fun z : ℂ => z + ↑t * Complex.I) 1 ↑u :=
      (hasDerivAt_id _).add_const _
    have h2 : HasDerivAt riemannZeta
        (deriv riemannZeta (↑u + ↑t * Complex.I))
        (↑u + ↑t * Complex.I) :=
      (differentiableAt_riemannZeta hne).hasDerivAt
    have h3 := (h2.comp (↑u : ℂ) h1)
    simp only [mul_one] at h3
    exact h3.comp_ofReal
  have hdiff : DifferentiableOn ℝ
      (fun v : ℝ => riemannZeta (↑v + ↑t * Complex.I)) (Set.Icc β σ') :=
    fun u _ => (hf u).differentiableAt.differentiableWithinAt
  have hbound : ∀ u ∈ Set.Ico β σ',
      ‖derivWithin (fun v : ℝ => riemannZeta (↑v + ↑t * Complex.I))
        (Set.Icc β σ') u‖ ≤ 112 * Real.log |t| ^ 2 := by
    intro u hu
    rw [(hf u).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hβσ) u (Set.mem_Icc_of_Ico hu))]
    apply abs_deriv_riemannZeta_le_sq_log ht
    · linarith [hu.1]
    · linarith [hu.2]
  exact norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound σ'
    (Set.right_mem_Icc.2 hβσ.le)

set_option maxHeartbeats 1600000 in
/-- **Quartic lower bound** right of the one-line:
`x³/(756·log|t|) ≤ ‖ζ(1+x+it)‖⁴`. -/
theorem pow_four_norm_riemannZeta_ge {x t : ℝ} (ht : 9 ≤ |t|)
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ^ 3 / (756 * Real.log |t|)
      ≤ ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  -- `log|t| > 2`
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  -- the pole bound sharpened by `x ≤ 1`
  have hpole : ‖riemannZeta (1 + (x : ℂ))‖ ≤ 3 / x := by
    have h1 := abs_riemannZeta_one_add_le hx0
    have h3 : 2 ≤ 2 / x := by
      rw [le_div_iff₀ hx0]
      linarith
    have h4 : 1 / x + 2 / x = 3 / x := by ring
    linarith
  -- the height-`2t` bound
  have hhigh : ‖riemannZeta (((1 + x : ℝ) : ℂ)
      + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤ 28 * Real.log |t| := by
    have h2t : (8 : ℝ) ≤ |2 * t| := by
      rw [abs_mul]
      simp only [abs_two]
      linarith
    have h2t0 : (0 : ℝ) < |2 * t| := by linarith
    have h1 := abs_riemannZeta_le_log h2t
      (show 1 - 1 / Real.log |2 * t| ≤ 1 + x by
        have h2 : (0 : ℝ) < Real.log |2 * t| := by
          have := Real.log_le_log (by norm_num : (0:ℝ) < 8) h2t
          have h3 : (0:ℝ) < Real.log 8 := Real.log_pos (by norm_num)
          linarith
        have h4 : 0 < 1 / Real.log |2 * t| := by positivity
        linarith)
      (show 1 + x ≤ 2 by linarith)
    refine le_trans h1 ?_
    have h5 : Real.log |2 * t| ≤ 2 * Real.log |t| := by
      have h6 : |2 * t| ≤ |t| ^ 2 := by
        rw [abs_mul]
        simp only [abs_two]
        nlinarith
      have h7 := Real.log_le_log h2t0 h6
      rwa [Real.log_pow, Nat.cast_ofNat] at h7
    linarith
  -- the product inequality with aligned arguments
  have hprod := norm_zeta_product_ge_one hx0 t
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have harg2 : (1 : ℂ) + ↑x + Complex.I * ↑t
      = ((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  have harg3 : (1 : ℂ) + ↑x + 2 * Complex.I * ↑t
      = ((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg2, harg3] at hprod
  -- extract the quartic bound
  have hnn1 : (0 : ℝ) ≤ ‖riemannZeta (1 + (x : ℂ))‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖riemannZeta (((1 + x : ℝ) : ℂ)
      + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hb1 := pow_le_pow_left₀ hnn1 hpole 3
  have hchain : ‖riemannZeta (1 + (x : ℂ))‖ ^ 3
      * ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
      * ‖riemannZeta (((1 + x : ℝ) : ℂ)
          + ((2 * t : ℝ) : ℂ) * Complex.I)‖
      ≤ (3 / x) ^ 3
        * ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
        * (28 * Real.log |t|) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hb1 (by positivity)
    · exact hhigh
    · exact norm_nonneg _
    · positivity
  have h1 := le_trans hprod hchain
  -- solve for the quartic factor
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  have hK : (0 : ℝ) < (3 / x) ^ 3 * (28 * Real.log |t|) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 756 * Real.log |t|)]
  have h2 : (3 / x) ^ 3
      * ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
      * (28 * Real.log |t|)
      = ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
        * (756 * Real.log |t|) / x ^ 3 := by
    field_simp
    ring
  rw [h2] at h1
  rw [le_div_iff₀ hx3] at h1
  linarith

end RHTower
