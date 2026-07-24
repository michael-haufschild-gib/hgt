import GaloisForLFunctions.RHTower.ZetaThreeFourOne
import GaloisForLFunctions.RHTower.ZetaDerivGrowth

/-!
# The de la Vallée Poussin zero-free region

`ζ(β + it) ≠ 0` whenever `|t| ≥ 9` and `β > 1 − c/log⁹|t|`, with the
explicit constant `c = 1/(2·27·28·224⁴)`.

If ζ vanished at `β + it`, the mean value along `[β, 1+x]` (derivative
controlled by the `112·log²` bound) would force
`|ζ(1+x+it)| ≤ 224·x·log²|t|` at `x = c/log⁹|t|`; against the pole cube
`(3/x)³` and the height-`2t` growth `28·log|t|`, the 3-4-1 product
inequality would collapse to `1 ≤ 1/2`.
-/

noncomputable section

namespace RHTower

open Set

/-- The zero-free constant `1/(2·27·28·224⁴)`. -/
def zetaZeroFreeC : ℝ := 1 / (2 * (27 * 28 * 224 ^ 4))

theorem zetaZeroFreeC_pos : 0 < zetaZeroFreeC := by
  rw [zetaZeroFreeC]
  norm_num

theorem zetaZeroFreeC_le_half : zetaZeroFreeC ≤ 1 / 2 := by
  rw [zetaZeroFreeC]
  norm_num

/-- **Mean value from a zero**: if `ζ(β+it) = 0`, the value at `σ'+it`
is bounded by `112·log²|t|·(σ'−β)` along the segment inside the
derivative-growth region. -/
theorem norm_riemannZeta_le_of_zero {β σ' t : ℝ} (ht : 9 ≤ |t|)
    (hβ1 : 1 - 1 / (4 * Real.log |t|) ≤ β) (hβσ : β < σ')
    (hσ2 : σ' ≤ 3 / 2)
    (hzero : riemannZeta (↑β + ↑t * Complex.I) = 0) :
    ‖riemannZeta (↑σ' + ↑t * Complex.I)‖
      ≤ 112 * Real.log |t| ^ 2 * (σ' - β) := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  -- pointwise differentiability of the horizontal restriction
  have hf : ∀ u : ℝ, HasDerivAt (fun v : ℝ => riemannZeta (↑v + ↑t * Complex.I))
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
  have hkey := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound σ'
    (Set.right_mem_Icc.2 hβσ.le)
  rw [hzero, sub_zero] at hkey
  exact hkey

set_option maxHeartbeats 3200000 in
/-- **The de la Vallée Poussin zero-free region**:
`ζ(β+it) ≠ 0` for `|t| ≥ 9` and `β > 1 − c/log⁹|t|`. -/
theorem riemannZeta_ne_zero_of_re_gt_one_sub {β t : ℝ} (ht : 9 ≤ |t|)
    (hβ : 1 - zetaZeroFreeC / Real.log |t| ^ 9 < β) :
    riemannZeta (↑β + ↑t * Complex.I) ≠ 0 := by
  intro hzero
  have ht0 : (0 : ℝ) < |t| := by linarith
  -- `log|t| > 2`
  have hexp2 : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
      nlinarith [Real.exp_pos 1]
    rw [h2]
    nlinarith [h3]
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hL9 : (2 : ℝ) ^ 9 < Real.log |t| ^ 9 := by
    exact pow_lt_pow_left₀ hlogt2 (by norm_num) (by norm_num)
  have hL90 : (0 : ℝ) < Real.log |t| ^ 9 := by positivity
  -- `β < 1` (else mathlib's nonvanishing applies)
  have hβ1 : β < 1 := by
    by_contra h
    rw [not_lt] at h
    have hre : (↑β + ↑t * Complex.I).re = β := by
      simp [Complex.add_re, Complex.mul_re]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact h) hzero
  -- the working scale
  have hx0 : (0 : ℝ) < zetaZeroFreeC / Real.log |t| ^ 9 :=
    div_pos zetaZeroFreeC_pos hL90
  have hx1 : zetaZeroFreeC / Real.log |t| ^ 9 ≤ 1 := by
    calc zetaZeroFreeC / Real.log |t| ^ 9
        ≤ zetaZeroFreeC / 2 ^ 9 := by
          apply div_le_div_of_nonneg_left zetaZeroFreeC_pos.le
            (by norm_num) hL9.le
      _ ≤ 1 := by
          have := zetaZeroFreeC_le_half
          rw [zetaZeroFreeC] at *
          norm_num
  have hxhalf : zetaZeroFreeC / Real.log |t| ^ 9 ≤ 1 / 2 := by
    calc zetaZeroFreeC / Real.log |t| ^ 9
        ≤ zetaZeroFreeC / 2 ^ 9 := by
          apply div_le_div_of_nonneg_left zetaZeroFreeC_pos.le
            (by norm_num) hL9.le
      _ ≤ 1 / 2 := by
          rw [zetaZeroFreeC]
          norm_num
  have hβfloor : 1 - 1 / (4 * Real.log |t|) ≤ β := by
    have h1 : zetaZeroFreeC / Real.log |t| ^ 9
        ≤ 1 / (4 * Real.log |t|) := by
      rw [div_le_div_iff₀ hL90 (by positivity)]
      have h2 : Real.log |t| ^ 9 = Real.log |t| ^ 8 * Real.log |t| := by
        ring
      have h3 : (2 : ℝ) ^ 8 ≤ Real.log |t| ^ 8 :=
        pow_le_pow_left₀ (by norm_num) hlogt2.le 8
      have h4 : zetaZeroFreeC * (4 * Real.log |t|)
          ≤ 4 * Real.log |t| := by
        nlinarith [zetaZeroFreeC_le_half, zetaZeroFreeC_pos, hL0]
      nlinarith [hL0]
    linarith
  -- the mean value at `σ' := 1 + x`
  have hmid : ‖riemannZeta (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
      + ↑t * Complex.I)‖
      ≤ 224 * (zetaZeroFreeC / Real.log |t| ^ 9)
        * Real.log |t| ^ 2 := by
    have h1 := norm_riemannZeta_le_of_zero ht hβfloor
      (show β < 1 + zetaZeroFreeC / Real.log |t| ^ 9 by linarith)
      (by linarith) hzero
    refine le_trans h1 ?_
    have h2 : 1 + zetaZeroFreeC / Real.log |t| ^ 9 - β
        ≤ 2 * (zetaZeroFreeC / Real.log |t| ^ 9) := by
      linarith
    nlinarith [sq_nonneg (Real.log |t|), hx0]
  -- the pole bound
  have hpole : ‖riemannZeta (1 + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ))‖
      ≤ 3 / (zetaZeroFreeC / Real.log |t| ^ 9) := by
    have h1 := abs_riemannZeta_one_add_le hx0
    have h2 : 1 / (zetaZeroFreeC / Real.log |t| ^ 9) + 2
        ≤ 3 / (zetaZeroFreeC / Real.log |t| ^ 9) := by
      have h3 : 2 ≤ 2 / (zetaZeroFreeC / Real.log |t| ^ 9) := by
        rw [le_div_iff₀ hx0]
        linarith
      have h4 : 1 / (zetaZeroFreeC / Real.log |t| ^ 9)
          + 2 / (zetaZeroFreeC / Real.log |t| ^ 9)
          = 3 / (zetaZeroFreeC / Real.log |t| ^ 9) := by
        ring
      linarith
    linarith
  -- the height-`2t` bound
  have hhigh : ‖riemannZeta (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
      + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤ 28 * Real.log |t| := by
    have h2t : (8 : ℝ) ≤ |2 * t| := by
      rw [abs_mul]
      simp only [abs_two]
      linarith
    have h2t0 : (0 : ℝ) < |2 * t| := by linarith
    have h1 := abs_riemannZeta_le_log h2t
      (show 1 - 1 / Real.log |2 * t| ≤ 1 + zetaZeroFreeC / Real.log |t| ^ 9 by
        have h2 : (0 : ℝ) < Real.log |2 * t| := by
          have := Real.log_le_log (by norm_num : (0:ℝ) < 8) h2t
          have h3 : (0:ℝ) < Real.log 8 := Real.log_pos (by norm_num)
          linarith
        have h4 : 0 < 1 / Real.log |2 * t| := by positivity
        linarith)
      (show 1 + zetaZeroFreeC / Real.log |t| ^ 9 ≤ 2 by linarith)
    refine le_trans h1 ?_
    have h5 : Real.log |2 * t| ≤ 2 * Real.log |t| := by
      have h6 : |2 * t| ≤ |t| ^ 2 := by
        rw [abs_mul]
        simp only [abs_two]
        nlinarith
      have h7 := Real.log_le_log h2t0 h6
      rwa [Real.log_pow, Nat.cast_ofNat] at h7
    linarith
  -- the 3-4-1 collapse
  have hprod := norm_zeta_product_ge_one hx0 t
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  -- align the three arguments
  have harg1 : (1 : ℂ) + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
      = 1 + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ) := rfl
  have harg2 : (1 : ℂ) + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
      + Complex.I * ↑t
      = ((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  have harg3 : (1 : ℂ) + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
      + 2 * Complex.I * ↑t
      = ((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg2, harg3] at hprod
  -- the bounded product
  have hnn1 : (0 : ℝ) ≤ ‖riemannZeta (1
      + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ))‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖riemannZeta
      (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ) + ↑t * Complex.I)‖ :=
    norm_nonneg _
  have hnn3 : (0 : ℝ) ≤ ‖riemannZeta
      (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
        + ((2 * t : ℝ) : ℂ) * Complex.I)‖ := norm_nonneg _
  have hb1 := pow_le_pow_left₀ hnn1 hpole 3
  have hb2 := pow_le_pow_left₀ hnn2 hmid 4
  have hchain : ‖riemannZeta (1 + ((zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ))‖ ^ 3
      * ‖riemannZeta (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
          + ↑t * Complex.I)‖ ^ 4
      * ‖riemannZeta (((1 + zetaZeroFreeC / Real.log |t| ^ 9 : ℝ) : ℂ)
          + ((2 * t : ℝ) : ℂ) * Complex.I)‖
      ≤ (3 / (zetaZeroFreeC / Real.log |t| ^ 9)) ^ 3
        * (224 * (zetaZeroFreeC / Real.log |t| ^ 9)
            * Real.log |t| ^ 2) ^ 4
        * (28 * Real.log |t|) := by
    apply mul_le_mul
    · apply mul_le_mul hb1 hb2 (by positivity) (by positivity)
    · exact hhigh
    · exact norm_nonneg _
    · positivity
  have hfinal : (3 / (zetaZeroFreeC / Real.log |t| ^ 9)) ^ 3
      * (224 * (zetaZeroFreeC / Real.log |t| ^ 9)
          * Real.log |t| ^ 2) ^ 4
      * (28 * Real.log |t|) = 1 / 2 := by
    have hc0 : zetaZeroFreeC ≠ 0 := ne_of_gt zetaZeroFreeC_pos
    have hL90' : Real.log |t| ^ 9 ≠ 0 := ne_of_gt hL90
    rw [zetaZeroFreeC]
    rw [zetaZeroFreeC] at hc0
    field_simp
    ring
  rw [hfinal] at hchain
  linarith [hprod, hchain]

end RHTower
