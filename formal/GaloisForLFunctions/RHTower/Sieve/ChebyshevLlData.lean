import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodData
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLittlewoodDepth

/-!
# The contour data at a rectangle whose width grows with the height

`exists_cheb_littlewood_data` supplies the contour hypotheses at the rectangle of width `A/log T`
for each fixed depth `A`, with constants depending on `A`.  Here the depth grows with the height:

```text
c(T) = 1 - c·log log T/log T ,     d(T) = 1 + 1/log T ,     ‖ζ'/ζ regular‖ ≤ Cr·log²T/log log T ,
```

with `c` and `Cr` absolute.  This is the rectangle the Littlewood region actually provides, and the
only one at which the contour shift can be taken `log log T` times deeper than de la Vallée
Poussin's without the constants degrading.
-/

namespace RHTower.Sieve

open Complex

/-- The left abscissa of the rectangle of width `c·log log T/log T`. -/
noncomputable def chebLeftLl (c T : ℝ) : ℝ := 1 - c * Real.log (Real.log T) / Real.log T

/-- Past `log T = 8` the width is positive. -/
theorem logLog_pos_of_eight {T : ℝ} (hT : 8 ≤ Real.log T) : 0 < Real.log (Real.log T) := by
  refine Real.log_pos ?_
  linarith

theorem chebLeftLl_lt_one {c T : ℝ} (hc : 0 < c) (hT : 8 ≤ Real.log T) :
    chebLeftLl c T < 1 := by
  rw [chebLeftLl]
  have hL : (0 : ℝ) < Real.log T := by linarith
  have : (0 : ℝ) < c * Real.log (Real.log T) / Real.log T := by
    have := logLog_pos_of_eight hT
    positivity
  linarith

theorem half_le_chebLeftLl {c T : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hT : 8 ≤ Real.log T) :
    1 / 2 ≤ chebLeftLl c T := by
  rw [chebLeftLl]
  have hL : (0 : ℝ) < Real.log T := by linarith
  have hone : Real.log (Real.log T) / Real.log T ≤ 1 := logLog_div_log_le_one hL
  have hstep : c * (Real.log (Real.log T) / Real.log T) ≤ c * 1 :=
    mul_le_mul_of_nonneg_left hone hc0.le
  rw [mul_div_assoc]
  linarith

theorem zero_lt_chebLeftLl {c T : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hT : 8 ≤ Real.log T) :
    0 < chebLeftLl c T := by
  have := half_le_chebLeftLl hc0 hc hT; linarith

theorem chebLeftLl_le_chebRightTwo {c T : ℝ} (hc : 0 < c) (hT : 8 ≤ Real.log T) :
    chebLeftLl c T ≤ chebRightTwo T :=
  le_trans (le_of_lt (chebLeftLl_lt_one hc hT)) (le_of_lt (one_lt_chebRightTwo hT))

set_option maxHeartbeats 800000 in
/-- **The contour data at the rectangle of width `c·log log T/log T`.** -/
theorem exists_cheb_ll_data :
    ∃ c Cr L₀ : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < Cr ∧ 8 ≤ L₀ ∧ ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      (∀ s ∈ Set.uIcc (chebLeftLl c T) (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
          riemannZeta s ≠ 0)
      ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
      ∧ (∀ y ∈ Set.Icc (-T) T,
          ‖zetaLogDerivReg ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T))
      ∧ (∀ x ∈ Set.uIoc (chebLeftLl c T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T))
      ∧ (∀ x ∈ Set.uIoc (chebLeftLl c T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T)) := by
  obtain ⟨cr, Cr, L₁, hcr0, hCr0, hL₁, hreg⟩ := exists_bound_zetaLogDerivReg_littlewood_depth
  obtain ⟨cz, L₂, hcz0, hL₂, hzf⟩ := exists_zeta_uniform_littlewood_depth_zero_free
  refine ⟨min (min cr cz) (1 / 2), Cr, max 8 (max L₁ L₂),
    lt_min (lt_min hcr0 hcz0) (by norm_num), min_le_right _ _, hCr0, le_max_left _ _,
    fun T hT1 hT => ?_⟩
  set c : ℝ := min (min cr cz) (1 / 2) with hcdef
  have hc0 : (0 : ℝ) < c := lt_min (lt_min hcr0 hcz0) (by norm_num)
  have hchalf : c ≤ 1 / 2 := min_le_right _ _
  have hccr : c ≤ cr := le_trans (min_le_left _ _) (min_le_left _ _)
  have hccz : c ≤ cz := le_trans (min_le_left _ _) (min_le_right _ _)
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans (le_max_left _ _) hT
  have hL₁T : L₁ ≤ Real.log T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hL₂T : L₂ ≤ Real.log T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hR0 : (0 : ℝ) ≤ Real.log (Real.log T) / Real.log T := by
    have := logLog_pos_of_eight hT8; positivity
  have hcd := chebLeftLl_le_chebRightTwo hc0 hT8
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hcre : ∀ y : ℝ, ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I).re = chebLeftLl c T := by
    intro y; simp
  have hcim : ∀ y : ℝ, ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I).im = y := by
    intro y; simp
  have hxre : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).re = x := by
    intro x u; simp
  have hxim : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).im = u := by
    intro x u; simp
  -- the strip condition at the left abscissa, at both constants
  have hleftz : 1 - cz * Real.log (Real.log T) / Real.log T ≤ chebLeftLl c T :=
    littlewood_depth_mono hccz hR0 (le_of_eq (by rw [chebLeftLl]))
  have hleftr : 1 - cr * Real.log (Real.log T) / Real.log T ≤ chebLeftLl c T :=
    littlewood_depth_mono hccr hR0 (le_of_eq (by rw [chebLeftLl]))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le hTT] at hs
    refine hzf s T hL₂T (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) ?_ hne
    exact le_trans hleftz hs.1.1
  · intro y hy
    rw [Set.uIcc_of_le hTT] at hy
    refine hzf _ T hL₂T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; exact hleftz
    · intro h
      have hh := hcre y
      rw [h] at hh
      simp only [Complex.one_re] at hh
      have := chebLeftLl_lt_one hc0 hT8
      linarith
  · intro y hy
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; exact hleftr
    · rw [hcre]; linarith [chebLeftLl_lt_one hc0 hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim]; rw [abs_of_nonneg (by linarith)]
    · rw [hxre]; linarith [hx.1, hleftr]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim, abs_of_nonpos (by linarith)]; linarith
    · rw [hxre]; linarith [hx.1, hleftr]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]

/-- **The contour data with the plain `log²T` edge bound.**  The `log log T` gain is dropped so the
assembly keeps the exponent-one shape; it survives in
`exists_bound_zetaLogDerivReg_littlewood_depth`. -/
theorem exists_cheb_ll_data_plain :
    ∃ c Cr L₀ : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < Cr ∧ 8 ≤ L₀ ∧ ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      (∀ s ∈ Set.uIcc (chebLeftLl c T) (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
          riemannZeta s ≠ 0)
      ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
      ∧ (∀ y ∈ Set.Icc (-T) T,
          ‖zetaLogDerivReg ((chebLeftLl c T : ℂ) + (y : ℝ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftLl c T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftLl c T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2) := by
  obtain ⟨c, Cr, L₀, hc0, hchalf, hCr0, hL₀, hdata⟩ := exists_cheb_ll_data
  refine ⟨c, Cr, L₀, hc0, hchalf, hCr0, hL₀, fun T hT1 hT => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans hL₀ hT
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log T) := by
    have he : Real.exp 1 ≤ 8 := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he hT8)
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log T) := by linarith
  have hweak : Cr * Real.log T ^ 2 / Real.log (Real.log T) ≤ Cr * Real.log T ^ 2 := by
    rw [div_le_iff₀ hLL0]
    nlinarith [mul_nonneg (mul_nonneg hCr0.le (sq_nonneg (Real.log T)))
      (by linarith : (0 : ℝ) ≤ Real.log (Real.log T) - 1)]
  exact ⟨h1, h2, fun y hy => le_trans (h3 y hy) hweak,
    fun x hx => le_trans (h4 x hx) hweak, fun x hx => le_trans (h5 x hx) hweak⟩

end RHTower.Sieve
