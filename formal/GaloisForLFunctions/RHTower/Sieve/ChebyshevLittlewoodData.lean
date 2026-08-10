import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneData
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLittlewood

/-!
# The contour data at a rectangle of arbitrary exponent-one width

`exists_cheb_kappa_one_data` supplies the five hypotheses of the Chebyshev contour bound at the
rectangle of width `1/40000/log T`, with the single bound `Cr log²T`.  Both the width constant and
the bound come from the exponent-one region.

At Littlewood strength the width constant is free and the bound carries an extra `log log T`:

```text
c(T) = 1 - A/log T,     d(T) = 1 + 1/log T,     ‖ζ'/ζ regular‖ ≤ Cr·log²T/log log T ,
```

for every `A > 0`.  The contour shift can therefore be taken `A` times deeper at a cost that is
`log log T` times smaller, which is the whole content of the Littlewood improvement for the prime
number theorem.
-/

namespace RHTower.Sieve

open Complex

/-- The left abscissa of the rectangle of width `A/log T`. -/
noncomputable def chebLeftLw (A T : ℝ) : ℝ := 1 - A / Real.log T

theorem chebLeftLw_lt_one {A T : ℝ} (hA : 0 < A) (hT : 8 ≤ Real.log T) :
    chebLeftLw A T < 1 := by
  rw [chebLeftLw]
  have : (0 : ℝ) < A / Real.log T := div_pos hA (by linarith)
  linarith

theorem half_le_chebLeftLw {A T : ℝ} (hT : 8 ≤ Real.log T)
    (hTA : 2 * A ≤ Real.log T) : 1 / 2 ≤ chebLeftLw A T := by
  rw [chebLeftLw]
  have h : A / Real.log T ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem zero_lt_chebLeftLw {A T : ℝ} (hT : 8 ≤ Real.log T)
    (hTA : 2 * A ≤ Real.log T) : 0 < chebLeftLw A T := by
  have := half_le_chebLeftLw hT hTA; linarith

theorem chebLeftLw_le_chebRightTwo {A T : ℝ} (hA : 0 < A) (hT : 8 ≤ Real.log T) :
    chebLeftLw A T ≤ chebRightTwo T :=
  le_trans (le_of_lt (chebLeftLw_lt_one hA hT)) (le_of_lt (one_lt_chebRightTwo hT))

set_option maxHeartbeats 800000 in
/-- **The contour data at the rectangle of width `A/log T`, at Littlewood strength.** -/
theorem exists_cheb_littlewood_data (A : ℝ) (hA : 0 < A) :
    ∃ Cr L₀ : ℝ, 0 < Cr ∧ max 8 (2 * A) ≤ L₀ ∧ ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      (∀ s ∈ Set.uIcc (chebLeftLw A T) (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
          riemannZeta s ≠ 0)
      ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
      ∧ (∀ y ∈ Set.Icc (-T) T,
          ‖zetaLogDerivReg ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T))
      ∧ (∀ x ∈ Set.uIoc (chebLeftLw A T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T))
      ∧ (∀ x ∈ Set.uIoc (chebLeftLw A T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T)) := by
  obtain ⟨Cr, L₁, hCr0, hL₁1, hreg⟩ := exists_bound_zetaLogDerivReg_uniform_littlewood A hA
  obtain ⟨L₂, hL₂1, hzf⟩ := exists_zeta_uniform_arbitrary_zero_free A hA
  refine ⟨Cr, max (max 8 (2 * A)) (max L₁ L₂), hCr0, le_max_left _ _, fun T hT1 hT => ?_⟩
  have hT8 : (8 : ℝ) ≤ Real.log T :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hTA : 2 * A ≤ Real.log T :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hL₁T : L₁ ≤ Real.log T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hL₂T : L₂ ≤ Real.log T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hcd := chebLeftLw_le_chebRightTwo hA hT8
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hcre : ∀ y : ℝ, ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I).re = chebLeftLw A T := by
    intro y; simp
  have hcim : ∀ y : ℝ, ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I).im = y := by
    intro y; simp
  have hxre : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).re = x := by
    intro x u; simp
  have hxim : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).im = u := by
    intro x u; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le hTT] at hs
    refine hzf s T hL₂T (le_trans (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) le_rfl) ?_ hne
    simpa [chebLeftLw] using hs.1.1
  · intro y hy
    rw [Set.uIcc_of_le hTT] at hy
    refine hzf _ T hL₂T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; simp [chebLeftLw]
    · intro h
      have hh := hcre y
      rw [h] at hh
      simp only [Complex.one_re] at hh
      have := chebLeftLw_lt_one hA hT8
      linarith
  · intro y hy
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; simp [chebLeftLw]
    · rw [hcre]; linarith [chebLeftLw_lt_one hA hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd, chebLeftLw] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim]; rw [abs_of_nonneg (by linarith)]
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd, chebLeftLw] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim, abs_of_nonpos (by linarith)]; linarith
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]

/-- **The contour data with the plain `log²T` bound.**  The `log log T` gain is dropped so that the
assembly keeps the exponent-one shape exactly; it survives in
`exists_bound_zetaLogDerivReg_uniform_littlewood`. -/
theorem exists_cheb_littlewood_data_plain (A : ℝ) (hA : 0 < A) :
    ∃ Cr L₀ : ℝ, 0 < Cr ∧ max 8 (2 * A) ≤ L₀ ∧ ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      (∀ s ∈ Set.uIcc (chebLeftLw A T) (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
          riemannZeta s ≠ 0)
      ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
      ∧ (∀ y ∈ Set.Icc (-T) T,
          ‖zetaLogDerivReg ((chebLeftLw A T : ℂ) + (y : ℝ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftLw A T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftLw A T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
            ≤ Cr * Real.log T ^ 2) := by
  obtain ⟨Cr, L₀, hCr0, hL₀, hdata⟩ := exists_cheb_littlewood_data A hA
  refine ⟨Cr, L₀, hCr0, hL₀, fun T hT1 hT => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans (le_trans (le_max_left _ _) hL₀) hT
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
