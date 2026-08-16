import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityExplicit

namespace RHTower.Sieve

noncomputable section

/-- The complete detector degeneration has inverse-gap degree seven: one degree from converting
weighted mass to count, two from pole clearing, and four from the moving-right divisor-square
Dirichlet series. -/
theorem exists_uniformGabrielExplicitFactor_le_gapPower :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
        (1 / (1 - sigma)) *
            (((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
                (2 : ℕ) *
              (1 + inghamMovingRightTranslatedExplicitConstant
                ((9 / 100 : ℝ) * (1 - sigma)))) ≤
          C * (1 + 1 / (1 - sigma)) ^ (7 : ℕ) := by
  let C0 : ℝ := Real.exp 8 *
    (5 * Real.pi * Real.exp 1 +
      (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ)))
  let r : ℝ := 100 / 9
  let CR : ℝ := 1 + C0 * r ^ (4 : ℕ)
  let C : ℝ := (Real.exp 1) ^ (2 : ℕ) * CR
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hr1 : 1 ≤ r := by dsimp only [r]; norm_num
  have hCR : 0 ≤ CR := by dsimp only [CR]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma0 hsigma1
  let d : ℝ := 1 - sigma
  let g : ℝ := 1 + 1 / d
  let delta : ℝ := (9 / 100 : ℝ) * d
  have hd : 0 < d := by dsimp only [d]; positivity
  have hinv0 : 0 ≤ 1 / d := by positivity
  have hg1 : 1 ≤ g := by dsimp only [g]; linarith
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hcenterGap :
      1 - inghamUniformGabrielCenter sigma = (1001 / 1000 : ℝ) * d := by
    dsimp only [d]
    unfold inghamUniformGabrielCenter
    ring
  have hdCenter : d ≤ (1001 / 1000 : ℝ) * d := by
    nlinarith
  have hcenterInv :
      1 / (1 - inghamUniformGabrielCenter sigma) ≤ 1 / d := by
    rw [hcenterGap]
    exact one_div_le_one_div_of_le hd hdCenter
  have hcenterInv0 :
      0 ≤ 1 / (1 - inghamUniformGabrielCenter sigma) := by
    rw [hcenterGap]
    positivity
  have hcenterBase :
      1 + 1 / (1 - inghamUniformGabrielCenter sigma) ≤ g := by
    dsimp only [g]
    linarith
  have hrawBase :
      (1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1 ≤
        g * Real.exp 1 :=
    mul_le_mul_of_nonneg_right hcenterBase (Real.exp_pos _).le
  have hraw0 :
      0 ≤ (1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1 := by
    positivity
  have hrawSq :
      ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
          (2 : ℕ) ≤
        (Real.exp 1) ^ (2 : ℕ) * g ^ (2 : ℕ) := by
    calc
      _ ≤ (g * Real.exp 1) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hraw0 hrawBase 2
      _ = (Real.exp 1) ^ (2 : ℕ) * g ^ (2 : ℕ) := by ring
  have hdeltaInv : 1 / delta = r * (1 / d) := by
    have hdne : d ≠ 0 := hd.ne'
    dsimp only [delta, r]
    field_simp [hdne]
  have hrightBase : 1 + 1 / delta ≤ r * g := by
    rw [hdeltaInv]
    dsimp only [g]
    nlinarith
  have hrightPow :
      (1 + 1 / delta) ^ (4 : ℕ) ≤ r ^ (4 : ℕ) * g ^ (4 : ℕ) := by
    calc
      _ ≤ (r * g) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hrightBase 4
      _ = r ^ (4 : ℕ) * g ^ (4 : ℕ) := by ring
  have hrightEq :
      inghamMovingRightTranslatedExplicitConstant delta =
        C0 * (1 + 1 / delta) ^ (4 : ℕ) := by
    dsimp only [inghamMovingRightTranslatedExplicitConstant, C0]
    ring
  have hright :
      1 + inghamMovingRightTranslatedExplicitConstant delta ≤
        CR * g ^ (4 : ℕ) := by
    rw [hrightEq]
    calc
      1 + C0 * (1 + 1 / delta) ^ (4 : ℕ) ≤
          1 + C0 * (r ^ (4 : ℕ) * g ^ (4 : ℕ)) :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hrightPow hC0)
      _ ≤ g ^ (4 : ℕ) + C0 * (r ^ (4 : ℕ) * g ^ (4 : ℕ)) :=
        add_le_add (one_le_pow₀ hg1) (le_refl _)
      _ = CR * g ^ (4 : ℕ) := by dsimp only [CR]; ring
  have hinvle : 1 / d ≤ g := by dsimp only [g]; linarith
  have hrawSq0 :
      0 ≤ ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
        (2 : ℕ) := sq_nonneg _
  have hright0 :
      0 ≤ 1 + inghamMovingRightTranslatedExplicitConstant delta := by
    rw [hrightEq]
    positivity
  calc
    (1 / (1 - sigma)) *
          (((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant
              ((9 / 100 : ℝ) * (1 - sigma)))) =
        (1 / d) *
          (((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant delta)) := by rfl
    _ ≤ g *
          (((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant delta)) :=
      mul_le_mul_of_nonneg_right hinvle (mul_nonneg hrawSq0 hright0)
    _ ≤ g * (((Real.exp 1) ^ (2 : ℕ) * g ^ (2 : ℕ)) *
          (1 + inghamMovingRightTranslatedExplicitConstant delta)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrawSq hright0) hg0
    _ ≤ g * (((Real.exp 1) ^ (2 : ℕ) * g ^ (2 : ℕ)) *
          (CR * g ^ (4 : ℕ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hright (by positivity)) hg0
    _ = C * g ^ (7 : ℕ) := by dsimp only [C]; ring
    _ = C * (1 + 1 / (1 - sigma)) ^ (7 : ℕ) := by rfl

end

end RHTower.Sieve
