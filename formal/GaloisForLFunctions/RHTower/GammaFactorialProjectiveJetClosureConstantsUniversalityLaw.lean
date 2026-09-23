import GaloisForLFunctions.HTGeometry.GammaFactorialThirdJetHarmonicResidue

/-!
# Gamma factorial projective-jet closure constants universality

The first, ordinary second, homogeneous projective-second, and projective-third factorial
Gamma defects have different powers of the observation point and microscope scale. Two
nonlinear raw-defect ratios cancel both nuisance quantities and converge to the universal
constants `-1/9` and `-1/6`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Homogeneous projective-second times first defect, normalized by the square of the ordinary
second defect. -/
def gammaFactorialProjectiveSecondFirstClosureRatio
    (n : ℕ) (x : ℂ) : ℂ :=
  GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x *
      GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
    GaloisForLFunctions.gammaFactorialSecondJetDefect n x ^ (2 : ℕ)

/-- Projective-third defect normalized by the square of the ordinary second defect. -/
def gammaFactorialProjectiveThirdSecondClosureRatio
    (n : ℕ) (x : ℂ) : ℂ :=
  GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
    GaloisForLFunctions.gammaFactorialSecondJetDefect n x ^ (2 : ℕ)

theorem tendsto_gammaFactorialProjectiveSecondFirstClosureRatio
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => gammaFactorialProjectiveSecondFirstClosureRatio n x)
      atTop (𝓝 (-1 / 9)) := by
  have hfirst :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (-2 / x)) :=
    GaloisForLFunctions.tendsto_gammaFactorialFirstJetDefect_div_harmonicScale hx
  have hsecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (6 / x ^ (2 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx
  have hprojectiveSecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (2 / x ^ (3 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale hx
  have hsecond_ne : (6 / x ^ (2 : ℕ) : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hnormalized :=
    (hprojectiveSecond.mul hfirst).div (hsecond.pow 2)
      (pow_ne_zero 2 hsecond_ne)
  have hvalue :
      ((2 / x ^ (3 : ℕ) : ℂ) * (-2 / x)) / (6 / x ^ (2 : ℕ)) ^ (2 : ℕ) = -1 / 9 := by
    field_simp [hx]
    norm_num
  rw [hvalue] at hnormalized
  have heq : ∀ᶠ n : ℕ in atTop,
      ((GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n) *
        (GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)) /
          (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) ^ (2 : ℕ) =
        gammaFactorialProjectiveSecondFirstClosureRatio n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    by_cases hsecondZero :
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x = 0
    · simp [gammaFactorialProjectiveSecondFirstClosureRatio, hsecondZero]
    · have hscale :=
        GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn
      rw [gammaFactorialProjectiveSecondFirstClosureRatio]
      field_simp [hsecondZero, hscale]
  exact hnormalized.congr' heq

theorem tendsto_gammaFactorialProjectiveThirdSecondClosureRatio
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => gammaFactorialProjectiveThirdSecondClosureRatio n x)
      atTop (𝓝 (-1 / 6)) := by
  have hsecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (6 / x ^ (2 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx
  have hprojectiveThird :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n ^ (2 : ℕ))
        atTop (𝓝 (-6 / x ^ (4 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq hx
  have hsecond_ne : (6 / x ^ (2 : ℕ) : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hnormalized :=
    hprojectiveThird.div (hsecond.pow 2) (pow_ne_zero 2 hsecond_ne)
  have hvalue :
      (-6 / x ^ (4 : ℕ) : ℂ) / (6 / x ^ (2 : ℕ)) ^ (2 : ℕ) = -1 / 6 := by
    field_simp [hx]
  rw [hvalue] at hnormalized
  have heq : ∀ᶠ n : ℕ in atTop,
      (GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n ^ (2 : ℕ)) /
          (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
            GaloisForLFunctions.gammaHarmonicMicroscopeScale n) ^ (2 : ℕ) =
        gammaFactorialProjectiveThirdSecondClosureRatio n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    by_cases hsecondZero :
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x = 0
    · simp [gammaFactorialProjectiveThirdSecondClosureRatio, hsecondZero]
    · have hscale :=
        GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn
      rw [gammaFactorialProjectiveThirdSecondClosureRatio]
      field_simp [hsecondZero, hscale]
  exact hnormalized.congr' heq

/-- **Gamma factorial projective-jet closure constants law.** Two nonlinear combinations of
raw defects eliminate both microscope scale and observation point. -/
theorem gammaFactorial_projectiveJetClosureConstantsUniversality :
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n => gammaFactorialProjectiveSecondFirstClosureRatio n x)
        atTop (𝓝 (-1 / 9)) ∧
      Tendsto (fun n => gammaFactorialProjectiveThirdSecondClosureRatio n x)
        atTop (𝓝 (-1 / 6)) ∧
      (-1 / 9 : ℂ) ≠ 0 ∧
      (-1 / 6 : ℂ) ≠ 0 := by
  intro x hx
  exact ⟨tendsto_gammaFactorialProjectiveSecondFirstClosureRatio hx,
    tendsto_gammaFactorialProjectiveThirdSecondClosureRatio hx,
    by norm_num, by norm_num⟩

end

end GaloisForLFunctions.RHTower
