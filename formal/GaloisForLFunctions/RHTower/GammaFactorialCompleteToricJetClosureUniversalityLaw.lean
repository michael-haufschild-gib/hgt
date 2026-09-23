import GaloisForLFunctions.HTGeometry.GammaFactorialExponentialEnvelopeEscape
import GaloisForLFunctions.RHTower.GammaFactorialProjectiveJetClosureConstantsUniversalityLaw

/-!
# Complete toric closure of the Gamma factorial jet hierarchy

Six independently normalized Gamma factorial defects and the harmonic factor carry three nuisance
weights: factorial scale, harmonic scale, and observation point. Four nonlinear ratios form an
integer basis of every Laurent monomial that cancels all three weights. Their universal limits are
`-1/9`, `-1/6`, `-π²/9`, and `729`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Log-curvature defect with its factorial scale converted to harmonic scale, normalized by the
square of the ordinary second-jet defect. -/
def gammaFactorialLogSecondHarmonicClosureRatio
    (n : ℕ) (x : ℂ) : ℂ :=
  GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x *
      (harmonic n : ℂ) ^ (2 : ℕ) /
    GaloisForLFunctions.gammaFactorialSecondJetDefect n x ^ (2 : ℕ)

/-- Sixth-power transition closing the log/envelope and first/second jet ratios. -/
def gammaFactorialLogEnvelopeSixthJetClosureRatio
    (n : ℕ) (x : ℂ) : ℂ :=
  (GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
      GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x) *
    (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
      GaloisForLFunctions.gammaFactorialFirstJetDefect n x) ^ (6 : ℕ)

theorem tendsto_gammaFactorialLogSecondHarmonicClosureRatio
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => gammaFactorialLogSecondHarmonicClosureRatio n x)
      atTop (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)) / 9)) := by
  have hlog :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ))
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (4 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq hx
  have hsecond :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n)
        atTop (𝓝 (6 / x ^ (2 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx
  have hsecond_ne : (6 / x ^ (2 : ℕ) : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hnormalized :=
    hlog.div (hsecond.pow 2) (pow_ne_zero 2 hsecond_ne)
  have hvalue :
      (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (4 : ℕ)) / (6 / x ^ (2 : ℕ)) ^ (2 : ℕ) =
        -((Real.pi : ℂ) ^ (2 : ℕ)) / 9 := by
    field_simp [hx]
    ring
  rw [hvalue] at hnormalized
  have heq : ∀ᶠ n : ℕ in atTop,
      (GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ)) /
        (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n) ^ (2 : ℕ) =
        gammaFactorialLogSecondHarmonicClosureRatio n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    by_cases hsecondZero :
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x = 0
    · simp [gammaFactorialLogSecondHarmonicClosureRatio, hsecondZero]
    · have hfactorial :
          GaloisForLFunctions.reciprocalGammaFactorialScale n ≠ 0 := by
        rw [GaloisForLFunctions.reciprocalGammaFactorialScale]
        exact div_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero n)
      have hharmonic : (harmonic n : ℂ) ≠ 0 := by
        exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
      rw [gammaFactorialLogSecondHarmonicClosureRatio,
        GaloisForLFunctions.gammaHarmonicMicroscopeScale]
      field_simp [hfactorial, hharmonic, hsecondZero]
  exact hnormalized.congr' heq

theorem tendsto_gammaFactorialLogEnvelopeSixthJetClosureRatio
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => gammaFactorialLogEnvelopeSixthJetClosureRatio n x)
      atTop (𝓝 729) := by
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
  have hlog :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ))
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (4 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq hx
  have henvelope :
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ))
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (10 : ℕ))) :=
    GaloisForLFunctions.tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq hx
  have hfirst_ne : (-2 / x : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) hx
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have henvelope_ne : (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (10 : ℕ)) ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))
      (pow_ne_zero 10 hx)
  have hsecondFirstNormalized := hsecond.div hfirst hfirst_ne
  have hsecondFirstValue : (6 / x ^ (2 : ℕ) : ℂ) / (-2 / x) = -3 / x := by
    field_simp [hx]
    ring
  rw [hsecondFirstValue] at hsecondFirstNormalized
  have hsecondFirstEq : ∀ᶠ n : ℕ in atTop,
      (GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n) /
        (GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          GaloisForLFunctions.gammaHarmonicMicroscopeScale n) =
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    by_cases hden :
        GaloisForLFunctions.gammaFactorialFirstJetDefect n x = 0
    · simp [hden]
    · field_simp
        [GaloisForLFunctions.gammaHarmonicMicroscopeScale_ne_zero hn, hden]
  have hsecondFirst := hsecondFirstNormalized.congr' hsecondFirstEq
  have hlogEnvelopeNormalized := hlog.div henvelope henvelope_ne
  have hlogEnvelopeValue :
      (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (4 : ℕ)) /
          (-4 * (Real.pi : ℂ) ^ (2 : ℕ) / x ^ (10 : ℕ)) = x ^ (6 : ℕ) := by
    field_simp [hx, hpi]
  rw [hlogEnvelopeValue] at hlogEnvelopeNormalized
  have hlogEnvelopeEq : ∀ᶠ n : ℕ in atTop,
      (GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ)) /
        (GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
          GaloisForLFunctions.reciprocalGammaFactorialScale n ^ (2 : ℕ)) =
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x := by
    filter_upwards [] with n
    by_cases hden :
        GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x = 0
    · simp [hden]
    · have hscale :
          GaloisForLFunctions.reciprocalGammaFactorialScale n ≠ 0 := by
        rw [GaloisForLFunctions.reciprocalGammaFactorialScale]
        exact div_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero n)
      field_simp [hscale, hden]
  have hlogEnvelope := hlogEnvelopeNormalized.congr' hlogEnvelopeEq
  have hclosure := hlogEnvelope.mul (hsecondFirst.pow 6)
  have hvalue : (x ^ (6 : ℕ) : ℂ) * (-3 / x) ^ (6 : ℕ) = 729 := by
    field_simp [hx]
    ring
  rw [hvalue] at hclosure
  simpa only [gammaFactorialLogEnvelopeSixthJetClosureRatio] using hclosure

/-- The three balance equations for factorial-scale, harmonic-scale, and observation-point
exponents of a Laurent monomial in `(F,S,P,T,L,E,h)`. -/
def GammaFactorialToricBalanced
    (aF aS aP aT aL aE aH : ℤ) : Prop :=
  aF + aS + aP + 2 * aT + 2 * aL + 2 * aE = 0 ∧
  aF + aS + aP + 2 * aT + aH = 0 ∧
  aF + 2 * aS + 3 * aP + 4 * aT + 4 * aL + 10 * aE = 0

/-- Every balanced integer exponent vector has unique coordinates in the four primitive closure
directions. -/
theorem gammaFactorialToricBalanced_iff_basisCoordinates
    (aF aS aP aT aL aE aH : ℤ) :
    GammaFactorialToricBalanced aF aS aP aT aL aE aH ↔
      ∃ u v w q : ℤ,
        aF = u - 6 * q ∧
        aS = -2 * u - 2 * v - 2 * w + 6 * q ∧
        aP = u ∧
        aT = v ∧
        aL = w + q ∧
        aE = -q ∧
        aH = 2 * w := by
  constructor
  · rintro ⟨hfactorial, hharmonic, hpoint⟩
    refine ⟨aP, aT, aL + aE, -aE, ?_⟩
    omega
  · rintro ⟨u, v, w, q, hF, hS, hP, hT, hL, hE, hH⟩
    rw [GammaFactorialToricBalanced]
    omega

/-- **Complete toric Gamma jet-closure law.** Four universal constants supply an integer basis
of all point- and scale-free Laurent monomials supported on the proved six-defect hierarchy. -/
theorem gammaFactorial_completeToricJetClosureUniversality :
    (∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n => gammaFactorialProjectiveSecondFirstClosureRatio n x)
        atTop (𝓝 (-1 / 9)) ∧
      Tendsto (fun n => gammaFactorialProjectiveThirdSecondClosureRatio n x)
        atTop (𝓝 (-1 / 6)) ∧
      Tendsto (fun n => gammaFactorialLogSecondHarmonicClosureRatio n x)
        atTop (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)) / 9)) ∧
      Tendsto (fun n => gammaFactorialLogEnvelopeSixthJetClosureRatio n x)
        atTop (𝓝 729)) ∧
    ∀ aF aS aP aT aL aE aH : ℤ,
      GammaFactorialToricBalanced aF aS aP aT aL aE aH ↔
        ∃ u v w q : ℤ,
          aF = u - 6 * q ∧
          aS = -2 * u - 2 * v - 2 * w + 6 * q ∧
          aP = u ∧
          aT = v ∧
          aL = w + q ∧
          aE = -q ∧
          aH = 2 * w := by
  refine ⟨?_, gammaFactorialToricBalanced_iff_basisCoordinates⟩
  intro x hx
  rcases gammaFactorial_projectiveJetClosureConstantsUniversality x hx with
    ⟨hprojectiveSecond, hprojectiveThird, _, _⟩
  exact ⟨hprojectiveSecond, hprojectiveThird,
    tendsto_gammaFactorialLogSecondHarmonicClosureRatio hx,
    tendsto_gammaFactorialLogEnvelopeSixthJetClosureRatio hx⟩

end

end GaloisForLFunctions.RHTower
