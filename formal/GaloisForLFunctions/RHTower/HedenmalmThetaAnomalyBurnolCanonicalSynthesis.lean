import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolCoronaEscape

/-!
# Canonical singular synthesis for the two-prime Burnol anomaly frame

The completed prime-two/prime-three Burnol cells form a nowhere-zero frame on the whole complex
spectral plane.  Their pointwise Moore--Penrose row is therefore source-canonical.  It reconstructs
one exactly and uniquely minimizes coefficient energy.

A two-coordinate Lagrange identity gives the complete excess law: energy above the minimum is the
squared determinant transverse to the frame, divided by frame energy.  The canonical inverse has
the order-one boundary escape forced by P-G112.  On Xi divisor copies it reconstructs the singular
quotient exactly, but both coefficients and minimum energy are reflection-equivariant/even.  Thus
the singular connector exists; Route P orientation must enter through a source-order coupling
beyond its least-energy finite-prime inverse.
-/

open Complex Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmIntervalAnomaly

/-- Squared norm of the completed prime-two/prime-three Burnol frame. -/
def burnolTwoPrimeFrameEnergy (z : ℂ) : ℝ :=
  Complex.normSq (burnolCompletedCenteredMultiplier 2 z) +
    Complex.normSq (burnolCompletedCenteredMultiplier 3 z)

/-- The completed two-prime frame has no common zero anywhere, including the removable origin. -/
theorem burnol_completed_two_prime_no_common_zero (z : ℂ) :
    burnolCompletedCenteredMultiplier 2 z ≠ 0 ∨
      burnolCompletedCenteredMultiplier 3 z ≠ 0 := by
  by_cases h2 : burnolCompletedCenteredMultiplier 2 z = 0
  · right
    intro h3
    rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplierE] at h2 h3
    rcases eq_or_ne z 0 with rfl | hz
    · exact centeredMultiplierE_at_zero_ne_zero (n := 2) (by norm_num) h2
    · rw [centeredMultiplierE_eq 2 hz] at h2
      rw [centeredMultiplierE_eq 3 hz] at h3
      exact hz (no_common_zero_centered_two_three h2 h3)
  · exact Or.inl h2

theorem burnolTwoPrimeFrameEnergy_pos (z : ℂ) :
    0 < burnolTwoPrimeFrameEnergy z := by
  rcases burnol_completed_two_prime_no_common_zero z with h2 | h3
  · unfold burnolTwoPrimeFrameEnergy
    nlinarith [Complex.normSq_pos.mpr h2,
      Complex.normSq_nonneg (burnolCompletedCenteredMultiplier 3 z)]
  · unfold burnolTwoPrimeFrameEnergy
    nlinarith [Complex.normSq_nonneg (burnolCompletedCenteredMultiplier 2 z),
      Complex.normSq_pos.mpr h3]

/-- Pointwise Moore--Penrose coefficient of the completed two-prime Burnol frame. -/
def burnolCanonicalSynthesisCoefficient (n : ℕ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (burnolCompletedCenteredMultiplier n z) /
    (burnolTwoPrimeFrameEnergy z : ℂ)

/-- **Canonical singular synthesis.**  The Moore--Penrose row reconstructs one everywhere. -/
theorem burnolCanonicalSynthesis_identity (z : ℂ) :
    burnolCanonicalSynthesisCoefficient 2 z *
        burnolCompletedCenteredMultiplier 2 z +
      burnolCanonicalSynthesisCoefficient 3 z *
        burnolCompletedCenteredMultiplier 3 z = 1 := by
  have hE : (burnolTwoPrimeFrameEnergy z : ℂ) ≠ 0 := by
    exact_mod_cast (burnolTwoPrimeFrameEnergy_pos z).ne'
  rw [burnolCanonicalSynthesisCoefficient, burnolCanonicalSynthesisCoefficient]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
  rw [← add_div, show
    ((Complex.normSq (burnolCompletedCenteredMultiplier 2 z) : ℂ) +
      (Complex.normSq (burnolCompletedCenteredMultiplier 3 z) : ℂ)) =
        (burnolTwoPrimeFrameEnergy z : ℂ) by
      simp [burnolTwoPrimeFrameEnergy]]
  exact div_self hE

/-- Two-coordinate complex Lagrange identity in the bilinear synthesis convention. -/
theorem complex_two_coordinate_lagrange
    (b₂ b₃ a₂ a₃ : ℂ) :
    (Complex.normSq b₂ + Complex.normSq b₃) *
        (Complex.normSq a₂ + Complex.normSq a₃) =
      Complex.normSq (b₂ * a₂ + b₃ * a₃) +
        Complex.normSq (b₂ * (starRingEnd ℂ) a₃ -
          b₃ * (starRingEnd ℂ) a₂) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Every synthesis row has at least reciprocal-frame energy. -/
theorem burnol_synthesis_energy_minimal
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1) :
    1 / burnolTwoPrimeFrameEnergy z ≤
      Complex.normSq b₂ + Complex.normSq b₃ := by
  have hid := complex_two_coordinate_lagrange b₂ b₃
    (burnolCompletedCenteredMultiplier 2 z)
    (burnolCompletedCenteredMultiplier 3 z)
  rw [hbez, Complex.normSq_one] at hid
  have hprod : 1 ≤
      (Complex.normSq b₂ + Complex.normSq b₃) * burnolTwoPrimeFrameEnergy z := by
    rw [burnolTwoPrimeFrameEnergy]
    nlinarith [Complex.normSq_nonneg
      (b₂ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
        b₃ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z))]
  exact (div_le_iff₀ (burnolTwoPrimeFrameEnergy_pos z)).mpr (by simpa using hprod)

/-- **Exact synthesis excess.**  Energy above the Moore--Penrose minimum is precisely the squared
transverse determinant divided by frame energy. -/
theorem burnol_synthesis_energy_gap_exact
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1) :
    (Complex.normSq b₂ + Complex.normSq b₃) -
        1 / burnolTwoPrimeFrameEnergy z =
      Complex.normSq
          (b₂ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
            b₃ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z)) /
        burnolTwoPrimeFrameEnergy z := by
  have hid := complex_two_coordinate_lagrange b₂ b₃
    (burnolCompletedCenteredMultiplier 2 z)
    (burnolCompletedCenteredMultiplier 3 z)
  rw [hbez, Complex.normSq_one, ← burnolTwoPrimeFrameEnergy] at hid
  have hE : burnolTwoPrimeFrameEnergy z ≠ 0 := (burnolTwoPrimeFrameEnergy_pos z).ne'
  field_simp [hE]
  nlinarith

theorem burnolCanonicalSynthesis_cross_zero (z : ℂ) :
    burnolCanonicalSynthesisCoefficient 2 z *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
      burnolCanonicalSynthesisCoefficient 3 z *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z) = 0 := by
  rw [burnolCanonicalSynthesisCoefficient, burnolCanonicalSynthesisCoefficient]
  ring

/-- Minimum synthesis energy is equivalent to vanishing transverse determinant. -/
theorem burnol_synthesis_energy_eq_min_iff_cross_zero
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1) :
    Complex.normSq b₂ + Complex.normSq b₃ =
        1 / burnolTwoPrimeFrameEnergy z ↔
      b₂ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
        b₃ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z) = 0 := by
  let cross : ℂ :=
    b₂ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
      b₃ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z)
  have hgap := burnol_synthesis_energy_gap_exact z b₂ b₃ hbez
  have hE : burnolTwoPrimeFrameEnergy z ≠ 0 := (burnolTwoPrimeFrameEnergy_pos z).ne'
  constructor
  · intro hmin
    have hq : Complex.normSq cross / burnolTwoPrimeFrameEnergy z = 0 := by
      dsimp only [cross]
      rw [← hgap, hmin, sub_self]
    have hn : Complex.normSq cross = 0 := (div_eq_zero_iff).mp hq |>.resolve_right hE
    exact Complex.normSq_eq_zero.mp hn
  · intro hcross
    have hn : Complex.normSq cross = 0 := Complex.normSq_eq_zero.mpr hcross
    have :
        (Complex.normSq b₂ + Complex.normSq b₃) -
            1 / burnolTwoPrimeFrameEnergy z = 0 := by
      rw [hgap]
      simp only [cross, hn, zero_div]
    linarith

theorem burnolCanonicalSynthesis_energy_exact (z : ℂ) :
    Complex.normSq (burnolCanonicalSynthesisCoefficient 2 z) +
        Complex.normSq (burnolCanonicalSynthesisCoefficient 3 z) =
      1 / burnolTwoPrimeFrameEnergy z := by
  have hid := complex_two_coordinate_lagrange
    (burnolCanonicalSynthesisCoefficient 2 z)
    (burnolCanonicalSynthesisCoefficient 3 z)
    (burnolCompletedCenteredMultiplier 2 z)
    (burnolCompletedCenteredMultiplier 3 z)
  rw [burnolCanonicalSynthesis_identity, Complex.normSq_one,
    burnolCanonicalSynthesis_cross_zero, Complex.normSq_zero, add_zero,
    ← burnolTwoPrimeFrameEnergy] at hid
  exact (eq_div_iff (burnolTwoPrimeFrameEnergy_pos z).ne').mpr hid

/-- The canonical synthesis row is the unique minimum-energy right inverse. -/
theorem burnolCanonicalSynthesis_unique_minimizer
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1)
    (hmin : Complex.normSq b₂ + Complex.normSq b₃ =
      1 / burnolTwoPrimeFrameEnergy z) :
    (b₂, b₃) =
      (burnolCanonicalSynthesisCoefficient 2 z,
        burnolCanonicalSynthesisCoefficient 3 z) := by
  let a₂ := burnolCompletedCenteredMultiplier 2 z
  let a₃ := burnolCompletedCenteredMultiplier 3 z
  have hcross : b₂ * (starRingEnd ℂ) a₃ - b₃ * (starRingEnd ℂ) a₂ = 0 := by
    dsimp only [a₂, a₃]
    exact (burnol_synthesis_energy_eq_min_iff_cross_zero z b₂ b₃ hbez).mp hmin
  have hE : (burnolTwoPrimeFrameEnergy z : ℂ) ≠ 0 := by
    exact_mod_cast (burnolTwoPrimeFrameEnergy_pos z).ne'
  have hEform : (burnolTwoPrimeFrameEnergy z : ℂ) =
      (starRingEnd ℂ) a₂ * a₂ + (starRingEnd ℂ) a₃ * a₃ := by
    rw [burnolTwoPrimeFrameEnergy]
    dsimp only [a₂, a₃]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  have hb₂E : b₂ * (burnolTwoPrimeFrameEnergy z : ℂ) = (starRingEnd ℂ) a₂ := by
    rw [hEform]
    linear_combination hbez * (starRingEnd ℂ) a₂ + hcross * a₃
  have hb₃E : b₃ * (burnolTwoPrimeFrameEnergy z : ℂ) = (starRingEnd ℂ) a₃ := by
    rw [hEform]
    linear_combination hbez * (starRingEnd ℂ) a₃ - hcross * a₂
  apply Prod.ext
  · dsimp only [burnolCanonicalSynthesisCoefficient, Prod.fst]
    dsimp only [a₂] at hb₂E
    exact (eq_div_iff hE).mpr hb₂E
  · dsimp only [burnolCanonicalSynthesisCoefficient, Prod.snd]
    dsimp only [a₃] at hb₃E
    exact (eq_div_iff hE).mpr hb₃E

theorem burnolCompletedCenteredMultiplier_conj (n : ℕ) (z : ℂ) :
    burnolCompletedCenteredMultiplier n ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (burnolCompletedCenteredMultiplier n z) := by
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplierE,
    burnolCompletedCenteredMultiplier_eq_centeredMultiplierE,
    centeredMultiplierE_conj]

theorem burnolTwoPrimeFrameEnergy_conj (z : ℂ) :
    burnolTwoPrimeFrameEnergy ((starRingEnd ℂ) z) =
      burnolTwoPrimeFrameEnergy z := by
  simp [burnolTwoPrimeFrameEnergy, burnolCompletedCenteredMultiplier_conj,
    Complex.normSq_conj]

theorem burnolCanonicalSynthesisCoefficient_conj (n : ℕ) (z : ℂ) :
    burnolCanonicalSynthesisCoefficient n ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (burnolCanonicalSynthesisCoefficient n z) := by
  simp [burnolCanonicalSynthesisCoefficient, burnolCompletedCenteredMultiplier_conj,
    burnolTwoPrimeFrameEnergy_conj]

/-- The canonical right inverse realizes P-G112's forced order-one boundary escape. -/
theorem burnolCanonicalSynthesis_linear_escape {t : ℝ} (ht : 0 < t) :
    t / 4 ≤ max
      ‖burnolCanonicalSynthesisCoefficient 2 (t : ℂ)‖
      ‖burnolCanonicalSynthesisCoefficient 3 (t : ℂ)‖ := by
  exact burnol_two_prime_bezout_linear_escape
    (fun s : ℝ => burnolCanonicalSynthesisCoefficient 2 (s : ℂ))
    (fun s : ℝ => burnolCanonicalSynthesisCoefficient 3 (s : ℂ)) ht
    (burnolCanonicalSynthesis_identity (t : ℂ))

/-- Canonical synthesis row specialized to an actual Xi divisor copy. -/
def thetaXiBurnolCanonicalSynthesisFrame (q : XiZeroCopy) : ℂ × ℂ :=
  (burnolCanonicalSynthesisCoefficient 2 (xiSpectralPoint q),
    burnolCanonicalSynthesisCoefficient 3 (xiSpectralPoint q))

theorem thetaXiBurnolCanonicalSynthesis_reconstructs_one (q : XiZeroCopy) :
    (thetaXiBurnolCanonicalSynthesisFrame q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 +
      (thetaXiBurnolCanonicalSynthesisFrame q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 = 1 := by
  exact burnolCanonicalSynthesis_identity (xiSpectralPoint q)

theorem thetaXiBurnolCanonicalSynthesisFrame_lineConj (q : XiZeroCopy) :
    thetaXiBurnolCanonicalSynthesisFrame (xiZeroCopyLineConjEquiv q) =
      ((starRingEnd ℂ) (thetaXiBurnolCanonicalSynthesisFrame q).1,
        (starRingEnd ℂ) (thetaXiBurnolCanonicalSynthesisFrame q).2) := by
  rw [thetaXiBurnolCanonicalSynthesisFrame, thetaXiBurnolCanonicalSynthesisFrame,
    xiSpectralPoint_lineConj, burnolCanonicalSynthesisCoefficient_conj,
    burnolCanonicalSynthesisCoefficient_conj]

def thetaXiBurnolCanonicalSynthesisEnergy (q : XiZeroCopy) : ℝ :=
  Complex.normSq (thetaXiBurnolCanonicalSynthesisFrame q).1 +
    Complex.normSq (thetaXiBurnolCanonicalSynthesisFrame q).2

theorem thetaXiBurnolCanonicalSynthesisEnergy_exact (q : XiZeroCopy) :
    thetaXiBurnolCanonicalSynthesisEnergy q =
      1 / burnolTwoPrimeFrameEnergy (xiSpectralPoint q) := by
  exact burnolCanonicalSynthesis_energy_exact (xiSpectralPoint q)

theorem thetaXiBurnolCanonicalSynthesisEnergy_lineConj (q : XiZeroCopy) :
    thetaXiBurnolCanonicalSynthesisEnergy (xiZeroCopyLineConjEquiv q) =
      thetaXiBurnolCanonicalSynthesisEnergy q := by
  rw [thetaXiBurnolCanonicalSynthesisEnergy_exact,
    thetaXiBurnolCanonicalSynthesisEnergy_exact, xiSpectralPoint_lineConj,
    burnolTwoPrimeFrameEnergy_conj]

/-- **Connector/no-orientation capstone.**  Canonical singular synthesis reconstructs the divisor
quotient, while its least energy is exactly reflection-even. -/
theorem thetaXiBurnolCanonicalSynthesis_reconstructs_but_energy_is_reflection_even
    (q : XiZeroCopy) :
    (thetaXiBurnolCanonicalSynthesisFrame q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 +
      (thetaXiBurnolCanonicalSynthesisFrame q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 = 1 ∧
      thetaXiBurnolCanonicalSynthesisEnergy (xiZeroCopyLineConjEquiv q) =
        thetaXiBurnolCanonicalSynthesisEnergy q :=
  ⟨thetaXiBurnolCanonicalSynthesis_reconstructs_one q,
    thetaXiBurnolCanonicalSynthesisEnergy_lineConj q⟩

end

end RHTower.HedenmalmThetaSource
