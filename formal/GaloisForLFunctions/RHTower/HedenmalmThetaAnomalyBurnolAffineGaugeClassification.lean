import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolCanonicalSynthesis

/-!
# Affine-gauge classification of every two-prime Burnol synthesis

Every right inverse of the completed prime-two/prime-three Burnol frame is the canonical
Moore--Penrose row plus a unique scalar multiple of the transverse frame vector.  Its coefficient
energy is exactly canonical energy plus `|gauge|²` times frame energy.

This identifies a universal Route-P obstruction.  For every reflection-real source choice, all
positive synthesis energies are reflection-even, not only the canonical minimum.  The sole odd
coordinate surviving the classification is the unsquared imaginary part of the transverse gauge;
positive scalarization erases it.
-/

open Complex Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Unique transverse coordinate of a two-prime synthesis row. -/
def burnolSynthesisGauge (z b₂ b₃ : ℂ) : ℂ :=
  (b₂ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
      b₃ * (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z)) /
    (burnolTwoPrimeFrameEnergy z : ℂ)

/-- Affine family of all two-prime synthesis rows. -/
def burnolAffineSynthesisFrame (c z : ℂ) : ℂ × ℂ :=
  (burnolCanonicalSynthesisCoefficient 2 z +
      c * burnolCompletedCenteredMultiplier 3 z,
    burnolCanonicalSynthesisCoefficient 3 z -
      c * burnolCompletedCenteredMultiplier 2 z)

theorem burnolAffineSynthesis_identity (c z : ℂ) :
    (burnolAffineSynthesisFrame c z).1 *
        burnolCompletedCenteredMultiplier 2 z +
      (burnolAffineSynthesisFrame c z).2 *
        burnolCompletedCenteredMultiplier 3 z = 1 := by
  rw [burnolAffineSynthesisFrame]
  dsimp only [Prod.fst, Prod.snd]
  rw [← burnolCanonicalSynthesis_identity z]
  ring

theorem burnolAffineSynthesis_cross (c z : ℂ) :
    (burnolAffineSynthesisFrame c z).1 *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) -
      (burnolAffineSynthesisFrame c z).2 *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z) =
      c * (burnolTwoPrimeFrameEnergy z : ℂ) := by
  rw [burnolAffineSynthesisFrame]
  dsimp only [Prod.fst, Prod.snd]
  have hc := burnolCanonicalSynthesis_cross_zero z
  rw [burnolTwoPrimeFrameEnergy]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  linear_combination hc

theorem burnolAffineSynthesis_gauge (c z : ℂ) :
    burnolSynthesisGauge z
      (burnolAffineSynthesisFrame c z).1
      (burnolAffineSynthesisFrame c z).2 = c := by
  rw [burnolSynthesisGauge, burnolAffineSynthesis_cross]
  have hE : (burnolTwoPrimeFrameEnergy z : ℂ) ≠ 0 := by
    exact_mod_cast (burnolTwoPrimeFrameEnergy_pos z).ne'
  simpa only [mul_comm] using mul_div_cancel_left₀ c hE

/-- **Complete affine classification.**  Every synthesis row has a unique scalar transverse
coordinate and equals the corresponding affine row. -/
theorem burnolSynthesis_affine_classification
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1) :
    (b₂, b₃) = burnolAffineSynthesisFrame (burnolSynthesisGauge z b₂ b₃) z := by
  let a₂ := burnolCompletedCenteredMultiplier 2 z
  let a₃ := burnolCompletedCenteredMultiplier 3 z
  let E : ℂ := (burnolTwoPrimeFrameEnergy z : ℂ)
  let d : ℂ := b₂ * (starRingEnd ℂ) a₃ - b₃ * (starRingEnd ℂ) a₂
  have hE : E ≠ 0 := by
    dsimp only [E]
    exact_mod_cast (burnolTwoPrimeFrameEnergy_pos z).ne'
  have hEform : E = (starRingEnd ℂ) a₂ * a₂ + (starRingEnd ℂ) a₃ * a₃ := by
    dsimp only [E]
    rw [burnolTwoPrimeFrameEnergy]
    dsimp only [a₂, a₃]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  have hb₂E : b₂ * E = (starRingEnd ℂ) a₂ + d * a₃ := by
    rw [hEform]
    dsimp only [d]
    linear_combination hbez * (starRingEnd ℂ) a₂
  have hb₃E : b₃ * E = (starRingEnd ℂ) a₃ - d * a₂ := by
    rw [hEform]
    dsimp only [d]
    linear_combination hbez * (starRingEnd ℂ) a₃
  apply Prod.ext
  · rw [burnolAffineSynthesisFrame]
    dsimp only [Prod.fst, burnolSynthesisGauge, burnolCanonicalSynthesisCoefficient]
    dsimp only [a₂, a₃, E, d] at hb₂E ⊢
    rw [div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hE).2
    linear_combination hb₂E
  · rw [burnolAffineSynthesisFrame]
    dsimp only [Prod.snd, burnolSynthesisGauge, burnolCanonicalSynthesisCoefficient]
    dsimp only [a₂, a₃, E, d] at hb₃E ⊢
    rw [div_mul_eq_mul_div, ← sub_div]
    apply (eq_div_iff hE).2
    linear_combination hb₃E

def burnolAffineSynthesisEnergy (c z : ℂ) : ℝ :=
  Complex.normSq (burnolAffineSynthesisFrame c z).1 +
    Complex.normSq (burnolAffineSynthesisFrame c z).2

/-- Energy of an affine synthesis is canonical energy plus exact transverse-gauge energy. -/
theorem burnolAffineSynthesisEnergy_exact (c z : ℂ) :
    burnolAffineSynthesisEnergy c z =
      1 / burnolTwoPrimeFrameEnergy z +
        Complex.normSq c * burnolTwoPrimeFrameEnergy z := by
  have hgap := burnol_synthesis_energy_gap_exact z
    (burnolAffineSynthesisFrame c z).1
    (burnolAffineSynthesisFrame c z).2
    (burnolAffineSynthesis_identity c z)
  rw [burnolAffineSynthesis_cross, Complex.normSq_mul,
    Complex.normSq_ofReal] at hgap
  unfold burnolAffineSynthesisEnergy
  have hE : burnolTwoPrimeFrameEnergy z ≠ 0 := (burnolTwoPrimeFrameEnergy_pos z).ne'
  field_simp [hE] at hgap ⊢
  nlinarith

/-- Complete energy classification for an arbitrary synthesis row. -/
theorem burnolSynthesisEnergy_classified
    (z b₂ b₃ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
      b₃ * burnolCompletedCenteredMultiplier 3 z = 1) :
    Complex.normSq b₂ + Complex.normSq b₃ =
      1 / burnolTwoPrimeFrameEnergy z +
        Complex.normSq (burnolSynthesisGauge z b₂ b₃) *
          burnolTwoPrimeFrameEnergy z := by
  have hclass := burnolSynthesis_affine_classification z b₂ b₃ hbez
  have henergy := congrArg
    (fun p : ℂ × ℂ => Complex.normSq p.1 + Complex.normSq p.2) hclass
  change Complex.normSq b₂ + Complex.normSq b₃ =
    burnolAffineSynthesisEnergy (burnolSynthesisGauge z b₂ b₃) z at henergy
  rw [henergy]
  exact burnolAffineSynthesisEnergy_exact _ _

theorem burnolAffineSynthesisFrame_conj (c z : ℂ) :
    burnolAffineSynthesisFrame ((starRingEnd ℂ) c) ((starRingEnd ℂ) z) =
      ((starRingEnd ℂ) (burnolAffineSynthesisFrame c z).1,
        (starRingEnd ℂ) (burnolAffineSynthesisFrame c z).2) := by
  simp [burnolAffineSynthesisFrame, burnolCanonicalSynthesisCoefficient_conj,
    burnolCompletedCenteredMultiplier_conj]

theorem burnolAffineSynthesisEnergy_conj (c z : ℂ) :
    burnolAffineSynthesisEnergy ((starRingEnd ℂ) c) ((starRingEnd ℂ) z) =
      burnolAffineSynthesisEnergy c z := by
  rw [burnolAffineSynthesisEnergy_exact, burnolAffineSynthesisEnergy_exact,
    burnolTwoPrimeFrameEnergy_conj, Complex.normSq_conj]

theorem burnol_reflection_real_synthesis_energy_even
    (b₂ b₃ : ℂ → ℂ)
    (hreal₂ : ∀ z : ℂ, b₂ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₂ z))
    (hreal₃ : ∀ z : ℂ, b₃ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₃ z))
    (z : ℂ) :
    Complex.normSq (b₂ ((starRingEnd ℂ) z)) +
        Complex.normSq (b₃ ((starRingEnd ℂ) z)) =
      Complex.normSq (b₂ z) + Complex.normSq (b₃ z) := by
  rw [hreal₂, hreal₃, Complex.normSq_conj, Complex.normSq_conj]

theorem burnolSynthesisGauge_conj
    (b₂ b₃ : ℂ → ℂ)
    (hreal₂ : ∀ z : ℂ, b₂ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₂ z))
    (hreal₃ : ∀ z : ℂ, b₃ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₃ z))
    (z : ℂ) :
    burnolSynthesisGauge ((starRingEnd ℂ) z)
        (b₂ ((starRingEnd ℂ) z)) (b₃ ((starRingEnd ℂ) z)) =
      (starRingEnd ℂ) (burnolSynthesisGauge z (b₂ z) (b₃ z)) := by
  simp [burnolSynthesisGauge, hreal₂, hreal₃,
    burnolCompletedCenteredMultiplier_conj, burnolTwoPrimeFrameEnergy_conj]

/-- Unsquared imaginary gauge is reflection odd. -/
theorem burnolSynthesisGauge_im_conj_neg
    (b₂ b₃ : ℂ → ℂ)
    (hreal₂ : ∀ z : ℂ, b₂ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₂ z))
    (hreal₃ : ∀ z : ℂ, b₃ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b₃ z))
    (z : ℂ) :
    (burnolSynthesisGauge ((starRingEnd ℂ) z)
        (b₂ ((starRingEnd ℂ) z)) (b₃ ((starRingEnd ℂ) z))).im =
      -(burnolSynthesisGauge z (b₂ z) (b₃ z)).im := by
  rw [burnolSynthesisGauge_conj b₂ b₃ hreal₂ hreal₃ z, Complex.conj_im]

def thetaXiBurnolAffineSynthesisFrame
    (c : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ × ℂ :=
  burnolAffineSynthesisFrame (c q) (xiSpectralPoint q)

def thetaXiBurnolAffineSynthesisEnergy
    (c : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℝ :=
  burnolAffineSynthesisEnergy (c q) (xiSpectralPoint q)

theorem thetaXiBurnolAffineSynthesis_reconstructs_one
    (c : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    (thetaXiBurnolAffineSynthesisFrame c q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 +
      (thetaXiBurnolAffineSynthesisFrame c q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 = 1 := by
  exact burnolAffineSynthesis_identity (c q) (xiSpectralPoint q)

theorem thetaXiBurnolAffineSynthesisEnergy_exact
    (c : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    thetaXiBurnolAffineSynthesisEnergy c q =
      1 / burnolTwoPrimeFrameEnergy (xiSpectralPoint q) +
        Complex.normSq (c q) * burnolTwoPrimeFrameEnergy (xiSpectralPoint q) := by
  exact burnolAffineSynthesisEnergy_exact (c q) (xiSpectralPoint q)

theorem thetaXiBurnolAffineSynthesisEnergy_lineConj
    (c : XiZeroCopy → ℂ)
    (hreal : ∀ q : XiZeroCopy,
      c (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (c q))
    (q : XiZeroCopy) :
    thetaXiBurnolAffineSynthesisEnergy c (xiZeroCopyLineConjEquiv q) =
      thetaXiBurnolAffineSynthesisEnergy c q := by
  rw [thetaXiBurnolAffineSynthesisEnergy, thetaXiBurnolAffineSynthesisEnergy,
    hreal, xiSpectralPoint_lineConj, burnolAffineSynthesisEnergy_conj]

theorem thetaXiBurnolGauge_im_lineConj_neg
    (c : XiZeroCopy → ℂ)
    (hreal : ∀ q : XiZeroCopy,
      c (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (c q))
    (q : XiZeroCopy) :
    (c (xiZeroCopyLineConjEquiv q)).im = -(c q).im := by
  rw [hreal, Complex.conj_im]

/-- **All-synthesis no-go and positive survivor.**  Every reflection-real finite-prime synthesis
reconstructs the Xi quotient, but its positive energy is reflection-even.  Only unsquared gauge
imaginary part remains odd. -/
theorem thetaXiBurnolAffineSynthesis_energy_even_but_gauge_im_odd
    (c : XiZeroCopy → ℂ)
    (hreal : ∀ q : XiZeroCopy,
      c (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (c q))
    (q : XiZeroCopy) :
    ((thetaXiBurnolAffineSynthesisFrame c q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 +
      (thetaXiBurnolAffineSynthesisFrame c q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 = 1) ∧
      thetaXiBurnolAffineSynthesisEnergy c (xiZeroCopyLineConjEquiv q) =
        thetaXiBurnolAffineSynthesisEnergy c q ∧
      (c (xiZeroCopyLineConjEquiv q)).im = -(c q).im :=
  ⟨thetaXiBurnolAffineSynthesis_reconstructs_one c q,
    thetaXiBurnolAffineSynthesisEnergy_lineConj c hreal q,
    thetaXiBurnolGauge_im_lineConj_neg c hreal q⟩

end

end RHTower.HedenmalmThetaSource
