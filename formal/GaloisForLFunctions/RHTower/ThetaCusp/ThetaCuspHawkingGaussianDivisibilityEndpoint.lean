import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedOrientationBoundary

/-!
# Theta-cusp Hawking Gaussian-channel divisibility endpoint

The moving-mirror Born pair kernel has a canonical source form factor after its universal
kinematic factor `2 i p q` is removed.  That form factor is the completed theta/Xi amplitude.
Following the quantum-amplifier description of Hawking radiation, this file assigns the minimal
phase-insensitive amplifier gain `1 + |beta|^(2 : ℕ)` to the continued source form factor.

Every individual aperture is a valid quantum-limited amplifier, unconditionally.  The nontrivial
condition is finite CP-divisibility as the centered-strip aperture increases: quantum-limited
amplifiers compose by multiplying gains, so an intermediate channel exists exactly when gain is
nondecreasing.  The aperture derivative of gain is the Hedenmalm split Hankel--Krein current.
Consequently, divisibility throughout the critical aperture is equivalent to RH.

This is an exact reduction, not a proof of the missing sign.  Its open core is to derive strip
translation as actual causal post-processing of the theta-cusp mirror channel; pointwise complete
positivity alone cannot do this because it holds at every aperture.
-/

open Complex Real Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Source-normalized Hawking pair amplitude -/

/-- Source form factor left after removing the universal moving-mirror pair prefactor. -/
def thetaCuspHawkingDeembeddedPairAmplitude (z : ℂ) : ℂ :=
  XiC z

/-- Exact de-embedding of the full two-frequency Hawking Born kernel. -/
theorem thetaCuspHawkingBornPairKernel_eq_kinematic_mul_deembedded
    (outgoing incoming : ℂ) :
    thetaCuspHawkingBornPairKernel outgoing incoming =
      2 * I * outgoing * incoming *
        thetaCuspHawkingDeembeddedPairAmplitude (outgoing + incoming) := by
  rfl

/-- Continued source pair amplitude along the centered upper critical aperture. -/
def thetaCuspHawkingStripPairAmplitude (a b : ℝ) : ℂ :=
  thetaCuspHawkingDeembeddedPairAmplitude ((b : ℂ) - (a : ℂ) * I)

/-- The source pair amplitude is exactly the pointed theta/Xi Hankel-orbit value. -/
theorem thetaCuspHawkingStripPairAmplitude_eq_orbit (a b : ℝ) :
    thetaCuspHawkingStripPairAmplitude a b =
      thetaXiHankelOrbitValuePlus a b := by
  rfl

/-! ## Quantum-limited amplifier algebra -/

/-- Power gain of the minimal phase-insensitive amplifier carried by the source pair mode. -/
def thetaCuspHawkingAmplifierGain (a b : ℝ) : ℝ :=
  1 + normSq (thetaCuspHawkingStripPairAmplitude a b)

/-- Admissibility condition for a quantum-limited phase-insensitive amplifier gain. -/
def IsQuantumLimitedAmplifierGain (gain : ℝ) : Prop :=
  1 ≤ gain

/-- Added vacuum particle number of a quantum-limited amplifier. -/
def quantumLimitedAmplifierAddedNoise (gain : ℝ) : ℝ :=
  gain - 1

/-- Every aperture gives a valid quantum-limited amplifier.  Thus pointwise complete positivity
does not distinguish RH. -/
theorem thetaCuspHawkingAmplifierGain_isQuantumLimited (a b : ℝ) :
    IsQuantumLimitedAmplifierGain (thetaCuspHawkingAmplifierGain a b) := by
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- Positive amplitude gain in the canonical two-mode Stinespring dilation. -/
def thetaCuspHawkingAmplifierAmplitudeGain (a b : ℝ) : ℝ :=
  Real.sqrt (thetaCuspHawkingAmplifierGain a b)

/-- The amplitude gain squares to the Hawking power gain. -/
theorem thetaCuspHawkingAmplifierAmplitudeGain_sq (a b : ℝ) :
    thetaCuspHawkingAmplifierAmplitudeGain a b ^ (2 : ℕ) =
      thetaCuspHawkingAmplifierGain a b := by
  rw [thetaCuspHawkingAmplifierAmplitudeGain, Real.sq_sqrt]
  have hgain := thetaCuspHawkingAmplifierGain_isQuantumLimited a b
  rw [IsQuantumLimitedAmplifierGain] at hgain
  exact le_trans zero_le_one hgain

/-- Explicit two-mode CCR/Stinespring completion of every source-normalized Hawking mode. -/
theorem thetaCuspHawkingStripPairAmplitude_isTwoModeBosonicCCR (a b : ℝ) :
    IsTwoModeBosonicCCR
      (thetaCuspHawkingAmplifierAmplitudeGain a b)
      (thetaCuspHawkingStripPairAmplitude a b) := by
  rw [IsTwoModeBosonicCCR, thetaCuspHawkingAmplifierAmplitudeGain_sq,
    thetaCuspHawkingAmplifierGain, Complex.normSq_eq_norm_sq]
  ring

/-- Quantum-limited amplifier gains are closed under channel composition. -/
theorem isQuantumLimitedAmplifierGain_mul
    {first second : ℝ}
    (hfirst : IsQuantumLimitedAmplifierGain first)
    (hsecond : IsQuantumLimitedAmplifierGain second) :
    IsQuantumLimitedAmplifierGain (second * first) := by
  rw [IsQuantumLimitedAmplifierGain] at hfirst hsecond ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hsecond)]

/-- Exact vacuum-noise law under serial composition of quantum-limited amplifiers. -/
theorem quantumLimitedAmplifierAddedNoise_mul (first second : ℝ) :
    quantumLimitedAmplifierAddedNoise (second * first) =
      second * quantumLimitedAmplifierAddedNoise first +
        quantumLimitedAmplifierAddedNoise second := by
  rw [quantumLimitedAmplifierAddedNoise, quantumLimitedAmplifierAddedNoise,
    quantumLimitedAmplifierAddedNoise]
  ring

/-- `later` is obtainable from `earlier` by a quantum-limited intermediate amplifier. -/
def QuantumLimitedAmplifierDivides (earlier later : ℝ) : Prop :=
  ∃ intermediate : ℝ,
    IsQuantumLimitedAmplifierGain intermediate ∧
      later = intermediate * earlier

/-- Identity channel is a valid intermediate amplifier. -/
theorem quantumLimitedAmplifierDivides_refl (gain : ℝ) :
    QuantumLimitedAmplifierDivides gain gain := by
  refine ⟨1, le_rfl, ?_⟩
  ring

/-- Serial quantum-limited divisibility is transitive. -/
theorem quantumLimitedAmplifierDivides_trans
    {first second third : ℝ}
    (h₁₂ : QuantumLimitedAmplifierDivides first second)
    (h₂₃ : QuantumLimitedAmplifierDivides second third) :
    QuantumLimitedAmplifierDivides first third := by
  rcases h₁₂ with ⟨middle₁, hmiddle₁, hsecond⟩
  rcases h₂₃ with ⟨middle₂, hmiddle₂, hthird⟩
  refine ⟨middle₂ * middle₁,
    isQuantumLimitedAmplifierGain_mul hmiddle₁ hmiddle₂, ?_⟩
  rw [hthird, hsecond]
  ring

/-- For a physical initial gain, existence of a quantum-limited intermediate channel is exactly
gain monotonicity. -/
theorem quantumLimitedAmplifierDivides_iff_le
    {earlier later : ℝ}
    (hearlier : IsQuantumLimitedAmplifierGain earlier) :
    QuantumLimitedAmplifierDivides earlier later ↔ earlier ≤ later := by
  constructor
  · rintro ⟨intermediate, hintermediate, rfl⟩
    calc
      earlier = 1 * earlier := by ring
      _ ≤ intermediate * earlier :=
        mul_le_mul_of_nonneg_right hintermediate
          (le_trans zero_le_one hearlier)
  · intro hle
    have hearlier_pos : 0 < earlier := lt_of_lt_of_le zero_lt_one hearlier
    refine ⟨later / earlier, ?_, ?_⟩
    · rw [IsQuantumLimitedAmplifierGain,
        (le_div_iff₀ hearlier_pos)]
      simpa using hle
    · exact (div_mul_cancel₀ later hearlier_pos.ne').symm

/-! ## Aperture derivative and finite CP-divisibility -/

/-- The amplifier gain derivative is exactly the theta/Xi split Hankel--Krein current. -/
theorem hasDerivAt_thetaCuspHawkingAmplifierGain (a b : ℝ) :
    HasDerivAt
      (fun t : ℝ => thetaCuspHawkingAmplifierGain t b)
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b)) a := by
  simpa [thetaCuspHawkingAmplifierGain,
    thetaCuspHawkingStripPairAmplitude,
    thetaCuspHawkingDeembeddedPairAmplitude,
    thetaXiHankelOrbitValuePlus] using
      (hasDerivAt_thetaXiHankelOrbit_normSq a b).const_add 1

/-- Finite CP-divisibility of every source-normalized Hawking amplifier mode through the centered
critical aperture. -/
def ThetaCuspHawkingAmplifierCPDivisible : Prop :=
  ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ ≤ a₂ → a₂ < 1 / 2 → ∀ b : ℝ,
    QuantumLimitedAmplifierDivides
      (thetaCuspHawkingAmplifierGain a₁ b)
      (thetaCuspHawkingAmplifierGain a₂ b)

/-- A nonnegative theta/Xi Krein current produces finite quantum-limited intermediate channels
through every closed sub-aperture. -/
theorem thetaCuspHawkingAmplifierCPDivisible_of_thetaXiHankelOrbitNonnegative
    (horbit : ThetaXiHankelOrbitNonnegative) :
    ThetaCuspHawkingAmplifierCPDivisible := by
  intro a₁ a₂ ha₁ ha₁₂ ha₂ b
  apply (quantumLimitedAmplifierDivides_iff_le
    (thetaCuspHawkingAmplifierGain_isQuantumLimited a₁ b)).2
  by_cases heq : a₁ = a₂
  · simp [heq]
  have hlt : a₁ < a₂ := lt_of_le_of_ne ha₁₂ heq
  let gain : ℝ → ℝ := fun t => thetaCuspHawkingAmplifierGain t b
  have hgain : ∀ t : ℝ, HasDerivAt gain
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus t b)
        (thetaXiHankelOrbitTangentPlus t b)
        (thetaXiHankelOrbitValueMinus t b)
        (thetaXiHankelOrbitTangentMinus t b)) t := by
    intro t
    simpa [gain] using hasDerivAt_thetaCuspHawkingAmplifierGain t b
  have hmono : MonotoneOn gain (Icc a₁ a₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a₁ a₂)
    · intro t ht
      exact (hgain t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgain t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgain t).deriv]
      exact horbit t (lt_trans ha₁ ht.1) (lt_trans ht.2 ha₂) b
  exact hmono (left_mem_Icc.mpr ha₁₂) (right_mem_Icc.mpr ha₁₂) ha₁₂

/-- Conversely, finite quantum-limited divisibility forces the infinitesimal theta/Xi Krein
current to be nonnegative at every critical-aperture point. -/
theorem thetaXiHankelOrbitNonnegative_of_thetaCuspHawkingAmplifierCPDivisible
    (hcp : ThetaCuspHawkingAmplifierCPDivisible) :
    ThetaXiHankelOrbitNonnegative := by
  intro a ha haHalf b
  let gain : ℝ → ℝ := fun t => thetaCuspHawkingAmplifierGain t b
  have hmono : MonotoneOn gain (Ioo 0 (1 / 2)) := by
    intro a₁ ha₁ a₂ ha₂ ha₁₂
    exact (quantumLimitedAmplifierDivides_iff_le
      (thetaCuspHawkingAmplifierGain_isQuantumLimited a₁ b)).mp
        (hcp a₁ a₂ ha₁.1 ha₁₂ ha₂.2 b)
  have hderiv : 0 ≤ deriv gain a := by
    rw [← derivWithin_of_isOpen isOpen_Ioo ⟨ha, haHalf⟩]
    exact hmono.derivWithin_nonneg
  have hgain := hasDerivAt_thetaCuspHawkingAmplifierGain a b
  rw [show deriv gain a = _ by simpa [gain] using hgain.deriv] at hderiv
  exact hderiv

/-- Exact identification of finite Hawking-amplifier divisibility with theta/Xi chamber
avoidance. -/
theorem thetaCuspHawkingAmplifierCPDivisible_iff_thetaXiHankelOrbitNonnegative :
    ThetaCuspHawkingAmplifierCPDivisible ↔
      ThetaXiHankelOrbitNonnegative := by
  constructor
  · exact thetaXiHankelOrbitNonnegative_of_thetaCuspHawkingAmplifierCPDivisible
  · exact thetaCuspHawkingAmplifierCPDivisible_of_thetaXiHankelOrbitNonnegative

/-- **Gaussian-divisibility endpoint.** RH is equivalent to finite CP-divisibility of every
source-normalized theta-cusp Hawking amplifier mode throughout the critical aperture. -/
theorem thetaCuspHawkingAmplifierCPDivisible_iff_riemannHypothesis :
    ThetaCuspHawkingAmplifierCPDivisible ↔ RiemannHypothesis :=
  thetaCuspHawkingAmplifierCPDivisible_iff_thetaXiHankelOrbitNonnegative.trans
    thetaXiHankelOrbitNonnegative_iff_riemannHypothesis

end RHTower
