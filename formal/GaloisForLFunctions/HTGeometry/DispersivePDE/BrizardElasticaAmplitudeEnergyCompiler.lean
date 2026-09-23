import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeCompiler
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Conserved energy of every compiled positive amplitude oscillator

The inverse-cubic amplitude equation carries a universal Hamiltonian.  This module proves its
conservation once at compiler level, so every Region I or Region II Jacobi realization inherits
the law without using its explicit elliptic first integral.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def amplitudeOscillatorEnergy
    (E : PositiveAmplitudeOscillator) (x : ℝ) : ℝ :=
  E.amplitude₁ x ^ (2 : ℕ) / 2 +
    E.q * E.amplitude x ^ (4 : ℕ) / 2 +
    E.q * E.gamma ^ (2 : ℕ) * E.amplitude x ^ (2 : ℕ) / 2 +
    E.q * E.nu ^ (2 : ℕ) / (2 * E.amplitude x ^ (2 : ℕ))

/-- The quartic plus inverse-square Hamiltonian has zero derivative along every compiled
amplitude oscillator. -/
theorem amplitudeOscillatorEnergy_hasDerivAt_zero
    (E : PositiveAmplitudeOscillator) (x : ℝ) :
    HasDerivAt (amplitudeOscillatorEnergy E) 0 x := by
  have hvSq := (E.amplitude₁_deriv x).pow 2
  have hASq := (E.amplitude_deriv x).pow 2
  have hAFourth := (E.amplitude_deriv x).pow 4
  have hkin := hvSq.div_const 2
  have hquartic := (hAFourth.const_mul E.q).div_const 2
  have hquadratic :=
    (hASq.const_mul (E.q * E.gamma ^ (2 : ℕ))).div_const 2
  have hden := hASq.const_mul 2
  have hbarrier := (hasDerivAt_const x (E.q * E.nu ^ (2 : ℕ))).div hden
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 (ne_of_gt (E.amplitude_pos x))))
  have hsum := ((hkin.add hquartic).add hquadratic).add hbarrier
  simp only [Pi.pow_apply] at hsum
  change HasDerivAt
    (fun y => E.amplitude₁ y ^ (2 : ℕ) / 2 +
      E.q * E.amplitude y ^ (4 : ℕ) / 2 +
      E.q * E.gamma ^ (2 : ℕ) * E.amplitude y ^ (2 : ℕ) / 2 +
      E.q * E.nu ^ (2 : ℕ) / (2 * E.amplitude y ^ (2 : ℕ))) 0 x
  apply hsum.congr_deriv
  rw [E.oscillator]
  field_simp [ne_of_gt (E.amplitude_pos x)]
  ring

/-- Global energy conservation follows from the pointwise zero derivative. -/
theorem amplitudeOscillatorEnergy_const
    (E : PositiveAmplitudeOscillator) (x y : ℝ) :
    amplitudeOscillatorEnergy E x = amplitudeOscillatorEnergy E y := by
  refine is_const_of_deriv_eq_zero
    (fun z => (amplitudeOscillatorEnergy_hasDerivAt_zero E z).differentiableAt)
    (fun z => ?_) x y
  rw [(amplitudeOscillatorEnergy_hasDerivAt_zero E z).deriv]

noncomputable def compiledAmplitudeEnergy
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  amplitudeOscillatorEnergy E (compiledArgument k₀ E s)

/-- Arclength rescaling preserves exact Hamiltonian conservation. -/
theorem compiledAmplitudeEnergy_hasDerivAt_zero
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledAmplitudeEnergy k₀ E) 0 s := by
  have h := (amplitudeOscillatorEnergy_hasDerivAt_zero E
    (compiledArgument k₀ E s)).scomp s (compiledArgument_hasDerivAt k₀ E s)
  change HasDerivAt
    (fun y : ℝ => amplitudeOscillatorEnergy E (compiledArgument k₀ E y)) (0 : ℝ) s
  simpa only [compiledAmplitudeEnergy, Function.comp_def, smul_eq_mul, mul_zero] using h

theorem compiledAmplitudeEnergy_const
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s t : ℝ) :
    compiledAmplitudeEnergy k₀ E s = compiledAmplitudeEnergy k₀ E t :=
  amplitudeOscillatorEnergy_const E (compiledArgument k₀ E s)
    (compiledArgument k₀ E t)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
