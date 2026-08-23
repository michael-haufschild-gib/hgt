import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorKreinCayleyEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint

/-!
# Canonical Krein--Cayley cascade no-go for first-order Hawking mixing

The earlier delayed-onset countermodel inserted `lambda ^ m` directly into one Cayley load.  This
module removes that freedom.  Each local scattering cell uses the primitive open-disk coordinate
`lambda`, the exact two-mode bosonic `SU(1,1)` Krein--Cayley chart, and has nonzero first coupling
derivative.  Cascading two such cells through one intermediate Nambu mode nevertheless gives the
source-to-terminal amplitude

`4 * lambda ^ 2 / (1 - lambda ^ 2) ^ 2`.

The cascade preserves the three-mode signed Hermitian form, mixes the terminal mode at every
nonzero real disk coordinate, and admits exact Hawking KMS detailed balance, while its terminal
first coupling derivative vanishes.  Thus canonical nonperturbative completion, source-linear
local cells, Krein losslessness, KMS, and finite-coupling connectivity do not force first-order
mixing.  The surviving RH-bearing producer must prove a theta-specific one-step observability law:
every tilted resonance sector is directly source-adjacent, not merely connected through a finite
scattering cascade.

Physical provenance: bosonic Bogoliubov transformations and quantum Stratonovich scattering
cascades.  The theorem below is an exact finite-dimensional obstruction, not a claim that a
particular moving-mirror model realizes this cascade.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Primitive real slice of the bosonic Krein--Cayley chart -/

/-- Positive-sheet coefficient of one canonical cell at real disk coordinate `lambda`. -/
def primitiveHawkingKreinCayleyGain (lambda : ℝ) : ℝ :=
  (1 + lambda ^ 2) / (1 - lambda ^ 2)

/-- Off-diagonal pair coefficient of one canonical cell at real disk coordinate `lambda`. -/
def primitiveHawkingKreinCayleyPair (lambda : ℝ) : ℝ :=
  2 * lambda / (1 - lambda ^ 2)

/-- The primitive gain is exactly the real slice of the canonical bosonic Krein--Cayley chart. -/
theorem primitiveHawkingKreinCayleyGain_eq_twoModeBosonicKreinCayleyGain
    (lambda : ℝ) :
    primitiveHawkingKreinCayleyGain lambda =
      twoModeBosonicKreinCayleyGain (lambda : ℂ) := by
  simp [primitiveHawkingKreinCayleyGain, twoModeBosonicKreinCayleyGain, pow_two]

/-- The primitive pair coefficient is exactly the real slice of the canonical chart. -/
theorem ofReal_primitiveHawkingKreinCayleyPair_eq_twoModeBosonicKreinCayleyPair
    (lambda : ℝ) :
    (primitiveHawkingKreinCayleyPair lambda : ℂ) =
      twoModeBosonicKreinCayleyPair (lambda : ℂ) := by
  simp [primitiveHawkingKreinCayleyPair, twoModeBosonicKreinCayleyPair, pow_two]

/-- Every primitive disk cell lies on the positive bosonic `SU(1,1)` sheet. -/
theorem primitiveHawkingKreinCayleyGain_sq_sub_pair_sq
    {lambda : ℝ} (hlambda : lambda ^ 2 < 1) :
    primitiveHawkingKreinCayleyGain lambda ^ 2 -
        primitiveHawkingKreinCayleyPair lambda ^ 2 = 1 := by
  have hden : 1 - lambda ^ 2 ≠ 0 := by linarith
  rw [primitiveHawkingKreinCayleyGain, primitiveHawkingKreinCayleyPair]
  field_simp [hden]
  ring

/-- Positive Nambu output of one primitive canonical cell. -/
def primitiveHawkingKreinCayleyPositiveOutput
    (lambda : ℝ) (x h : ℂ) : ℂ :=
  (primitiveHawkingKreinCayleyGain lambda : ℂ) * x +
    (primitiveHawkingKreinCayleyPair lambda : ℂ) * h

/-- Negative Nambu output of one primitive canonical cell. -/
def primitiveHawkingKreinCayleyNegativeOutput
    (lambda : ℝ) (x h : ℂ) : ℂ :=
  (primitiveHawkingKreinCayleyPair lambda : ℂ) * x +
    (primitiveHawkingKreinCayleyGain lambda : ℂ) * h

/-- One primitive canonical cell preserves the two-mode signed Hermitian form. -/
theorem primitiveHawkingKreinCayley_preserves_signedHermitian
    {lambda : ℝ} (hlambda : lambda ^ 2 < 1) (x h : ℂ) :
    conj (primitiveHawkingKreinCayleyPositiveOutput lambda x h) *
          primitiveHawkingKreinCayleyPositiveOutput lambda x h -
        conj (primitiveHawkingKreinCayleyNegativeOutput lambda x h) *
          primitiveHawkingKreinCayleyNegativeOutput lambda x h =
      conj x * x - conj h * h := by
  let g := primitiveHawkingKreinCayleyGain lambda
  let p := primitiveHawkingKreinCayleyPair lambda
  have hccr := primitiveHawkingKreinCayleyGain_sq_sub_pair_sq hlambda
  have hccrC := congrArg (fun y : ℝ => (y : ℂ)) hccr
  push_cast at hccrC
  change conj ((g : ℂ) * x + (p : ℂ) * h) *
        ((g : ℂ) * x + (p : ℂ) * h) -
      conj ((p : ℂ) * x + (g : ℂ) * h) *
        ((p : ℂ) * x + (g : ℂ) * h) =
      conj x * x - conj h * h
  simp only [map_add, map_mul, conj_ofReal]
  linear_combination (conj x * x - conj h * h) * hccrC

/-- A primitive canonical cell has a nonzero first pair-amplitude coupling jet. -/
theorem hasDerivAt_primitiveHawkingKreinCayleyPair_zero :
    HasDerivAt primitiveHawkingKreinCayleyPair 2 0 := by
  change HasDerivAt (fun lambda : ℝ => 2 * lambda / (1 - lambda ^ 2)) 2 0
  have hn := (hasDerivAt_id (𝕜 := ℝ) 0).const_mul (2 : ℝ)
  have hd := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
    ((hasDerivAt_id (𝕜 := ℝ) 0).pow 2)
  have hq := hn.div hd (by norm_num)
  have hfun : (fun x : ℝ => 2 * x / (1 - x ^ 2)) =
      (fun y => 2 * id y) / ((fun _ : ℝ => 1) - id ^ 2) := by
    funext x
    rfl
  rw [hfun]
  norm_num at hq
  exact hq

/-! ## Two-cell source-to-terminal cascade -/

/-- Source-side positive output after the first cell. -/
def primitiveHawkingKreinCayleyCascadeSourceOutput
    (lambda : ℝ) (x₀ x₁ _x₂ : ℂ) : ℂ :=
  primitiveHawkingKreinCayleyPositiveOutput lambda x₀ x₁

/-- Negative intermediate output after the second cell. -/
def primitiveHawkingKreinCayleyCascadeMiddleOutput
    (lambda : ℝ) (x₀ x₁ x₂ : ℂ) : ℂ :=
  primitiveHawkingKreinCayleyNegativeOutput lambda x₂
    (primitiveHawkingKreinCayleyNegativeOutput lambda x₀ x₁)

/-- Terminal positive output after the second cell. -/
def primitiveHawkingKreinCayleyCascadeTerminalOutput
    (lambda : ℝ) (x₀ x₁ x₂ : ℂ) : ℂ :=
  primitiveHawkingKreinCayleyPositiveOutput lambda x₂
    (primitiveHawkingKreinCayleyNegativeOutput lambda x₀ x₁)

/-- Two canonical cells preserve the three-mode signature `(+,-,+)`. -/
theorem primitiveHawkingKreinCayleyCascade_preserves_signedHermitian
    {lambda : ℝ} (hlambda : lambda ^ 2 < 1) (x₀ x₁ x₂ : ℂ) :
    conj (primitiveHawkingKreinCayleyCascadeSourceOutput lambda x₀ x₁ x₂) *
          primitiveHawkingKreinCayleyCascadeSourceOutput lambda x₀ x₁ x₂ -
        conj (primitiveHawkingKreinCayleyCascadeMiddleOutput lambda x₀ x₁ x₂) *
          primitiveHawkingKreinCayleyCascadeMiddleOutput lambda x₀ x₁ x₂ +
        conj (primitiveHawkingKreinCayleyCascadeTerminalOutput lambda x₀ x₁ x₂) *
          primitiveHawkingKreinCayleyCascadeTerminalOutput lambda x₀ x₁ x₂ =
      conj x₀ * x₀ - conj x₁ * x₁ + conj x₂ * x₂ := by
  have hfirst := primitiveHawkingKreinCayley_preserves_signedHermitian
    hlambda x₀ x₁
  have hsecond := primitiveHawkingKreinCayley_preserves_signedHermitian
    hlambda x₂ (primitiveHawkingKreinCayleyNegativeOutput lambda x₀ x₁)
  rw [primitiveHawkingKreinCayleyCascadeSourceOutput,
    primitiveHawkingKreinCayleyCascadeMiddleOutput,
    primitiveHawkingKreinCayleyCascadeTerminalOutput]
  linear_combination hfirst + hsecond

/-- End-to-end source amplitude is the product of the two primitive pair coefficients. -/
theorem primitiveHawkingKreinCayleyCascadeTerminal_source_eq_pair_sq
    (lambda : ℝ) :
    primitiveHawkingKreinCayleyCascadeTerminalOutput lambda 1 0 0 =
      (primitiveHawkingKreinCayleyPair lambda : ℂ) ^ 2 := by
  simp [primitiveHawkingKreinCayleyCascadeTerminalOutput,
    primitiveHawkingKreinCayleyPositiveOutput,
    primitiveHawkingKreinCayleyNegativeOutput, pow_two]

/-- Explicit quadratic source-to-terminal amplitude of the canonical two-cell cascade. -/
theorem primitiveHawkingKreinCayleyCascadeTerminal_source_eq
    (lambda : ℝ) :
    primitiveHawkingKreinCayleyCascadeTerminalOutput lambda 1 0 0 =
      ((4 * lambda ^ 2 / (1 - lambda ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [primitiveHawkingKreinCayleyCascadeTerminal_source_eq_pair_sq,
    primitiveHawkingKreinCayleyPair]
  norm_cast
  rw [div_pow]
  ring

/-- Every nonzero real disk coordinate mixes source into the terminal mode. -/
theorem primitiveHawkingKreinCayleyCascadeTerminal_source_ne_zero
    {lambda : ℝ} (hlambda : lambda ≠ 0) (hdisk : lambda ^ 2 < 1) :
    primitiveHawkingKreinCayleyCascadeTerminalOutput lambda 1 0 0 ≠ 0 := by
  have hden : 1 - lambda ^ 2 ≠ 0 := by linarith
  rw [primitiveHawkingKreinCayleyCascadeTerminal_source_eq_pair_sq]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
    (div_ne_zero (mul_ne_zero (by norm_num) hlambda) hden))

/-- Despite primitive linear local cells, the end-to-end first coupling jet vanishes. -/
theorem hasDerivAt_primitiveHawkingKreinCayleyCascadeTerminal_source_zero :
    HasDerivAt
      (fun lambda : ℝ =>
        primitiveHawkingKreinCayleyPair lambda ^ 2) 0 0 := by
  have hmul := hasDerivAt_primitiveHawkingKreinCayleyPair_zero.mul
    hasDerivAt_primitiveHawkingKreinCayleyPair_zero
  have hfun :
      (fun lambda : ℝ => primitiveHawkingKreinCayleyPair lambda ^ 2) =
        primitiveHawkingKreinCayleyPair * primitiveHawkingKreinCayleyPair := by
    funext lambda
    simp [pow_two]
  rw [hfun]
  norm_num [primitiveHawkingKreinCayleyPair] at hmul
  exact hmul

/-! ## Exact Hawking KMS dressing of the terminal transition -/

/-- Upward KMS probability carried by the source-to-terminal cascade channel. -/
def primitiveHawkingKreinCayleyCascadeKMSUpProbability
    (lambda kappa omega : ℝ) : ℝ :=
  primitiveHawkingKreinCayleyPair lambda ^ 4 *
    thetaCuspHawkingKMSExcitedPopulation kappa omega

/-- Downward KMS probability carried by the source-to-terminal cascade channel. -/
def primitiveHawkingKreinCayleyCascadeKMSDownProbability
    (lambda kappa omega : ℝ) : ℝ :=
  primitiveHawkingKreinCayleyPair lambda ^ 4 *
    (1 - thetaCuspHawkingKMSExcitedPopulation kappa omega)

/-- Exact Hawking detailed balance is compatible with quadratic end-to-end amplitude onset. -/
theorem primitiveHawkingKreinCayleyCascadeKMSUpProbability_eq_ratio_mul_down
    (lambda kappa omega : ℝ) :
    primitiveHawkingKreinCayleyCascadeKMSUpProbability lambda kappa omega =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        primitiveHawkingKreinCayleyCascadeKMSDownProbability
          lambda kappa omega := by
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  have hq : 1 + q ≠ 0 := by
    linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega]
  rw [primitiveHawkingKreinCayleyCascadeKMSUpProbability,
    primitiveHawkingKreinCayleyCascadeKMSDownProbability,
    thetaCuspHawkingKMSExcitedPopulation]
  change _ * (q / (1 + q)) = q * (_ * (1 - q / (1 + q)))
  field_simp [hq]
  ring

/-- **[NO-GO] [PAPER-PROVED] [LEAN-PROVED]** Two canonical source-linear
Krein--Cayley cells have nonzero local first jets, exact three-mode signed conservation, exact
Hawking KMS detailed balance, and nonzero finite-coupling source-to-terminal mixing, but their
end-to-end first coupling jet vanishes.  Generic full dynamics therefore cannot replace the
theta-specific direct one-step observability theorem required by the RH route. -/
theorem canonicalKreinCayleyCascade_lossless_KMS_mixing_not_force_firstOrder :
    HasDerivAt primitiveHawkingKreinCayleyPair 2 0 ∧
    HasDerivAt
      (fun lambda : ℝ => primitiveHawkingKreinCayleyPair lambda ^ 2) 0 0 ∧
    (∀ lambda : ℝ, lambda ^ 2 < 1 → ∀ x₀ x₁ x₂ : ℂ,
      conj (primitiveHawkingKreinCayleyCascadeSourceOutput lambda x₀ x₁ x₂) *
            primitiveHawkingKreinCayleyCascadeSourceOutput lambda x₀ x₁ x₂ -
          conj (primitiveHawkingKreinCayleyCascadeMiddleOutput lambda x₀ x₁ x₂) *
            primitiveHawkingKreinCayleyCascadeMiddleOutput lambda x₀ x₁ x₂ +
          conj (primitiveHawkingKreinCayleyCascadeTerminalOutput lambda x₀ x₁ x₂) *
            primitiveHawkingKreinCayleyCascadeTerminalOutput lambda x₀ x₁ x₂ =
        conj x₀ * x₀ - conj x₁ * x₁ + conj x₂ * x₂) ∧
    (∀ lambda : ℝ, lambda ≠ 0 → lambda ^ 2 < 1 →
      primitiveHawkingKreinCayleyCascadeTerminalOutput lambda 1 0 0 ≠ 0) ∧
    (∀ lambda kappa omega : ℝ,
      primitiveHawkingKreinCayleyCascadeKMSUpProbability lambda kappa omega =
        thetaCuspHawkingKMSBoltzmannRatio kappa omega *
          primitiveHawkingKreinCayleyCascadeKMSDownProbability
            lambda kappa omega) := by
  exact ⟨hasDerivAt_primitiveHawkingKreinCayleyPair_zero,
    hasDerivAt_primitiveHawkingKreinCayleyCascadeTerminal_source_zero,
    fun _ hlambda => primitiveHawkingKreinCayleyCascade_preserves_signedHermitian hlambda,
    fun _ hlambda hdisk =>
      primitiveHawkingKreinCayleyCascadeTerminal_source_ne_zero hlambda hdisk,
    primitiveHawkingKreinCayleyCascadeKMSUpProbability_eq_ratio_mul_down⟩

end RHTower
