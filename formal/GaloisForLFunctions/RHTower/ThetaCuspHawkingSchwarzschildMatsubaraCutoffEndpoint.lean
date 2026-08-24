import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Hawking--Schwarzschild Matsubara cutoff endpoint

This module isolates a genuinely black-hole-specific RH experiment.  It combines three exact
inputs whose epistemic status must remain separate.

* **[LITERATURE]** For a Schwarzschild radius `Rₛ`, Hawking inverse temperature is
  `β_H = 4πRₛ`; hence bosonic Matsubara rates are `2πn / β_H = n / (2Rₛ)`.
* **[LITERATURE]** Correia--Gopalka--Isabella--Wolz, arXiv:2511.11794, prove that changing from
  tortoise-coordinate scattering to a hard radial cutoff multiplies the elastic amplitude by
  `(R_IR/Rₛ)^(2 i Rₛ ω)`.  Along `ω = i y`, its modulus is
  `exp (-2 Rₛ y log (R_IR/Rₛ))`.  Polynomial boundedness forces the sharp horizon bound
  `R_IR/Rₛ ≥ 1`.
* **[PROVED IN THE CORPUS]** The theta shell character has modulus `‖2^(1/2-s)‖`, logarithm
  `(1/2-Re s) log 2`, and functional-equation reflection sends it to its reciprocal.

At Hawking Matsubara rate, the gravitational large-diffeomorphism factor becomes the inverse
integer power of the cutoff ratio.  Therefore identifying the physical ratio `R_IR/Rₛ` with the
actual theta shell modulus makes Hawking Matsubara transport literally the theta shell tower,
not a thermal relabeling.

**[CONJECTURE] [OPEN CORE]** The source-specific dynamical statement is that the Xi/theta
scattering realization assigns `R_IR/Rₛ = ‖shellTransferCharacter s‖` to a sector labelled by
`s`, and that functional-equation partners remain separately polynomially bounded when they do
not mix.  This module does not assume or prove that realization.  It proves its exact
consequences: every off-line sector pair contains exactly one subhorizon cutoff and exactly one
exponentially divergent Hawking Matsubara gauge.  Thus unmixed admissibility is equivalent to RH;
if RH fails, admissible full dynamics must instead mix/dress every tilted reflection pair.

Hawking/KMS provenance for horizon reflectivity and the Boltzmann factor:
N. Oshita, Q. Wang, N. Afshordi, arXiv:1905.00464.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Hawking inverse temperature `β_H = 4πRₛ` in units `ℏ = c = k_B = 1`. -/
def schwarzschildHawkingInverseTemperature (radius : ℝ) : ℝ :=
  4 * Real.pi * radius

/-- Positive imaginary-frequency rate of bosonic Hawking Matsubara mode `n`. -/
def schwarzschildHawkingMatsubaraRate (radius : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * (n : ℝ) / schwarzschildHawkingInverseTemperature radius

/-- Hawking periodicity cancels Schwarzschild scale in the large-diffeomorphism exponent. -/
theorem schwarzschildHawkingMatsubaraRate_eq
    {radius : ℝ} (hradius : 0 < radius) (n : ℕ) :
    2 * radius * schwarzschildHawkingMatsubaraRate radius n = n := by
  rw [schwarzschildHawkingMatsubaraRate,
    schwarzschildHawkingInverseTemperature]
  have hradius0 : radius ≠ 0 := ne_of_gt hradius
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Modulus of the Schwarzschild hard-cutoff large-diffeomorphism factor on `ω = i rate`.

This is the modulus of `(R_IR/Rₛ)^(2 i Rₛ ω)`, with `cutoffRatio = R_IR/Rₛ`.
-/
def schwarzschildHardCutoffUpperImaginaryGauge
    (radius rate cutoffRatio : ℝ) : ℝ :=
  Real.exp (-(2 * radius * rate) * Real.log cutoffRatio)

/-- At Hawking Matsubara mode `n`, the gravitational cutoff gauge is exactly `ratio⁻ⁿ`. -/
theorem schwarzschildHardCutoffUpperImaginaryGauge_matsubara
    {radius cutoffRatio : ℝ} (hradius : 0 < radius)
    (hcutoff : 0 < cutoffRatio) (n : ℕ) :
    schwarzschildHardCutoffUpperImaginaryGauge radius
        (schwarzschildHawkingMatsubaraRate radius n) cutoffRatio =
      (cutoffRatio⁻¹) ^ n := by
  rw [schwarzschildHardCutoffUpperImaginaryGauge,
    schwarzschildHawkingMatsubaraRate_eq hradius]
  calc
    Real.exp (-(n : ℝ) * Real.log cutoffRatio) =
        Real.exp ((n : ℝ) * (-Real.log cutoffRatio)) := by ring_nf
    _ = (Real.exp (-Real.log cutoffRatio)) ^ n :=
      Real.exp_nat_mul (-Real.log cutoffRatio) n
    _ = (cutoffRatio⁻¹) ^ n := by
      rw [Real.exp_neg, Real.exp_log hcutoff]

/-- Conjectural Schwarzschild cutoff ratio supplied by the actual theta shell character. -/
def thetaSchwarzschildCutoffRatio (s : ℂ) : ℝ :=
  ‖shellTransferCharacter s‖

/-- Every theta-assigned Schwarzschild cutoff ratio is strictly positive. -/
theorem thetaSchwarzschildCutoffRatio_pos (s : ℂ) :
    0 < thetaSchwarzschildCutoffRatio s := by
  rw [thetaSchwarzschildCutoffRatio, norm_shellTransferCharacter]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- Cutoff logarithm is exactly theta shell-transfer entropy in the prime-two clock. -/
theorem thetaSchwarzschildCutoffRatio_log (s : ℂ) :
    Real.log (thetaSchwarzschildCutoffRatio s) =
      shellTransferEntropy s * Real.log 2 := by
  rw [thetaSchwarzschildCutoffRatio,
    log_norm_shellTransferCharacter, shellTransferEntropy_eq]

/-- Functional-equation partners receive reciprocal Schwarzschild cutoff ratios. -/
theorem thetaSchwarzschildCutoffRatio_reflection_mul (s : ℂ) :
    thetaSchwarzschildCutoffRatio s *
        thetaSchwarzschildCutoffRatio (1 - star s) = 1 := by
  have h := congrArg norm (shellTransferCharacter_reflection_pair s)
  simpa [thetaSchwarzschildCutoffRatio, Complex.norm_mul, norm_star] using h

/-- Hawking Matsubara dilation of a theta-labelled sector is its inverse shell tower. -/
theorem thetaSchwarzschildHawkingMatsubaraGauge_eq
    {radius : ℝ} (hradius : 0 < radius) (s : ℂ) (n : ℕ) :
    schwarzschildHardCutoffUpperImaginaryGauge radius
        (schwarzschildHawkingMatsubaraRate radius n)
        (thetaSchwarzschildCutoffRatio s) =
      (thetaSchwarzschildCutoffRatio s)⁻¹ ^ n :=
  schwarzschildHardCutoffUpperImaginaryGauge_matsubara hradius
    (thetaSchwarzschildCutoffRatio_pos s) n

/-- A subhorizon theta cutoff produces exponential growth along Hawking Matsubara modes. -/
theorem thetaSchwarzschildHawkingMatsubaraGauge_tendsto_atTop
    {radius : ℝ} (hradius : 0 < radius) {s : ℂ}
    (hsubhorizon : thetaSchwarzschildCutoffRatio s < 1) :
    Tendsto
      (fun n : ℕ =>
        schwarzschildHardCutoffUpperImaginaryGauge radius
          (schwarzschildHawkingMatsubaraRate radius n)
          (thetaSchwarzschildCutoffRatio s))
      atTop atTop := by
  simp_rw [thetaSchwarzschildHawkingMatsubaraGauge_eq hradius]
  exact tendsto_pow_atTop_atTop_of_one_lt
    ((one_lt_inv₀ (thetaSchwarzschildCutoffRatio_pos s)).2 hsubhorizon)

/-- A superhorizon theta cutoff suppresses the Hawking Matsubara gauge to zero. -/
theorem thetaSchwarzschildHawkingMatsubaraGauge_tendsto_zero
    {radius : ℝ} (hradius : 0 < radius) {s : ℂ}
    (hsuperhorizon : 1 < thetaSchwarzschildCutoffRatio s) :
    Tendsto
      (fun n : ℕ =>
        schwarzschildHardCutoffUpperImaginaryGauge radius
          (schwarzschildHawkingMatsubaraRate radius n)
          (thetaSchwarzschildCutoffRatio s))
      atTop (nhds 0) := by
  simp_rw [thetaSchwarzschildHawkingMatsubaraGauge_eq hradius]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (inv_pos.mpr (thetaSchwarzschildCutoffRatio_pos s)))
    ((inv_lt_one₀ (thetaSchwarzschildCutoffRatio_pos s)).2 hsuperhorizon)

/-- Both unmixed reflection sectors obey the Schwarzschild horizon cutoff bound. -/
def thetaSchwarzschildUnmixedCutoffAdmissible (s : ℂ) : Prop :=
  1 ≤ thetaSchwarzschildCutoffRatio s ∧
    1 ≤ thetaSchwarzschildCutoffRatio (1 - star s)

/-- Reciprocal Schwarzschild cutoff sectors are both admissible exactly at zero theta tilt. -/
theorem thetaSchwarzschildUnmixedCutoffAdmissible_iff (s : ℂ) :
    thetaSchwarzschildUnmixedCutoffAdmissible s ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨hs, hreflect⟩
    have hmul := thetaSchwarzschildCutoffRatio_reflection_mul s
    have hone : thetaSchwarzschildCutoffRatio s = 1 := by
      nlinarith
    exact (norm_shellTransferCharacter_eq_one_iff s).1 hone
  · intro hs
    have hone : thetaSchwarzschildCutoffRatio s = 1 :=
      (norm_shellTransferCharacter_eq_one_iff s).2 hs
    have hmul := thetaSchwarzschildCutoffRatio_reflection_mul s
    constructor
    · exact hone.ge
    · rw [hone, one_mul] at hmul
      exact hmul.ge

/-- Every nonzero tilt puts exactly one reflected cutoff behind the Schwarzschild horizon. -/
theorem thetaSchwarzschild_offLine_subhorizon_dichotomy
    {s : ℂ} (hoff : s.re ≠ 1 / 2) :
    (thetaSchwarzschildCutoffRatio s < 1 ∧
      1 < thetaSchwarzschildCutoffRatio (1 - star s)) ∨
    (thetaSchwarzschildCutoffRatio (1 - star s) < 1 ∧
      1 < thetaSchwarzschildCutoffRatio s) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · right
    constructor
    · rw [thetaSchwarzschildCutoffRatio,
        norm_shellTransferCharacter_lt_one_iff]
      simp only [Complex.sub_re, Complex.one_re, Complex.star_def,
        Complex.conj_re]
      linarith
    · exact (one_lt_norm_shellTransferCharacter_iff s).2 hleft
  · left
    constructor
    · exact (norm_shellTransferCharacter_lt_one_iff s).2 hright
    · rw [thetaSchwarzschildCutoffRatio,
        one_lt_norm_shellTransferCharacter_iff]
      simp only [Complex.sub_re, Complex.one_re, Complex.star_def,
        Complex.conj_re]
      linarith

/-- **Off-line Hawking prediction.** Exactly one unmixed reflection sector has a divergent
Hawking Matsubara large-diffeomorphism gauge. -/
theorem thetaSchwarzschild_offLine_one_matsubaraGauge_diverges
    {radius : ℝ} (hradius : 0 < radius) {s : ℂ}
    (hoff : s.re ≠ 1 / 2) :
    (Tendsto
          (fun n : ℕ =>
            schwarzschildHardCutoffUpperImaginaryGauge radius
              (schwarzschildHawkingMatsubaraRate radius n)
              (thetaSchwarzschildCutoffRatio s))
          atTop atTop ∧
        Tendsto
          (fun n : ℕ =>
            schwarzschildHardCutoffUpperImaginaryGauge radius
              (schwarzschildHawkingMatsubaraRate radius n)
              (thetaSchwarzschildCutoffRatio (1 - star s)))
          atTop (nhds 0)) ∨
      (Tendsto
          (fun n : ℕ =>
            schwarzschildHardCutoffUpperImaginaryGauge radius
              (schwarzschildHawkingMatsubaraRate radius n)
              (thetaSchwarzschildCutoffRatio (1 - star s)))
          atTop atTop ∧
        Tendsto
          (fun n : ℕ =>
            schwarzschildHardCutoffUpperImaginaryGauge radius
              (schwarzschildHawkingMatsubaraRate radius n)
              (thetaSchwarzschildCutoffRatio s))
          atTop (nhds 0)) := by
  rcases thetaSchwarzschild_offLine_subhorizon_dichotomy hoff with h | h
  · exact Or.inl
      ⟨thetaSchwarzschildHawkingMatsubaraGauge_tendsto_atTop hradius h.1,
        thetaSchwarzschildHawkingMatsubaraGauge_tendsto_zero hradius h.2⟩
  · exact Or.inr
      ⟨thetaSchwarzschildHawkingMatsubaraGauge_tendsto_atTop hradius h.1,
        thetaSchwarzschildHawkingMatsubaraGauge_tendsto_zero hradius h.2⟩

/-- Global conjectural producer: every Xi-zero sector and its reflection remain separately
polynomially bounded under the theta--Schwarzschild cutoff identification. -/
def thetaXiSchwarzschildUnmixedPolynomialBoundedness : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → thetaSchwarzschildUnmixedCutoffAdmissible ρ

/-- **Hawking--Schwarzschild RH endpoint.** Unmixed polynomial boundedness of every reciprocal
theta cutoff pair is equivalent to the Riemann hypothesis. -/
theorem thetaXiSchwarzschildUnmixedPolynomialBoundedness_iff_riemannHypothesis :
    thetaXiSchwarzschildUnmixedPolynomialBoundedness ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h ρ hρ
    exact (thetaSchwarzschildUnmixedCutoffAdmissible_iff ρ).1 (h ρ hρ)
  · intro h ρ hρ
    exact (thetaSchwarzschildUnmixedCutoffAdmissible_iff ρ).2 (h ρ hρ)

end

end RHTower
