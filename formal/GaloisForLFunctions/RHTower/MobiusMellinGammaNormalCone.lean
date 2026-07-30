import GaloisForLFunctions.RHTower.ArchimedeanGamma
import GaloisForLFunctions.RHTower.MobiusSquarefreeReciprocalTransfer
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The critical Möbius score in the Mellin--Gamma normal cone

The critical squarefree score and the Gamma source do not share an affine coordinate.  Their
source-natural comparison is Mellin duality: multiplication by the critical radial variable is
translation by two in the Mellin parameter of `Gammaℝ`.

The same file records the deformation-to-the-normal-cone forced by the Euler pole.  The completed
Möbius transfer vanishes to first order in the base parameter; division by that normal parameter
extends through the pole by the analytic zeta residue unit.  Its exceptional value is the
reciprocal source section.  Although the finite transfer is a separated rank-one function of base
and spectral variables, the exceptional reciprocal section retains its nontrivial projective
horizon connection.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Mellin response of the density-weighted critical score `2(1-y) exp(-y)`. -/
def criticalMobiusScoreMellin (z : ℂ) : ℂ :=
  2 * (1 - z) * Complex.Gamma z

/-- **Source-natural Gamma comparison.**  The critical score is the Gamma recurrence defect.
This compares multiplication by `1-y` on the critical boundary with translation of the Mellin
parameter; it does not identify the two variables. -/
theorem criticalMobiusScoreMellin_eq_gammaShiftDefect
    {z : ℂ} (hz : z ≠ 0) :
    criticalMobiusScoreMellin z =
      2 * (Complex.Gamma z - Complex.Gamma (z + 1)) := by
  rw [Complex.Gamma_add_one z hz]
  simp only [criticalMobiusScoreMellin]
  ring

/-- Radial Mellin response in the exact real archimedean normalization.  Under `y = π r²`,
this is the transform of the same critical score against the Gaussian radial kernel. -/
def criticalMobiusRadialScoreMellin (s : ℂ) : ℂ :=
  (2 - s) * Complex.Gammaℝ s

/-- Multiplication by the radial variable `π r²` is the source-induced shift `s ↦ s+2`.
Consequently the radial critical score is the exact `Gammaℝ` shift defect. -/
theorem criticalMobiusRadialScoreMellin_eq_gammaRealShiftDefect
    {s : ℂ} (hs : s ≠ 0) :
    criticalMobiusRadialScoreMellin s =
      2 * (Complex.Gammaℝ s - (Real.pi : ℂ) * Complex.Gammaℝ (s + 2)) := by
  rw [GaloisForLFunctions.gammaReal_shift_two hs]
  simp only [criticalMobiusRadialScoreMellin]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The completed archimedean factor cancels on the distinguished radial score, leaving a purely
rational two-pole section.  The denominator-free form needs no nonvanishing hypotheses. -/
theorem criticalMobiusRadialScoreMellin_mul_polynomial_eq_archFactor
    (s : ℂ) :
    criticalMobiusRadialScoreMellin s * (s * (s - 1)) =
      2 * (2 - s) * archFactor s := by
  simp only [criticalMobiusRadialScoreMellin, archFactor]
  ring

/-- Ratio form of the exact archimedean cancellation. -/
theorem criticalMobiusRadialScoreMellin_div_archFactor
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    criticalMobiusRadialScoreMellin s / archFactor s =
      2 * (2 - s) / (s * (s - 1)) := by
  simp only [criticalMobiusRadialScoreMellin, archFactor]
  field_simp [hs0, sub_ne_zero.mpr hs1, hGamma]

/-- The rational normal form left after archimedean cancellation. -/
def criticalMobiusRadialRationalSection (s : ℂ) : ℂ :=
  2 * (2 - s) / (s * (s - 1))

/-- The radial normal form splits into one pole on each side of the critical line.  The right pole
has coefficient two, hence its standard half-plane Cauchy vector has squared norm four. -/
theorem criticalMobiusRadialRationalSection_eq_polarized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    criticalMobiusRadialRationalSection s = -4 / s + 2 / (s - 1) := by
  simp only [criticalMobiusRadialRationalSection]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- The separated completed source transfer before blowing up the Euler-pole base zero. -/
def separatedCompletedMobiusTransfer
    (X : ℂ → ℂ) (base s : ℂ) : ℂ :=
  (riemannZeta base * X s)⁻¹

/-- The deformation-to-the-normal-cone extension, using the analytic zeta residue unit. -/
def mobiusCompletedNormalConeTransfer
    (X : ℂ → ℂ) (base s : ℂ) : ℂ :=
  (zetaResidueUnit base * X s)⁻¹

/-- Away from the Euler pole, the normal-cone extension is the completed transfer divided by the
normal parameter `base-1`. -/
theorem mobiusCompletedNormalConeTransfer_eq_div
    {X : ℂ → ℂ} {base s : ℂ}
    (hbase : base ≠ 1) (hzeta : riemannZeta base ≠ 0) (hX : X s ≠ 0) :
    mobiusCompletedNormalConeTransfer X base s =
      separatedCompletedMobiusTransfer X base s / (base - 1) := by
  have hresidue : zetaResidueUnit base = (base - 1) * riemannZeta base := by
    simp only [zetaResidueUnit, Function.update_of_ne hbase]
  rw [mobiusCompletedNormalConeTransfer, separatedCompletedMobiusTransfer, hresidue]
  field_simp [hbase, hzeta, hX]

/-- The exceptional normal-cone section is exactly the reciprocal source section. -/
@[simp] theorem mobiusCompletedNormalConeTransfer_one
    (X : ℂ → ℂ) (s : ℂ) :
    mobiusCompletedNormalConeTransfer X 1 s = (X s)⁻¹ := by
  simp [mobiusCompletedNormalConeTransfer]

/-- The blown-up transfer is genuinely analytic through the Euler-pole base point whenever the
spectral section is nonzero there. -/
theorem mobiusCompletedNormalConeTransfer_analyticAt_one
    {X : ℂ → ℂ} {s : ℂ} (hX : X s ≠ 0) :
    AnalyticAt ℂ (fun base => mobiusCompletedNormalConeTransfer X base s) 1 := by
  have hprod : AnalyticAt ℂ (fun base => zetaResidueUnit base * X s) 1 :=
    zetaResidueUnit_analyticAt.mul analyticAt_const
  have hne : zetaResidueUnit 1 * X s ≠ 0 := by
    simpa using hX
  change AnalyticAt ℂ ((fun base => zetaResidueUnit base * X s)⁻¹) 1
  exact hprod.inv hne

/-- Hence the ordinary transfers divided by their Euler normal parameter converge to the
reciprocal exceptional section. -/
theorem tendsto_mobiusCompletedNormalConeTransfer_one
    {X : ℂ → ℂ} {s : ℂ} (hX : X s ≠ 0) :
    Tendsto (fun base => mobiusCompletedNormalConeTransfer X base s)
      (𝓝 1) (𝓝 ((X s)⁻¹)) := by
  rw [← mobiusCompletedNormalConeTransfer_one X s]
  exact (mobiusCompletedNormalConeTransfer_analyticAt_one hX).continuousAt

/-- The projectivized square of the exceptional section is the reciprocal-horizon transition. -/
@[simp] theorem neg_sq_mobiusCompletedNormalConeTransfer_one
    (X : ℂ → ℂ) (s : ℂ) :
    -(mobiusCompletedNormalConeTransfer X 1 s) ^ 2 = -(X s)⁻¹ ^ 2 := by
  simp

/-- **Finite mixed-curvature no-go.**  The entire two-variable normal-cone family has separated
rank one: every `2 x 2` cross minor vanishes.  Thus the reciprocal-horizon Ward class cannot be an
ordinary finite mixed curvature of the base and spectral variables; it is exceptional-boundary
data of the blown-up family. -/
theorem mobiusCompletedNormalConeTransfer_cross_minor_zero
    (X : ℂ → ℂ) (base₁ base₂ s₁ s₂ : ℂ) :
    mobiusCompletedNormalConeTransfer X base₁ s₁ *
        mobiusCompletedNormalConeTransfer X base₂ s₂ =
      mobiusCompletedNormalConeTransfer X base₁ s₂ *
        mobiusCompletedNormalConeTransfer X base₂ s₁ := by
  simp only [mobiusCompletedNormalConeTransfer]
  ring

end RHTower
