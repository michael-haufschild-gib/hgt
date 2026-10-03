import GaloisForLFunctions.RHTower.PMRamanujanBandHilbert
import GaloisForLFunctions.RHTower.PMRamanujanBandCutoffMellin
import GaloisForLFunctions.RHTower.L2MellinUnitary

/-!
# Actual moving-band Mellin carrier

The complete natural denominator band has an exact critical-frequency L2 carrier.
Multiplication by its literal cutoff phase preserves the complete signed energy.
The scale integral of this representative equals the audited arithmetic cutoff
transform in its initial half-plane, with zeta cleared and q=1 subtracted.
No cutoff-uniform norm estimate or analytic continuation is asserted here.
-/

open MeasureTheory Set Complex Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The literal critical-frequency vector at the real natural cutoff. -/
def pmRamanujanNaturalBandMellinVector (ε X : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  if hX : 1 ≤ ⌊X⌋₊ then pmRamanujanBandMellinVector ε ⌊X⌋₊ ⌊2*X⌋₊ hX else 0

theorem pmRamanujanNaturalBandMellinVector_eq (ε : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    pmRamanujanNaturalBandMellinVector ε X =
      pmRamanujanBandMellinVector ε ⌊X⌋₊ ⌊2*X⌋₊ ((Nat.one_le_floor_iff X).mpr hX) := by
  simp [pmRamanujanNaturalBandMellinVector, (Nat.one_le_floor_iff X).mpr hX]

def pmRamanujanNormalizedBandMellinVector (ε X : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((X^ε : ℝ) : ℂ) • pmRamanujanNaturalBandMellinVector ε X

/-- The exact cutoff phase on the actual complete critical-frequency vector. -/
def pmRamanujanMovingBandMellinVector (ε X : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  MellinL2.fourierPhaseMulUnitary (Real.log X/(2*Real.pi))
    (pmRamanujanNormalizedBandMellinVector ε X)

private theorem pmbm_phase_eq_cpow {X : ℝ} (hX : 0 < X) (ε τ : ℝ) :
    MellinL2.fourierPhase (Real.log X/(2*Real.pi)) τ * ((X^ε : ℝ) : ℂ) =
      (X : ℂ)^((ε : ℂ)+(τ : ℂ)*I) := by
  have hp : 2*Real.pi*((Real.log X/(2*Real.pi))*τ) = Real.log X*τ := by
    field_simp [Real.pi_ne_zero]
  rw [MellinL2.fourierPhase, Real.fourierChar_apply, hp,
    Real.rpow_def_of_pos hX, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    ← Complex.ofReal_log hX.le, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pmRamanujanMovingBandMellinVector_ae (ε : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    (pmRamanujanMovingBandMellinVector ε X : ℝ → ℂ) =ᵐ[volume]
      fun τ => (X : ℂ)^((ε : ℂ)+(τ : ℂ)*I) *
        pmRamanujanBandMellinTrace ε ⌊X⌋₊ ⌊2*X⌋₊ τ := by
  have hfloor := (Nat.one_le_floor_iff X).mpr hX
  have hv := (memLp_pmRamanujanBandMellinTrace ε hfloor (Y := ⌊2*X⌋₊)).coeFn_toLp
  have hs := Lp.coeFn_smul ((X^ε : ℝ) : ℂ) (pmRamanujanNaturalBandMellinVector ε X)
  have hp := MellinL2.fourierPhaseMulAux_ae (Real.log X/(2*Real.pi))
    (pmRamanujanNormalizedBandMellinVector ε X)
  filter_upwards [hv, hs, hp] with τ hv hs hp
  change (pmRamanujanMovingBandMellinVector ε X : ℝ → ℂ) τ = _ at hp
  rw [hp]
  change (pmRamanujanNormalizedBandMellinVector ε X : ℝ → ℂ) τ = _ at hs
  rw [hs, Pi.smul_apply, smul_eq_mul, pmRamanujanNaturalBandMellinVector_eq ε hX]
  change (pmRamanujanBandMellinVector ε ⌊X⌋₊ ⌊2*X⌋₊ hfloor : ℝ → ℂ) τ = _ at hv
  rw [hv, ← mul_assoc, pmbm_phase_eq_cpow (by linarith : 0 < X)]

theorem norm_sq_pmRamanujanMovingBandMellinVector (ε : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    ‖pmRamanujanMovingBandMellinVector ε X‖^2 =
      2*Real.pi*(X^ε)^2 *
        ∑' n : ℕ, ‖pmRamanujanDenominatorBand ε ⌊X⌋₊ ⌊2*X⌋₊ (n+1)‖^2 /
          (((n : ℝ)+1)*((n : ℝ)+2)) := by
  rw [pmRamanujanMovingBandMellinVector,
    (MellinL2.fourierPhaseMulUnitary _).norm_map,
    pmRamanujanNormalizedBandMellinVector, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < X) ε),
    mul_pow, pmRamanujanNaturalBandMellinVector_eq ε hX,
    norm_sq_pmRamanujanBandMellinVector, norm_sq_pmRamanujanBandLogVector_eq_energy]
  ring

/-- Literal moving trace; it is the representative of the unitary moving vector. -/
def pmRamanujanMovingBandMellinTrace (ε X τ : ℝ) : ℂ :=
  (X : ℂ)^((ε : ℂ)+(τ : ℂ)*I) *
    pmRamanujanBandMellinTrace ε ⌊X⌋₊ ⌊2*X⌋₊ τ

private theorem pmbm_mellin_integrand (ε τ : ℝ) (z : ℂ) {X : ℝ} (hX : 1 ≤ X) :
    (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanMovingBandMellinTrace ε X τ =
      riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I) *
        (pmRamanujanBandScaleSymbol ε ((1/2 : ℂ)+(τ : ℂ)*I) X *
          (X : ℂ)^((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z-1)) := by
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he : (-z-(1/2 : ℂ))+((ε : ℂ)+(τ : ℂ)*I) =
      (ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z-1 := by ring
  calc
    _ = riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I) *
        (pmRamanujanBandScaleSymbol ε ((1/2 : ℂ)+(τ : ℂ)*I) X *
          ((X : ℂ)^(-z-(1/2 : ℂ)) * (X : ℂ)^((ε : ℂ)+(τ : ℂ)*I))) := by
      simp only [pmRamanujanMovingBandMellinTrace, pmRamanujanBandMellinTrace,
        pmRamanujanBandScaleSymbol]
      ring
    _ = _ := by rw [← Complex.cpow_add _ _ hX0, he]

theorem integrableOn_pmRamanujanMovingBandMellinTrace {ε : ℝ} (hε : 0 < ε)
    (τ : ℝ) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun X : ℝ => (X : ℂ)^(-z-(1/2 : ℂ)) *
      pmRamanujanMovingBandMellinTrace ε X τ) (Ici 1) := by
  have hi := (integrableOn_pmRamanujanBandScaleSymbol_cpow hε hz
    (s := (1/2 : ℂ)+(τ : ℂ)*I) (by norm_num)).const_mul
      (riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
  exact (pmbm_mellin_integrand ε τ z hX).symm

/-- Exact scale transform of the actual moving Hilbert representative, with zeta cleared. -/
theorem pmRamanujanMovingBandMellin_cleared_eq {ε : ℝ} (hε : 0 < ε)
    (τ : ℝ) {z : ℂ} (hz : 1 < z.re)
    (hr : (ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z ≠ 0) :
    riemannZeta z * (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) *
      pmRamanujanMovingBandMellinTrace ε X τ) =
      pmPowerDampedDivisorDensity ε *
        (riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I)) *
        ((1-(2 : ℂ)^(-((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z)))/
          ((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z)) *
        (riemannZeta (1+z-((1/2 : ℂ)+(τ : ℂ)*I)) *
          pmRamanujanBandEulerCorrection ε z ((1/2 : ℂ)+(τ : ℂ)*I) -
            riemannZeta z) := by
  have he : (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) *
      pmRamanujanMovingBandMellinTrace ε X τ) =
      (riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I)) *
        ∫ X in Ici (1 : ℝ), pmRamanujanBandScaleSymbol ε ((1/2 : ℂ)+(τ : ℂ)*I) X *
          (X : ℂ)^((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z-1) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
    exact pmbm_mellin_integrand ε τ z hX
  rw [he, ← mul_assoc, mul_comm (riemannZeta z), mul_assoc,
    pmRamanujanBandCutoffMellin_cleared_eq hε hz (by norm_num) hr]
  ring

end RHTower
