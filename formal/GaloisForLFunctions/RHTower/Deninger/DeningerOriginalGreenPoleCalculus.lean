import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.Order

/-!
# Original translation denominator: poles and Laurent coefficients

The original period fixes both the imaginary pole lattice and the residue
normalization. Divided differences identify the Laurent coefficient without
changing the numerator, deleting a boundary, or assuming a spectral zero simple.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem quotient_laurentCoeff_of_simple_zero {N D : ℂ → ℂ} {s d : ℂ}
    (hN : AnalyticAt ℂ N s) (hD : AnalyticAt ℂ D s)
    (hDz : D s = 0) (hd : HasDerivAt D d s) (hd0 : d ≠ 0) :
    laurentCoeff (fun z => N z / D z) s (-1) = N s / d := by
  have hds : AnalyticAt ℂ (dslope D s) s := by
    obtain ⟨p,hp⟩ := hD
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have hds0 : dslope D s s ≠ 0 := by rwa [dslope_same, hd.deriv]
  have hA : AnalyticAt ℂ (fun z => N z / dslope D s z) s := hN.div hds hds0
  have hfac (z : ℂ) : D z = (z-s) * dslope D s z := by
    have h := sub_smul_dslope D s z
    simpa only [hDz, sub_zero, smul_eq_mul] using h.symm
  have he : (fun z => N z / D z) = (fun z => (N z / dslope D s z) / (z-s)) := by
    funext z
    rw [hfac, div_div]
    congr 1
    ring
  rw [he, laurentCoeff_analytic_div_sub hA, dslope_same, hd.deriv]

private theorem quotient_order_of_simple_zero {N D : ℂ → ℂ} {s d : ℂ}
    (hN : AnalyticAt ℂ N s) (hN0 : N s ≠ 0) (hD : AnalyticAt ℂ D s)
    (hDz : D s = 0) (hd : HasDerivAt D d s) (hd0 : d ≠ 0) :
    meromorphicOrderAt (fun z => N z / D z) s = (-1 : ℤ) := by
  have hNo : analyticOrderAt N s = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hN0)
  have hDo : analyticOrderAt D s = 1 :=
    hD.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hDz (by rwa [hd.deriv])
  change meromorphicOrderAt (N / D) s = (-1 : ℤ)
  rw [meromorphicOrderAt_div hN.meromorphicAt hD.meromorphicAt,
    hN.meromorphicOrderAt_eq, hD.meromorphicOrderAt_eq, hNo, hDo]
  norm_num

/-- Pole coordinate in the original Fourier convention, with no period rescaling. -/
def deningerOriginalGreenPole (L : ℝ) (k : ℤ) : ℂ :=
  ((-(2 * Real.pi * ((1/L) * (k : ℝ))) : ℝ) : ℂ) * Complex.I

/-- The denominator of the original positive-translation primitive. -/
def deningerOriginalGreenDenominator (L : ℝ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * (L : ℂ))

/-- Every original harmonic lies on the imaginary Mellin boundary. -/
theorem deningerOriginalGreenPole_re (L : ℝ) (k : ℤ) :
    (deningerOriginalGreenPole L k).re = 0 := by
  simp [deningerOriginalGreenPole]

private theorem exp_originalGreenPole {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    Complex.exp (-deningerOriginalGreenPole L k * (L : ℂ)) = 1 := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  congr 1
  dsimp only [deningerOriginalGreenPole]
  push_cast
  field_simp [hLc]

/-- Each original harmonic is an actual zero of the original denominator. -/
theorem deningerOriginalGreenDenominator_zero {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    deningerOriginalGreenDenominator L (deningerOriginalGreenPole L k) = 0 := by
  rw [deningerOriginalGreenDenominator, exp_originalGreenPole hL, sub_self]

/-- The denominator derivative at every original harmonic is exactly the period. -/
theorem deningerOriginalGreenDenominator_hasDerivAt {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    HasDerivAt (deningerOriginalGreenDenominator L) (L : ℂ) (deningerOriginalGreenPole L k) := by
  have hlin := (hasDerivAt_id (deningerOriginalGreenPole L k)).neg.mul_const (L : ℂ)
  have h := hlin.cexp.const_sub 1
  have hexp : Complex.exp (-(deningerOriginalGreenPole L k * (L : ℂ))) = 1 := by
    simpa only [neg_mul] using exp_originalGreenPole hL k
  convert! h using 1
  simp [hexp]

/-- Exact Laurent residue of an analytic numerator over the original denominator. -/
theorem deningerOriginalGreen_laurentCoeff {N : ℂ → ℂ} {L : ℝ} (hL : L ≠ 0)
    (k : ℤ) (hN : AnalyticAt ℂ N (deningerOriginalGreenPole L k)) :
    laurentCoeff (fun s => N s / deningerOriginalGreenDenominator L s)
      (deningerOriginalGreenPole L k) (-1) = N (deningerOriginalGreenPole L k) / (L : ℂ) := by
  apply quotient_laurentCoeff_of_simple_zero hN
    (by unfold deningerOriginalGreenDenominator; fun_prop)
    (deningerOriginalGreenDenominator_zero hL k)
    (deningerOriginalGreenDenominator_hasDerivAt hL k)
  exact_mod_cast hL

/-- A nonzero numerator forces a simple pole at each original harmonic. -/
theorem deningerOriginalGreen_pole_order {N : ℂ → ℂ} {L : ℝ} (hL : L ≠ 0)
    (k : ℤ) (hN : AnalyticAt ℂ N (deningerOriginalGreenPole L k))
    (hN0 : N (deningerOriginalGreenPole L k) ≠ 0) :
    meromorphicOrderAt (fun s => N s / deningerOriginalGreenDenominator L s)
      (deningerOriginalGreenPole L k) = (-1 : ℤ) := by
  apply quotient_order_of_simple_zero hN hN0
    (by unfold deningerOriginalGreenDenominator; fun_prop)
    (deningerOriginalGreenDenominator_zero hL k)
    (deningerOriginalGreenDenominator_hasDerivAt hL k)
  exact_mod_cast hL

end RHTower
