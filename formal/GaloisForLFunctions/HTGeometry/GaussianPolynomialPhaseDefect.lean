import GaloisForLFunctions.HTGeometry.GaussianPolynomialCoordinateEnergy
import GaloisForLFunctions.HTGeometry.ComplexGaussianTranslationDefect
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Relative energy error for the entire vertically translated polynomial Gaussian

Vertical translation changes both the polynomial and the Gaussian. The latter
contributes a positive scalar and a unit-modulus modulation. Keeping all three
defect terms gives a coefficient-uniform relative error in continuous L².
-/

open scoped Real SchwartzMap
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions
open HTGeometry

/-- Modulation preserves the full L² norm, including interference among summands. -/
theorem norm_modulationMul_eq (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖modulationMul a f‖ = ‖f‖ := by
  have hpoint : ∀ᵐ x ∂(volume : Measure ℝ), ‖modulationMul a f x‖ = ‖f x‖ := by
    filter_upwards [coeFn_modulationMul a f] with x hx
    rw [hx, norm_mul, norm_modulationSymbol, one_mul]
  apply le_antisymm
  · exact Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ hx => hx.le)
  · exact Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ hx => hx.ge)

/-- The modulation error vanishes linearly in its frequency. -/
theorem norm_modulationSymbol_sub_one_le (a x : ℝ) :
    ‖modulationSymbol a x - 1‖ ≤ 2 * π * |a| * |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * (a * x))
  rw [mul_comm Complex.I] at h
  simpa only [modulationSymbol, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), mul_assoc] using h

/-- The coordinate-weighted Schwartz norm controls the complete modulation defect. -/
theorem norm_modulationMul_sub_toLp_le (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖modulationMul a (f.toLp 2 (volume : Measure ℝ)) -
        f.toLp 2 (volume : Measure ℝ)‖ ≤
      (2 * π * |a|) * ‖(mulXCLM f).toLp 2 (volume : Measure ℝ)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (modulationMul a (f.toLp 2 (volume : Measure ℝ)))
      (f.toLp 2 (volume : Measure ℝ)),
    coeFn_modulationMul a (f.toLp 2 (volume : Measure ℝ)),
    SchwartzMap.coeFn_toLp f 2 (volume : Measure ℝ),
    SchwartzMap.coeFn_toLp (mulXCLM f) 2 (volume : Measure ℝ)] with x hs hm hf hx
  simp only [hs, Pi.sub_apply, hm, hf, hx, mulXCLM_apply]
  rw [show modulationSymbol a x * f x - f x = (modulationSymbol a x - 1) * f x by ring,
    norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    _ ≤ (2 * π * |a| * |x|) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (norm_modulationSymbol_sub_one_le a x) (norm_nonneg _)
    _ = _ := by ring

/-- The Gaussian phase error is uniform in every polynomial coefficient. -/
theorem norm_modulationMul_polyGauss_sub_le (P : Polynomial ℝ) (a : ℝ) :
    ‖modulationMul a ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)) -
        (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      (|a| * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  refine (norm_modulationMul_sub_toLp_le a _).trans ?_
  have h := mul_le_mul_of_nonneg_left (gaussianPolynomialCoordinateNorm_le P) (abs_nonneg a)
  convert h using 1 <;> ring

/-- The entire polynomial Gaussian after an imaginary displacement. -/
def verticalPolynomialGaussianLp (P : Polynomial ℝ) (δ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.exp (π * δ ^ 2) : ℂ) • modulationMul (-δ)
    ((complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I)).toLp 2 (volume : Measure ℝ))

/-- The L² construction represents the complete complex Gaussian, with its phase intact. -/
theorem coeFn_verticalPolynomialGaussianLp (P : Polynomial ℝ) (δ : ℝ) :
    (verticalPolynomialGaussianLp P δ : ℝ → ℂ) =ᵐ[volume] fun x =>
      P.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + (δ : ℂ) * Complex.I) *
        Complex.exp (-(π : ℂ) * ((x : ℂ) + (δ : ℂ) * Complex.I) ^ 2) := by
  have hexp (x : ℝ) :
      (Real.exp (π * δ ^ 2) : ℂ) * modulationSymbol (-δ) x * (gaussReal x : ℂ) =
        Complex.exp (-(π : ℂ) * ((x : ℂ) + (δ : ℂ) * Complex.I) ^ 2) := by
    rw [modulationSymbol, gaussReal, Complex.ofReal_exp, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold verticalPolynomialGaussianLp
  filter_upwards [Lp.coeFn_smul (Real.exp (π * δ ^ 2) : ℂ)
      (modulationMul (-δ) ((complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I)).toLp 2
        (volume : Measure ℝ))),
    coeFn_modulationMul (-δ) ((complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I)).toLp 2
      (volume : Measure ℝ)),
    SchwartzMap.coeFn_toLp (complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I)) 2
      (volume : Measure ℝ)] with x hs hm ht
  rw [hs, Pi.smul_apply, smul_eq_mul, hm, ht, complexTranslatedPolyGauss_apply]
  rw [← hexp]
  ring

/-- A relative defect budget retaining polynomial translation, phase, and scalar growth. -/
def verticalPolynomialGaussianDefect (d : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (π * δ ^ 2) *
    (Real.exp (|δ| * Real.sqrt (4 * π * d)) - 1 +
      |δ| * Real.sqrt (4 * π * ((d : ℝ) + 1))) +
    (Real.exp (π * δ ^ 2) - 1)

/-- Every vertical translation has an independent coefficient-uniform relative error. -/
theorem norm_verticalPolynomialGaussianLp_sub_le (P : Polynomial ℝ) (δ : ℝ) :
    ‖verticalPolynomialGaussianLp P δ -
        (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      verticalPolynomialGaussianDefect P.natDegree δ *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let f := (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)
  let T := (complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I)).toLp 2 (volume : Measure ℝ)
  let c : ℝ := Real.exp (π * δ ^ 2)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hc1 : 0 ≤ c - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hT := norm_complexTranslatedPolyGauss_sub_le P ((δ : ℂ) * Complex.I)
  rw [toLp_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one] at hT
  have hM := norm_modulationMul_polyGauss_sub_le P (-δ)
  rw [abs_neg] at hM
  have hid : verticalPolynomialGaussianLp P δ - f =
      (c : ℂ) • modulationMul (-δ) (T - f) +
        (c : ℂ) • (modulationMul (-δ) f - f) + ((c : ℂ) - 1) • f := by
    simp only [verticalPolynomialGaussianLp, map_sub, f, T, c]
    module
  have hscalar : ‖(c : ℂ)‖ = c := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hscalar' : ‖(c : ℂ) - 1‖ = c - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc1]
  calc
    _ ≤ ‖(c : ℂ) • modulationMul (-δ) (T - f)‖ +
        ‖(c : ℂ) • (modulationMul (-δ) f - f)‖ + ‖((c : ℂ) - 1) • f‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = c * ‖T - f‖ + c * ‖modulationMul (-δ) f - f‖ + (c - 1) * ‖f‖ := by
      rw [norm_smul, norm_smul, norm_smul, hscalar, hscalar', norm_modulationMul_eq]
    _ ≤ c * ((Real.exp (|δ| * Real.sqrt (4 * π * P.natDegree)) - 1) * ‖f‖) +
        c * ((|δ| * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) * ‖f‖) +
        (c - 1) * ‖f‖ := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT hc)
        (mul_le_mul_of_nonneg_left hM hc)) le_rfl
    _ = _ := by unfold verticalPolynomialGaussianDefect; dsimp [c, f]; ring

/-- An unconditional lower energy margin for the full translated Gaussian amplitude. -/
theorem norm_verticalPolynomialGaussianLp_lower_margin (P : Polynomial ℝ) (δ : ℝ) :
    (1 - verticalPolynomialGaussianDefect P.natDegree δ) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      ‖verticalPolynomialGaussianLp P δ‖ := by
  have h := norm_verticalPolynomialGaussianLp_sub_le P δ
  have ht := norm_le_norm_add_norm_sub (verticalPolynomialGaussianLp P δ)
    ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ))
  nlinarith only [h, ht]

end GaloisForLFunctions
