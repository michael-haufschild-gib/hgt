import GaloisForLFunctions.RHTower.XiShiftedHardEdgeFiniteHankelWitness
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.HTGeometry.FiniteRegularityWienerFamily

/-!
# Exact polynomial--Gaussian carrier for the Route-U compact witness

The negative Xi heat trace is built from the *amplitude*

`P(z²) exp (-t z² / 2)`,

whose square is the existing polynomial--Gaussian heat summand.  This module realizes that
amplitude as the positive Fourier transform of an actual real-even Schwartz function.  Thus the
Paley--Wiener cutoff used by Route U starts from the correct unsquared carrier, rather than from the
already-squared density.
-/

open scoped FourierTransform SchwartzMap
open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Unsquared entire polynomial--Gaussian profile whose square is the Xi heat summand. -/
def routeUXiPolynomialGaussianProfile
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (z : ℂ) : ℂ :=
  evalRealPolynomial P (z ^ 2) *
    Complex.exp (-(((t : ℝ) / 2 : ℝ) : ℂ) * z ^ 2)

/-- Squaring the carrier gives exactly the already formalized polynomial--Gaussian Xi term. -/
theorem routeUXiPolynomialGaussianProfile_sq_xiSpectralPoint
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (q : XiZeroCopy) :
    routeUXiPolynomialGaussianProfile P t (xiSpectralPoint q) ^ 2 =
      xiPolynomialGaussianHeatTerm P (t : ℝ) q := by
  rw [routeUXiPolynomialGaussianProfile, xiPolynomialGaussianHeatTerm,
    xiGaussianHeatTerm, mul_pow]
  congr 1
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Gaussian dilation placing the heat profile in mathlib's self-dual `exp (-πx²)` scale. -/
def routeUXiHeatProfileScale (t : {τ : ℝ // 0 < τ}) : ℝ :=
  Real.sqrt (2 * Real.pi * (t : ℝ))

theorem routeUXiHeatProfileScale_pos (t : {τ : ℝ // 0 < τ}) :
    0 < routeUXiHeatProfileScale t := by
  rw [routeUXiHeatProfileScale]
  exact Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos) t.property)

/-- Polynomial factor before the heat-profile dilation. -/
def routeUXiHeatProfilePolynomial
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : Polynomial ℝ :=
  (evenSquarePolynomial P).comp
    (Polynomial.C ((2 * Real.pi) / routeUXiHeatProfileScale t) * Polynomial.X)

/-- The rescaled real-axis heat profile as a genuine Schwartz function.  Its value at `x` is the
entire carrier evaluated at angular frequency `2πx`. -/
def routeUXiHeatProfileSchwartz
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : SchwartzMap ℝ ℂ :=
  schwartzDilate (polyGaussSchwartz (routeUXiHeatProfilePolynomial P t))
    (routeUXiHeatProfileScale_pos t).ne'

theorem routeUXiHeatProfileSchwartz_apply
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUXiHeatProfileSchwartz P t x =
      routeUXiPolynomialGaussianProfile P t ((2 * Real.pi * x : ℝ) : ℂ) := by
  have hc : 0 < routeUXiHeatProfileScale t := routeUXiHeatProfileScale_pos t
  have hcsq : routeUXiHeatProfileScale t ^ 2 = 2 * Real.pi * (t : ℝ) := by
    rw [routeUXiHeatProfileScale, Real.sq_sqrt]
    exact (mul_pos (mul_pos (by norm_num) Real.pi_pos) t.property).le
  rw [routeUXiHeatProfileSchwartz, schwartzDilate_apply, polyGaussSchwartz_apply,
    routeUXiHeatProfilePolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, evenSquarePolynomial, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, gaussReal,
    routeUXiPolynomialGaussianProfile]
  have hlin : (2 * Real.pi / routeUXiHeatProfileScale t) *
      (routeUXiHeatProfileScale t * x) = 2 * Real.pi * x := by
    field_simp [hc.ne']
  rw [hlin]
  have hz : ((((2 * Real.pi * x : ℝ) : ℂ)) ^ 2) =
      ((((2 * Real.pi * x) ^ 2 : ℝ) : ℂ)) := by exact_mod_cast rfl
  rw [hz, evalRealPolynomial_ofReal]
  push_cast
  congr 1
  congr 1
  have hcsqC : ((routeUXiHeatProfileScale t : ℂ) ^ 2) =
      (2 * Real.pi : ℂ) * (t : ℝ) := by exact_mod_cast hcsq
  rw [mul_pow, hcsqC]
  ring

theorem routeUXiHeatProfileSchwartz_even
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUXiHeatProfileSchwartz P t (-x) = routeUXiHeatProfileSchwartz P t x := by
  rw [routeUXiHeatProfileSchwartz_apply, routeUXiHeatProfileSchwartz_apply]
  unfold routeUXiPolynomialGaussianProfile
  have hneg : (((2 * Real.pi * -x : ℝ) : ℂ)) =
      -(((2 * Real.pi * x : ℝ) : ℂ)) := by push_cast; ring
  rw [hneg, neg_sq]

theorem routeUXiHeatProfileSchwartz_real
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    (starRingEnd ℂ) (routeUXiHeatProfileSchwartz P t x) =
      routeUXiHeatProfileSchwartz P t x := by
  rw [routeUXiHeatProfileSchwartz_apply]
  unfold routeUXiPolynomialGaussianProfile
  rw [map_mul, ← evalRealPolynomial_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal]

/-- Complex physical amplitude obtained by Fourier-inverting the rescaled spectral profile. -/
def routeUXiHeatPhysicalComplex
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : SchwartzMap ℝ ℂ :=
  FourierTransform.fourier (routeUXiHeatProfileSchwartz P t)

theorem routeUXiHeatPhysicalComplex_even
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUXiHeatPhysicalComplex P t (-x) = routeUXiHeatPhysicalComplex P t x := by
  simpa only [routeUXiHeatPhysicalComplex, SchwartzMap.fourier_coe] using
    fourier_even_of_even (routeUXiHeatProfileSchwartz_even P t) x

theorem routeUXiHeatPhysicalComplex_real
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    (starRingEnd ℂ) (routeUXiHeatPhysicalComplex P t x) =
      routeUXiHeatPhysicalComplex P t x := by
  have hreality := fourier_neg_eq_conj (routeUXiHeatProfileSchwartz_real P t) x
  have heven := routeUXiHeatPhysicalComplex_even P t x
  have hreality' :
      routeUXiHeatPhysicalComplex P t (-x) =
        (starRingEnd ℂ) (routeUXiHeatPhysicalComplex P t x) := by
    simpa only [routeUXiHeatPhysicalComplex, SchwartzMap.fourier_coe] using hreality
  exact hreality'.symm.trans heven

/-- Real physical amplitude consumed by the exact finite-Hankel Route-U lift. -/
def routeUXiHeatPhysicalReal
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : SchwartzMap ℝ ℝ :=
  (routeUXiHeatPhysicalComplex P t).postcompCLM Complex.reCLM

theorem routeUXiHeatPhysicalReal_even
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUXiHeatPhysicalReal P t (-x) = routeUXiHeatPhysicalReal P t x := by
  change (routeUXiHeatPhysicalComplex P t (-x)).re =
    (routeUXiHeatPhysicalComplex P t x).re
  rw [routeUXiHeatPhysicalComplex_even]

theorem routeURealEvenAmplitude_heatPhysical_eq
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    routeURealEvenAmplitude (routeUXiHeatPhysicalReal P t) =
      routeUXiHeatPhysicalComplex P t := by
  apply SchwartzMap.ext
  intro x
  rw [routeURealEvenAmplitude, schwartzEvenPart_apply]
  change (2 : ℂ)⁻¹ *
      (((routeUXiHeatPhysicalReal P t x : ℝ) : ℂ) +
        ((routeUXiHeatPhysicalReal P t (-x) : ℝ) : ℂ)) = _
  rw [routeUXiHeatPhysicalReal_even]
  change (2 : ℂ)⁻¹ *
      (((routeUXiHeatPhysicalComplex P t x).re : ℂ) +
        ((routeUXiHeatPhysicalComplex P t x).re : ℂ)) = _
  have hreal : (((routeUXiHeatPhysicalComplex P t x).re : ℝ) : ℂ) =
      routeUXiHeatPhysicalComplex P t x :=
    Complex.conj_eq_iff_re.mp (routeUXiHeatPhysicalComplex_real P t x)
  rw [hreal]
  ring

/-- **Exact real-axis carrier identity.**  The positive angular-frequency Fourier transform of the
real-even physical amplitude is the unsquared polynomial--Gaussian heat profile. -/
theorem routeUPositiveFourierExtension_heatPhysical_eq
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUPositiveFourierExtension
        (routeURealEvenAmplitude (routeUXiHeatPhysicalReal P t)) x =
      routeUXiPolynomialGaussianProfile P t (x : ℂ) := by
  rw [routeURealEvenAmplitude_heatPhysical_eq, routeUPositiveFourierExtension,
    routeUXiHeatPhysicalComplex]
  let h : SchwartzMap ℝ ℂ := routeUXiHeatProfileSchwartz P t
  change FourierTransform.fourier (FourierTransform.fourier h)
      (-x / (2 * Real.pi)) = _
  have hinv : FourierTransform.fourierInv (FourierTransform.fourier h) = h :=
    FourierTransform.fourierInv_fourier_eq h
  rw [SchwartzMap.fourierInv_apply_eq] at hinv
  change schwartzNeg (FourierTransform.fourier (FourierTransform.fourier h)) = h at hinv
  have hdouble : FourierTransform.fourier (FourierTransform.fourier h) = schwartzNeg h := by
    apply SchwartzMap.ext
    intro y
    have hy := congrArg (fun F : SchwartzMap ℝ ℂ => F (-y)) hinv
    simpa [schwartzNeg_apply] using hy
  rw [hdouble, schwartzNeg_apply, routeUXiHeatProfileSchwartz_apply]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  congr 1
  push_cast
  field_simp

end RHTower
