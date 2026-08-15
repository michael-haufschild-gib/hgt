import GaloisForLFunctions.RHTower.RoutePPrimitiveHankelDepthSquareIntertwiner

/-!
# Route P primitive Hankel dyadic Calderon reconstruction

P-G180 identifies the P-G177 collision feature as the Wold defect `(I-V)` of an undifferenced
Laplace column, where `V f(r)=f(2r)/2`.  Finite dyadic sums telescope exactly back to the base
column.  Their terminal remainder loses a factor `1/8` of squared energy at every step and hence
vanishes in the cofinal limit.

Consequently the doubled-scale source block is strictly contractive but reconstructive: it cannot
by itself manufacture the singular divisor curvature sought after P-G177.  Such singularity must
enter through the source-defined Gamma--Euler continuation/landing.  No Xi divisor is used here.
-/

open Complex Filter Matrix MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Physical half-amplitude dyadic dilation on the radial Hankel carrier. -/
def routePHalfDyadicDilation (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (1 / 2 : ℂ) * f (2 * r)

/-- Undifferenced primitive Laplace column underlying P-G177's cubic feature. -/
def routePPrimitiveCubicHankelBaseFeature
    (pe : Nat.Primes × ℕ) (r : ℝ) : ℂ :=
  finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) * (r : ℂ) *
    Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) * (r : ℂ)))

/-- Arithmetic depth squaring is exactly physical dyadic dilation already on the undifferenced
Laplace column. -/
theorem routePPrimitiveCubicHankelBaseFeature_depthSquare
    (pe : Nat.Primes × ℕ) (r : ℝ) :
    (routePPrimitiveDepthSquareModularGain pe : ℂ) *
        routePPrimitiveCubicHankelBaseFeature (routePPrimitiveDepthSquare pe) r =
      routePHalfDyadicDilation (routePPrimitiveCubicHankelBaseFeature pe) r := by
  have hq := routePPrimitiveDepthSquareModularGain_mul_amplitude pe
  simp only [routePPrimitiveCubicHankelBaseFeature,
    routePHalfDyadicDilation,
    xiGammaEulerPrimitiveLogFrequency_routePPrimitiveDepthSquare]
  have hexp :
      Complex.exp (-(((2 * xiGammaEulerPrimitiveLogFrequency pe : ℝ) : ℂ) *
          (r : ℂ))) =
        Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
          ((2 * r : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    (routePPrimitiveDepthSquareModularGain pe : ℂ) *
          (finiteVonMangoldtDepthOneAmplitude
              (xiGammaEulerValuationNat (routePPrimitiveDepthSquare pe)) *
            (r : ℂ) *
            Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
              ((2 * r : ℝ) : ℂ)))) =
        ((routePPrimitiveDepthSquareModularGain pe : ℂ) *
          finiteVonMangoldtDepthOneAmplitude
            (xiGammaEulerValuationNat (routePPrimitiveDepthSquare pe))) *
          (r : ℂ) *
          Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
            ((2 * r : ℝ) : ℂ))) := by ring
    _ = finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          (r : ℂ) *
          Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
            ((2 * r : ℝ) : ℂ))) := by rw [hq]
    _ = (1 / 2 : ℂ) *
          (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
            ((2 * r : ℝ) : ℂ) *
            Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
              ((2 * r : ℝ) : ℂ)))) := by
      push_cast
      ring

/-- P-G177's collision column is exactly the Wold defect `(I-V)` of its base Laplace column. -/
theorem routePPrimitiveCubicHankelFeature_eq_base_sub_dilation
    (pe : Nat.Primes × ℕ) (r : ℝ) :
    routePPrimitiveCubicHankelFeature pe r =
      routePPrimitiveCubicHankelBaseFeature pe r -
        routePHalfDyadicDilation (routePPrimitiveCubicHankelBaseFeature pe) r := by
  simp only [routePPrimitiveCubicHankelFeature,
    routePPrimitiveCubicHankelBaseFeature, routePHalfDyadicDilation]
  have hexp :
      Complex.exp (-((xiGammaEulerPrimitiveLogFrequency pe : ℂ) *
          ((2 * r : ℝ) : ℂ))) =
        Complex.exp (-(((2 * xiGammaEulerPrimitiveLogFrequency pe : ℝ) : ℂ) *
          (r : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

/-- Recursive dyadic iterate, kept explicit so the finite Calderon telescope is definitionally
transparent. -/
def routePHalfDyadicIterate : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | k + 1, f => routePHalfDyadicDilation (routePHalfDyadicIterate k f)

theorem routePHalfDyadicIterate_sub
    (k : ℕ) (f h : ℝ → ℂ) (r : ℝ) :
    routePHalfDyadicIterate k (fun x => f x - h x) r =
      routePHalfDyadicIterate k f r - routePHalfDyadicIterate k h r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
      simp only [routePHalfDyadicIterate, routePHalfDyadicDilation]
      rw [ih]
      ring

theorem routePHalfDyadicIterate_dilation
    (k : ℕ) (f : ℝ → ℂ) (r : ℝ) :
    routePHalfDyadicIterate k (routePHalfDyadicDilation f) r =
      routePHalfDyadicIterate (k + 1) f r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
      simp only [routePHalfDyadicIterate, routePHalfDyadicDilation]
      rw [ih]
      rfl

/-- Exact finite Calderon reconstruction for every radial function. -/
theorem sum_range_routePHalfDyadicIterate_defect
    (N : ℕ) (f : ℝ → ℂ) (r : ℝ) :
    ∑ k ∈ Finset.range N,
        routePHalfDyadicIterate k
          (fun x => f x - routePHalfDyadicDilation f x) r =
      f r - routePHalfDyadicIterate N f r := by
  induction N with
  | zero => simp [routePHalfDyadicIterate]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [routePHalfDyadicIterate_sub,
        routePHalfDyadicIterate_dilation]
      ring

/-- The P-G177 collision column reconstructs its base Laplace column by an exact finite dyadic
telescope, with one explicit terminal remainder. -/
theorem sum_range_routePPrimitiveCubicHankelFeature_reconstruction
    (N : ℕ) (pe : Nat.Primes × ℕ) (r : ℝ) :
    ∑ k ∈ Finset.range N,
        routePHalfDyadicIterate k
          (routePPrimitiveCubicHankelFeature pe) r =
      routePPrimitiveCubicHankelBaseFeature pe r -
        routePHalfDyadicIterate N
          (routePPrimitiveCubicHankelBaseFeature pe) r := by
  have hfun : routePPrimitiveCubicHankelFeature pe =
      fun x => routePPrimitiveCubicHankelBaseFeature pe x -
        routePHalfDyadicDilation (routePPrimitiveCubicHankelBaseFeature pe) x := by
    funext x
    exact routePPrimitiveCubicHankelFeature_eq_base_sub_dilation pe x
  rw [hfun]
  exact sum_range_routePHalfDyadicIterate_defect N
    (routePPrimitiveCubicHankelBaseFeature pe) r

/-- Every dyadic iterate loses exactly one further factor `1/8` of physical squared energy. -/
theorem integral_normSq_routePHalfDyadicIterate
    (N : ℕ) (f : ℝ → ℂ) :
    (∫ r : ℝ in Set.Ioi 0, Complex.normSq (routePHalfDyadicIterate N f r)) =
      (1 / 8 : ℝ) ^ N *
        ∫ r : ℝ in Set.Ioi 0, Complex.normSq (f r) := by
  induction N with
  | zero => simp [routePHalfDyadicIterate]
  | succ N ih =>
      simp only [routePHalfDyadicIterate, routePHalfDyadicDilation]
      rw [integral_normSq_half_dyadic_dilation, ih, pow_succ]
      ring

/-- The terminal remainder in the Calderon reconstruction vanishes in physical squared energy. -/
theorem tendsto_integral_normSq_routePHalfDyadicIterate
    (f : ℝ → ℂ) :
    Tendsto
      (fun N : ℕ =>
        ∫ r : ℝ in Set.Ioi 0,
          Complex.normSq (routePHalfDyadicIterate N f r))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 8 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul := hpow.mul_const
    (∫ r : ℝ in Set.Ioi 0, Complex.normSq (f r))
  simpa only [integral_normSq_routePHalfDyadicIterate, zero_mul] using hmul

end

end RHTower
