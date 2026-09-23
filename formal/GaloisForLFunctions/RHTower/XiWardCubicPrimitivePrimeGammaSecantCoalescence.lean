import GaloisForLFunctions.RHTower.XiWardCubicPrimeGammaMixedSecantGraph

/-!
# Primitive prime--Gamma secant coalescence (W-H204)

W-H203 constructs the finite source-only mixed graph carrier.  This module specializes one
secant leg to the actual primitive Burnol/Deninger node of P-G200 and opens it by a positive radial
increment `c`.

At every strict-right Xi copy, the negative upper source secant is exactly

`1 / ((mu + lambda + c) (mu + lambda))`.

As `c -> 0+` this converges to `(mu+lambda)⁻²`, the generated reporter identified by P-G200.
After multiplication by the literal resolved von Mangoldt amplitude, the coalescent limit is
exactly the Laplace report of the actual primitive Burnol window.  Thus neither differentiation
nor a target-fitted coefficient is required: the squared graph column is the boundary value of a
finite strict-Euler prime--Gamma cup with coefficients intact.

The remaining global obstruction is now only the signed trace shorting of the matrix-complete
mixed cup, not construction of its finite source carrier or its coefficient-faithful coalescent.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Positive radial shift of an actual primitive node inside Deninger's strict lower source
sector. -/
def xiWardCubicPrimitiveDeningerLowerShift
    (pe : Nat.Primes × ℕ) (kappa c : ℝ) (hc : 0 ≤ c) :
    DeningerPrimeGammaLowerPoint :=
  ⟨(routePPrimitiveBurnolCenteredMode pe (-kappa) + (c : ℂ)) * (-I), by
    have hfreq := half_lt_xiGammaEulerPrimitiveLogFrequency pe
    rw [show (1 / 2 +
        (routePPrimitiveBurnolCenteredMode pe (-kappa) + (c : ℂ)) *
          (-I) * I).re =
        1 / 2 + xiGammaEulerPrimitiveLogFrequency pe + c by
      simp [routePPrimitiveBurnolCenteredMode, Complex.mul_re]
      ring]
    linarith⟩

/-- Canonical reflected upper mate of the shifted primitive source node. -/
def xiWardCubicPrimitiveDeningerUpperShift
    (pe : Nat.Primes × ℕ) (kappa c : ℝ) (hc : 0 ≤ c) :
    DeningerPrimeGammaUpperPoint :=
  deningerPrimeGammaPointConjEquiv
    (xiWardCubicPrimitiveDeningerLowerShift pe kappa c hc)

theorem xiWardCubicPrimitiveDeningerUpperShift_coe
    (pe : Nat.Primes × ℕ) (kappa c : ℝ) (hc : 0 ≤ c) :
    (xiWardCubicPrimitiveDeningerUpperShift pe kappa c hc : ℂ) =
      (routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ)) * I := by
  apply Complex.ext
  · simp [xiWardCubicPrimitiveDeningerUpperShift,
      deningerPrimeGammaPointConjEquiv,
      xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode, Complex.mul_re]
  · simp [xiWardCubicPrimitiveDeningerUpperShift,
      deningerPrimeGammaPointConjEquiv,
      xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode, Complex.mul_im]

/-- Shifted P-G200 Cauchy evaluation formula. -/
theorem xiWeilCauchyTest_xiWardCubicPrimitiveDeningerUpperShift
    (pe : Nat.Primes × ℕ) (kappa c : ℝ) (hc : 0 ≤ c)
    (q : XiRightZeroCopy) :
    xiWeilCauchyTest
        (xiWardCubicPrimitiveDeningerUpperShift pe kappa c hc : ℂ)
        (xiSpectralPoint q.1) =
      I * (xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ))⁻¹ := by
  have hspectral : xiSpectralPoint q.1 = -I * xiRightCenteredZero q := by
    rw [xiRightCenteredZero]
    ring_nf
    norm_num [I_mul_I]
  have hsum : xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, routePPrimitiveBurnolCenteredMode_re,
      Complex.ofReal_re, Complex.zero_re] at hre
    linarith [xiRightCenteredZero_re_pos q,
      xiGammaEulerPrimitiveLogFrequency_pos pe]
  rw [xiWeilCauchyTest, hspectral,
    xiWardCubicPrimitiveDeningerUpperShift_coe]
  rw [show -I * xiRightCenteredZero q -
      (routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ)) * I =
      -I * (xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ)) by ring]
  rw [mul_inv]
  simp only [inv_neg, Complex.inv_I]
  ring

/-- Finite primitive generated reporter before source-node coalescence. -/
def xiWardCubicPrimitiveGeneratedSecant
    (pe : Nat.Primes × ℕ) (kappa c : ℝ) (q : XiRightZeroCopy) : ℂ :=
  (xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ))⁻¹ *
    (xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa)⁻¹

/-- **W-H204 finite coefficient-free incidence.**  The generated endpoint product is exactly the
negative secant of two strict-Euler Deninger source evaluations. -/
theorem xiWardCubicPrimitiveGeneratedSecant_eq_neg_sourceSecant
    (pe : Nat.Primes × ℕ) (kappa : ℝ) {c : ℝ} (hc : 0 < c)
    (q : XiRightZeroCopy) :
    xiWardCubicPrimitiveGeneratedSecant pe kappa c q =
      -xiWardCubicPrimeGammaUpperSecantTest
        (xiWardCubicPrimitiveDeningerUpperShift pe kappa 0 (le_refl 0))
        (xiWardCubicPrimitiveDeningerUpperShift pe kappa c hc.le)
        (xiSpectralPoint q.1) := by
  rw [xiWardCubicPrimeGammaUpperSecantTest,
    xiWeilCauchyTest_xiWardCubicPrimitiveDeningerUpperShift,
    xiWeilCauchyTest_xiWardCubicPrimitiveDeningerUpperShift,
    xiWardCubicPrimitiveDeningerUpperShift_coe,
    xiWardCubicPrimitiveDeningerUpperShift_coe,
    xiWardCubicPrimitiveGeneratedSecant]
  have hX : xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, routePPrimitiveBurnolCenteredMode_re,
      Complex.zero_re] at hre
    linarith [xiRightCenteredZero_re_pos q,
      xiGammaEulerPrimitiveLogFrequency_pos pe]
  have hXc : xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa + (c : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, routePPrimitiveBurnolCenteredMode_re,
      Complex.ofReal_re, Complex.zero_re] at hre
    linarith [xiRightCenteredZero_re_pos q,
      xiGammaEulerPrimitiveLogFrequency_pos pe]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  field_simp [hX, hXc, hcC]
  norm_num

/-- The finite strict-Euler secant coalesces to P-G200's squared generated reporter. -/
theorem tendsto_xiWardCubicPrimitiveGeneratedSecant
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    Tendsto (fun c : ℝ =>
        xiWardCubicPrimitiveGeneratedSecant pe kappa c q)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa)⁻¹ ^ (2 : ℕ))) := by
  let X : ℂ := xiRightCenteredZero q +
    routePPrimitiveBurnolCenteredMode pe kappa
  have hX : X ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [X] at hre
    simp only [Complex.add_re, routePPrimitiveBurnolCenteredMode_re,
      Complex.zero_re] at hre
    linarith [xiRightCenteredZero_re_pos q,
      xiGammaEulerPrimitiveLogFrequency_pos pe]
  have hadd : ContinuousAt (fun c : ℝ => X + (c : ℂ)) 0 := by fun_prop
  have hcont : ContinuousAt
      (fun c : ℝ => (X + (c : ℂ))⁻¹ * X⁻¹) 0 :=
    (hadd.inv₀ (by simpa using hX)).mul continuousAt_const
  have ht : Tendsto (fun c : ℝ => (X + (c : ℂ))⁻¹ * X⁻¹)
      (nhdsWithin 0 (Ioi 0)) (nhds ((X + (0 : ℂ))⁻¹ * X⁻¹)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  simpa [xiWardCubicPrimitiveGeneratedSecant, X, pow_two] using ht

/-- **W-H204 coefficient-faithful coalescence.**  Restoring the actual resolved von Mangoldt
amplitude makes the secant limit exactly the primitive Burnol-window Laplace report. -/
theorem tendsto_xiWardCubicPrimitiveGeneratedSecant_mul_amplitude
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    Tendsto (fun c : ℝ =>
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          xiWardCubicPrimitiveGeneratedSecant pe kappa c q)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ L : ℝ in Ioi 0,
        Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
          routePPrimitiveBurnolWindowFeature pe kappa L)) := by
  have h := (tendsto_xiWardCubicPrimitiveGeneratedSecant pe kappa q).const_mul
    (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
  convert h using 1
  rw [integral_routePPrimitiveBurnolWindowFeature_eq_deningerSquaredEvaluation,
    neg_sq_xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint]

end

end RHTower
