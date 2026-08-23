import GaloisForLFunctions.RHTower.FiniteEulerGammaConnection
import GaloisForLFunctions.RHTower.HeatAperturePrimeSeamReflection

/-!
# Differential identities for the finite Euler--Gamma weld

This module closes the value-level and connection-level reflection package for one finite Euler
factor. It identifies its logarithmic source with both the canonical imaginary-slope digamma
anomaly and the hyperbolic cotangent form, then logarithmically differentiates the FE-symmetric
quartet. The trigamma curvature identity is reused from `HeatAperturePrimeSeamReflection`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- Complex hyperbolic cotangent, kept explicit because mathlib exposes `sinh` and `cosh`
but no bundled complex `coth`. -/
def complexCoth (z : ℂ) : ℂ := Complex.cosh z / Complex.sinh z

/-- Away from zeros of the finite Euler factor, its Gamma argument is not integral. -/
theorem primeEulerGammaCoordinate_ne_int_of_localFactor_ne_zero
    (p : Nat.Primes) (s : ℂ) (hs : finiteEulerLocalFactor p s ≠ 0) :
    ∀ m : ℤ, primeEulerGammaCoordinate p s ≠ (m : ℂ) := by
  intro m hm
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have harg : -s * (Real.log p : ℂ) = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold primeEulerGammaCoordinate at hm
    field_simp [hpi] at hm
    calc
      -s * (Real.log p : ℂ) = Complex.I *
          (Complex.I * (Real.log p : ℂ) * s) := by
            symm
            calc
              Complex.I * (Complex.I * (Real.log p : ℂ) * s) =
                  (Complex.I * Complex.I) * ((Real.log p : ℂ) * s) := by ring
              _ = -s * (Real.log p : ℂ) := by rw [Complex.I_mul_I]; ring
      _ = Complex.I * (2 * (Real.pi : ℂ) * (m : ℂ)) := by rw [hm]
      _ = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  apply hs
  unfold finiteEulerLocalFactor
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  ring

/-- The finite Euler connection is exactly its imaginary-slope digamma-reflection anomaly. -/
theorem primeLogSource_eq_digammaReflection
    (p : Nat.Primes) (s : ℂ) (hs : finiteEulerLocalFactor p s ≠ 0) :
    _root_.RHTower.primeLogSource p s =
      -(Real.log p : ℂ) / 2 + finiteEulerGammaSlope p *
        (Complex.digamma (1 - primeEulerGammaCoordinate p s) -
          Complex.digamma (primeEulerGammaCoordinate p s)) := by
  let L : ℂ := (Real.log p : ℂ)
  let x : ℂ := L * s
  let u : ℂ := primeEulerGammaCoordinate p s
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hu : (Real.pi : ℂ) * u = (x / 2) * Complex.I := by
    dsimp [u, x, L, primeEulerGammaCoordinate]
    field_simp [hpi]
  have hsin : Complex.sin ((Real.pi : ℂ) * u) =
      Complex.I / 2 * (Complex.exp (x / 2) - Complex.exp (-(x / 2))) := by
    rw [hu, Complex.sin_mul_I]
    unfold Complex.sinh
    ring
  have hcos : Complex.cos ((Real.pi : ℂ) * u) =
      (Complex.exp (x / 2) + Complex.exp (-(x / 2))) / 2 := by
    rw [hu, Complex.cos_mul_I]
    unfold Complex.cosh
    ring
  have hfactor : finiteEulerLocalFactor p s = 1 - Complex.exp (-x) := by
    unfold finiteEulerLocalFactor
    congr 2
    dsimp [x, L]
    ring
  have hdiff : Complex.exp (x / 2) - Complex.exp (-(x / 2)) ≠ 0 := by
    intro hzero
    apply hs
    rw [hfactor]
    have hprod : Complex.exp (-(x / 2)) * Complex.exp (x / 2) = 1 := by
      rw [← Complex.exp_add, show -(x / 2) + x / 2 = 0 by ring, Complex.exp_zero]
    have hsq : Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) =
        Complex.exp (-x) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      1 - Complex.exp (-x) =
          Complex.exp (-(x / 2)) * Complex.exp (x / 2) -
            Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) := by rw [hprod, hsq]
      _ = Complex.exp (-(x / 2)) *
          (Complex.exp (x / 2) - Complex.exp (-(x / 2))) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hdig := _root_.RHTower.digamma_reflection
    (primeEulerGammaCoordinate_ne_int_of_localFactor_ne_zero p s hs)
  change Complex.digamma u - Complex.digamma (1 - u) = _ at hdig
  have hpow : ((p : ℂ) ^ (-s)) = Complex.exp (-x) := by
    rw [_root_.RHTower.primePow_eq_exp p.property.two_le]
    congr 1
    dsimp [x, L]
    ring
  rw [_root_.RHTower.primeLogSource, hpow]
  change L * Complex.exp (-x) / (1 - Complex.exp (-x)) =
    -L / 2 + finiteEulerGammaSlope p *
      (Complex.digamma (1 - u) - Complex.digamma u)
  rw [show finiteEulerGammaSlope p = Complex.I * L / (2 * (Real.pi : ℂ)) by rfl]
  rw [show Complex.digamma (1 - u) - Complex.digamma u =
      (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * u) /
        Complex.sin ((Real.pi : ℂ) * u) by linear_combination -hdig]
  rw [hsin, hcos]
  have hfactorNe : 1 - Complex.exp (-x) ≠ 0 := by
    intro hzero
    apply hs
    rw [hfactor, hzero]
  field_simp [hpi, hdiff, hfactorNe]
  have hprod : Complex.exp (-(x / 2)) * Complex.exp (x / 2) = 1 := by
    rw [← Complex.exp_add, show -(x / 2) + x / 2 = 0 by ring, Complex.exp_zero]
  have hsq : Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) =
      Complex.exp (-x) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← hsq]
  linear_combination 2 * L * Complex.exp (-(x / 2)) * hprod

/-- Equivalent hyperbolic form of the finite Euler connection. -/
theorem primeLogSource_eq_complexCoth
    (p : Nat.Primes) (s : ℂ) (hs : finiteEulerLocalFactor p s ≠ 0) :
    _root_.RHTower.primeLogSource p s =
      (Real.log p : ℂ) / 2 *
        (complexCoth ((Real.log p : ℂ) * s / 2) - 1) := by
  let L : ℂ := (Real.log p : ℂ)
  let x : ℂ := L * s
  have hfactor : finiteEulerLocalFactor p s = 1 - Complex.exp (-x) := by
    unfold finiteEulerLocalFactor
    congr 2
    dsimp [x, L]
    ring
  have hfactorNe : 1 - Complex.exp (-x) ≠ 0 := by
    intro hzero
    apply hs
    rw [hfactor, hzero]
  have hprod : Complex.exp (-(x / 2)) * Complex.exp (x / 2) = 1 := by
    rw [← Complex.exp_add, show -(x / 2) + x / 2 = 0 by ring, Complex.exp_zero]
  have hsq : Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) =
      Complex.exp (-x) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsplit : 1 - Complex.exp (-x) = Complex.exp (-(x / 2)) *
      (Complex.exp (x / 2) - Complex.exp (-(x / 2))) := by
    calc
      1 - Complex.exp (-x) =
          Complex.exp (-(x / 2)) * Complex.exp (x / 2) -
            Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) := by rw [hprod, hsq]
      _ = _ := by ring
  have hdiff : Complex.exp (x / 2) - Complex.exp (-(x / 2)) ≠ 0 := by
    intro hzero
    apply hfactorNe
    rw [hsplit, hzero, mul_zero]
  have hpow : ((p : ℂ) ^ (-s)) = Complex.exp (-x) := by
    rw [_root_.RHTower.primePow_eq_exp p.property.two_le]
    congr 1
    dsimp [x, L]
    ring
  rw [_root_.RHTower.primeLogSource, hpow]
  change L * Complex.exp (-x) / (1 - Complex.exp (-x)) =
    L / 2 * (complexCoth (x / 2) - 1)
  rw [complexCoth]
  unfold Complex.cosh Complex.sinh
  field_simp [hfactorNe, hdiff]
  rw [hsplit, ← hsq]
  ring

/-- Logarithmic differentiation of the FE-symmetric quartet is the reflected Euler connection. -/
theorem logDeriv_finiteEulerLocalQuartet
    (p : Nat.Primes) (s : ℂ) (hs : finiteEulerLocalQuartet p s ≠ 0) :
    logDeriv (finiteEulerLocalQuartet p) s =
      _root_.RHTower.primeLogSource p s -
        _root_.RHTower.primeLogSource p (1 - s) := by
  have hs' : finiteEulerLocalFactor p s ≠ 0 ∧
      finiteEulerLocalFactor p (1 - s) ≠ 0 := by
    simpa [finiteEulerLocalQuartet] using hs
  have hfirst := hasDerivAt_finiteEulerLocalFactor p s
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s :=
    (hasDerivAt_id s).const_sub 1
  have hsecond : DifferentiableAt ℂ
      (fun z : ℂ => finiteEulerLocalFactor p (1 - z)) s :=
    (hasDerivAt_finiteEulerLocalFactor p (1 - s)).comp s hinner |>.differentiableAt
  have hmul := logDeriv_mul s hs'.1 hs'.2 hfirst.differentiableAt hsecond
  have hcomp := logDeriv_comp
    (hasDerivAt_finiteEulerLocalFactor p (1 - s)).differentiableAt
    hinner.differentiableAt
  rw [logDeriv_finiteEulerLocalFactor, hinner.deriv] at hcomp
  change logDeriv (finiteEulerLocalQuartet p) s = _
  rw [show finiteEulerLocalQuartet p = fun z : ℂ =>
      finiteEulerLocalFactor p z * finiteEulerLocalFactor p (1 - z) by rfl]
  rw [hmul]
  change _ + logDeriv (fun z : ℂ => finiteEulerLocalFactor p (1 - z)) s = _
  rw [logDeriv_finiteEulerLocalFactor]
  rw [show logDeriv (fun z : ℂ => finiteEulerLocalFactor p (1 - z)) s =
      -_root_.RHTower.primeLogSource p (1 - s) by
        simpa [Function.comp_def] using hcomp]
  ring

end GaloisForLFunctions.RHTower

end
