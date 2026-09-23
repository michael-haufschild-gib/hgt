import GaloisForLFunctions.RHTower.FiniteEulerLocalQuartet
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Finite Euler factors as reciprocal Gamma pairs

Euler's reflection formula gives an unconditional reciprocal-Gamma expression
for every finite Euler factor.  The formulation uses inverses of Gamma values,
so it remains valid at the apparent Gamma-pole locations.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The imaginary Gamma slope associated with a finite prime. -/
def finiteEulerGammaSlope (p : Nat.Primes) : ℂ :=
  Complex.I * (Real.log p : ℂ) / (2 * (Real.pi : ℂ))

/-- The Euler--Gamma slope has no real component. -/
theorem finiteEulerGammaSlope_re (p : Nat.Primes) :
    (finiteEulerGammaSlope p).re = 0 := by
  set L : ℝ := Real.log (p : ℝ)
  change (Complex.I * (L : ℂ) / (2 * (Real.pi : ℂ))).re = 0
  simp [Complex.div_re]

/-- Every prime produces a genuinely upper-imaginary Gamma slope. -/
theorem finiteEulerGammaSlope_im_pos (p : Nat.Primes) :
    0 < (finiteEulerGammaSlope p).im := by
  set L : ℝ := Real.log (p : ℝ)
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  change 0 < (Complex.I * (L : ℂ) / (2 * (Real.pi : ℂ))).im
  have hL : 0 < L := hlog
  simp [Complex.div_im, hL, Real.pi_pos]

/-- The reciprocal Gamma pair associated with one finite Euler factor. -/
def finiteEulerGammaReciprocalPair (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Complex.Gamma (finiteEulerGammaSlope p * s) *
    Complex.Gamma (1 - finiteEulerGammaSlope p * s))⁻¹

/-- The finite semilocal inverse Euler multiplier. -/
def finiteEulerSemilocalProduct (S : Finset Nat.Primes) (s : ℂ) : ℂ :=
  ∏ p ∈ S, finiteEulerLocalFactor p s

/-- **Finite Euler--Gamma reflection weld.**  Every prime Euler factor is exactly a reciprocal
Gamma pair with its canonical imaginary slope. -/
theorem finiteEulerLocalFactor_eq_reciprocalGammaPair (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalFactor p s =
      -2 * Complex.I * (Real.pi : ℂ) *
        Complex.exp (-((Real.log p : ℂ) * s) / 2) *
        (Complex.Gamma (finiteEulerGammaSlope p * s) *
          Complex.Gamma (1 - finiteEulerGammaSlope p * s))⁻¹ := by
  let u : ℂ := Complex.I * (Real.log p : ℂ) * s / (2 * (Real.pi : ℂ))
  let x : ℂ := (Real.log p : ℂ) * s
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hrecip : (Complex.Gamma u * Complex.Gamma (1 - u))⁻¹ =
      Complex.sin ((Real.pi : ℂ) * u) / (Real.pi : ℂ) := by
    rw [Complex.Gamma_mul_Gamma_one_sub, inv_div]
  have hsin : Complex.sin ((Real.pi : ℂ) * u) =
      Complex.I / 2 * (Complex.exp (x / 2) - Complex.exp (-(x / 2))) := by
    rw [show (Real.pi : ℂ) * u = (x / 2) * Complex.I by
      dsimp [u, x]
      field_simp [hpi]]
    rw [Complex.sin_mul_I]
    unfold Complex.sinh
    ring
  have hsum : Complex.exp (-(x / 2)) * Complex.exp (x / 2) = 1 := by
    rw [← Complex.exp_add]
    have : -(x / 2) + x / 2 = 0 := by ring
    rw [this, Complex.exp_zero]
  have hsq : Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) = Complex.exp (-x) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold finiteEulerLocalFactor
  rw [show -s * (Real.log p : ℂ) = -x by
    dsimp [x]
    ring]
  rw [show finiteEulerGammaSlope p * s = u by
    dsimp [finiteEulerGammaSlope, u]
    ring,
    show (Real.log p : ℂ) * s = x by rfl, hrecip, hsin]
  field_simp [hpi]
  rw [Complex.I_sq]
  calc
    1 - Complex.exp (-x) =
        Complex.exp (-(x / 2)) * Complex.exp (x / 2) -
          Complex.exp (-(x / 2)) * Complex.exp (-(x / 2)) := by rw [hsum, hsq]
    _ = Complex.exp (-(x / 2)) *
          (Complex.exp (x / 2) - Complex.exp (-(x / 2))) := by ring
    _ = -(-1 * (Complex.exp (-(x / 2)) *
          (Complex.exp (x / 2) - Complex.exp (-(x / 2))))) := by ring
    _ = -(-1 * Complex.exp (-(x / 2)) *
          (Complex.exp (x / 2) - Complex.exp (-(x / 2)))) := by ring

/-- The local Euler--Gamma weld in terms of the named reciprocal Gamma pair. -/
theorem finiteEulerLocalFactor_eq_gammaReciprocalPair (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalFactor p s =
      -2 * Complex.I * (Real.pi : ℂ) *
        Complex.exp (-((Real.log p : ℂ) * s) / 2) *
        finiteEulerGammaReciprocalPair p s := by
  simpa only [finiteEulerGammaReciprocalPair] using
    finiteEulerLocalFactor_eq_reciprocalGammaPair p s

/-- The functional-equation-symmetric Euler quartet is a four-factor reciprocal-Gamma
weld with a constant exponential gauge. -/
theorem finiteEulerLocalQuartet_eq_gammaReciprocalQuartet
    (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalQuartet p s =
      (-2 * Complex.I * (Real.pi : ℂ)) ^ (2 : ℕ) *
        Complex.exp (-((Real.log p : ℂ) / 2)) *
        (finiteEulerGammaReciprocalPair p s *
          finiteEulerGammaReciprocalPair p (1 - s)) := by
  rw [finiteEulerLocalQuartet,
    finiteEulerLocalFactor_eq_gammaReciprocalPair p s,
    finiteEulerLocalFactor_eq_gammaReciprocalPair p (1 - s)]
  have hexp : Complex.exp (-((Real.log p : ℂ) * s) / 2) *
      Complex.exp (-((Real.log p : ℂ) * (1 - s)) / 2)
      = Complex.exp (-((Real.log p : ℂ) / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    -2 * Complex.I * (Real.pi : ℂ) * Complex.exp (-((Real.log p : ℂ) * s) / 2) *
          finiteEulerGammaReciprocalPair p s *
        (-2 * Complex.I * (Real.pi : ℂ) *
          Complex.exp (-((Real.log p : ℂ) * (1 - s)) / 2) *
          finiteEulerGammaReciprocalPair p (1 - s)) =
        ((-2 * Complex.I * (Real.pi : ℂ)) * (-2 * Complex.I * (Real.pi : ℂ))) *
          (Complex.exp (-((Real.log p : ℂ) * s) / 2) *
            Complex.exp (-((Real.log p : ℂ) * (1 - s)) / 2)) *
          (finiteEulerGammaReciprocalPair p s *
            finiteEulerGammaReciprocalPair p (1 - s)) := by ring
    _ = (-2 * Complex.I * (Real.pi : ℂ)) ^ (2 : ℕ) *
          Complex.exp (-((Real.log p : ℂ) / 2)) *
          (finiteEulerGammaReciprocalPair p s *
            finiteEulerGammaReciprocalPair p (1 - s)) := by
      rw [hexp]
      ring

/-- A finite semilocal Euler multiplier is the product of its reciprocal Gamma pairs with the
combined cardinality and logarithmic-exponential gauge. -/
theorem finiteEulerSemilocalProduct_eq_gammaReciprocalPairs
    (S : Finset Nat.Primes) (s : ℂ) :
    finiteEulerSemilocalProduct S s =
      (-2 * Complex.I * (Real.pi : ℂ)) ^ S.card *
        Complex.exp (-s * (∑ p ∈ S, (Real.log p : ℂ)) / 2) *
        ∏ p ∈ S, finiteEulerGammaReciprocalPair p s := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp [finiteEulerSemilocalProduct, finiteEulerGammaReciprocalPair]
  | insert p S hp ih =>
      unfold finiteEulerSemilocalProduct at ih ⊢
      rw [Finset.prod_insert hp, finiteEulerLocalFactor_eq_reciprocalGammaPair, ih,
        Finset.card_insert_of_notMem hp, Finset.sum_insert hp,
        Finset.prod_insert hp]
      unfold finiteEulerGammaReciprocalPair
      have hexp : Complex.exp (-s * ((Real.log p : ℂ) + ∑ q ∈ S, (Real.log q : ℂ)) / 2) =
          Complex.exp (-((Real.log p : ℂ) * s) / 2) *
            Complex.exp (-s * (∑ q ∈ S, (Real.log q : ℂ)) / 2) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hexp, pow_succ]
      ring_nf

end GaloisForLFunctions.RHTower

end
