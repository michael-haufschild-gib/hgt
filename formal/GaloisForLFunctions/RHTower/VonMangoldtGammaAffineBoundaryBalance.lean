import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy

/-!
# Cutoff-compatible affine two-boundary balance

Orthogonal two-boundary compression is positive at every finite aperture, but its projection
coefficients depend on the aperture.  The two boundary characters themselves force a second,
cutoff-compatible balance: subtract the unique affine combination of the Cauchy cells at `+a`
and `-a` which cancels the first two Laurent coefficients at infinity.

The residual has the exact triple-denominator factor

`(w^(2 : ℕ)-a^(2 : ℕ)) / ((w+lambda)(a+lambda)(-a+lambda))`.

For `a=1/2` this removes both Mellin boundary values and gains three inverse powers of the
prime-log rate.  The resulting finite von Mangoldt vectors are literal prefixes of one common
source packet, and their Grams remain positive semidefinite.  Summability at the Euler boundary
and comparison with the completed prime--Gamma moment germ remain separate analytic theorems.
-/

open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Affine coefficient of the positive boundary cell. -/
def twoBoundaryCauchyAffinePlusCoefficient (a w : ℂ) : ℂ :=
  (a + w) / (2 * a)

/-- Affine coefficient of the negative boundary cell. -/
def twoBoundaryCauchyAffineMinusCoefficient (a w : ℂ) : ℂ :=
  (a - w) / (2 * a)

/-- Cauchy cell after the affine subtraction of its two boundary values. -/
def twoBoundaryCauchyAffineResidual (a w lambda : ℂ) : ℂ :=
  1 / (w + lambda) -
    twoBoundaryCauchyAffinePlusCoefficient a w / (a + lambda) -
    twoBoundaryCauchyAffineMinusCoefficient a w / (-a + lambda)

@[simp] theorem twoBoundaryCauchyAffineResidual_self_plus
    (a lambda : ℂ) (ha : a ≠ 0) :
    twoBoundaryCauchyAffineResidual a a lambda = 0 := by
  have hcoeff : (a + a) / (2 * a) = (1 : ℂ) := by
    field_simp
    ring
  simp [twoBoundaryCauchyAffineResidual,
    twoBoundaryCauchyAffinePlusCoefficient,
    twoBoundaryCauchyAffineMinusCoefficient, hcoeff]

@[simp] theorem twoBoundaryCauchyAffineResidual_self_minus
    (a lambda : ℂ) (ha : a ≠ 0) :
    twoBoundaryCauchyAffineResidual a (-a) lambda = 0 := by
  have hcoeff : (a + a) / (2 * a) = (1 : ℂ) := by
    field_simp
    ring
  simp [twoBoundaryCauchyAffineResidual,
    twoBoundaryCauchyAffinePlusCoefficient,
    twoBoundaryCauchyAffineMinusCoefficient, hcoeff]

/-- Exact three-denominator gain from the affine two-boundary subtraction. -/
theorem twoBoundaryCauchyAffineResidual_eq
    {a w lambda : ℂ} (ha : a ≠ 0)
    (hw : w + lambda ≠ 0) (hp : a + lambda ≠ 0)
    (hm : -a + lambda ≠ 0) :
    twoBoundaryCauchyAffineResidual a w lambda =
      (w ^ (2 : ℕ) - a ^ (2 : ℕ)) /
        ((w + lambda) * (a + lambda) * (-a + lambda)) := by
  rw [twoBoundaryCauchyAffineResidual,
    twoBoundaryCauchyAffinePlusCoefficient,
    twoBoundaryCauchyAffineMinusCoefficient]
  field_simp
  ring

/-- Affine-balanced all-depth source feature. -/
def finiteExponentialAllDepthAffineBalancedCauchyFeature
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (a w : ℂ) (p : P) : ℂ :=
  finiteExponentialAllDepthCauchyFeature weight rate N i w p -
    twoBoundaryCauchyAffinePlusCoefficient a w *
      finiteExponentialAllDepthCauchyFeature weight rate N i a p -
    twoBoundaryCauchyAffineMinusCoefficient a w *
      finiteExponentialAllDepthCauchyFeature weight rate N i (-a) p

/-- The feature is the actual oriented anomaly numerator times the affine scalar residual. -/
theorem finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (a w : ℂ) (p : P) :
    finiteExponentialAllDepthAffineBalancedCauchyFeature
        weight rate N i a w p =
      (Real.sqrt (weight p) * rate p ^ (i : ℕ) *
          expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) *
        twoBoundaryCauchyAffineResidual a w (rate p : ℂ) := by
  rw [finiteExponentialAllDepthAffineBalancedCauchyFeature]
  simp only [finiteExponentialAllDepthCauchyFeature]
  rw [twoBoundaryCauchyAffineResidual]
  ring

@[simp] theorem finiteExponentialAllDepthAffineBalancedCauchyFeature_plus_eq_zero
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (a : ℂ) (ha : a ≠ 0) (p : P) :
    finiteExponentialAllDepthAffineBalancedCauchyFeature
        weight rate N i a a p = 0 := by
  rw [finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual]
  rw [twoBoundaryCauchyAffineResidual_self_plus a (rate p) ha, mul_zero]

@[simp] theorem finiteExponentialAllDepthAffineBalancedCauchyFeature_minus_eq_zero
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (a : ℂ) (ha : a ≠ 0) (p : P) :
    finiteExponentialAllDepthAffineBalancedCauchyFeature
        weight rate N i a (-a) p = 0 := by
  rw [finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual]
  rw [twoBoundaryCauchyAffineResidual_self_minus a (rate p) ha, mul_zero]

/-- Triple-denominator form of the affine-balanced source feature. -/
theorem finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_triple
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    {a w : ℂ} (p : P) (ha : a ≠ 0)
    (hw : w + (rate p : ℂ) ≠ 0) (hp : a + (rate p : ℂ) ≠ 0)
    (hm : -a + (rate p : ℂ) ≠ 0) :
    finiteExponentialAllDepthAffineBalancedCauchyFeature
        weight rate N i a w p =
      (Real.sqrt (weight p) * rate p ^ (i : ℕ) *
          expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) *
        ((w ^ (2 : ℕ) - a ^ (2 : ℕ)) /
          ((w + (rate p : ℂ)) * (a + (rate p : ℂ)) *
            (-a + (rate p : ℂ)))) := by
  rw [finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual,
    twoBoundaryCauchyAffineResidual_eq ha hw hp hm]

/-- Actual von Mangoldt specialization at the two Mellin boundary characters `±1/2`. -/
def finiteVonMangoldtAllDepthAffineBalancedCauchyFeature
    (N : ℕ) (i : Fin N) (w : ℂ) (n : ℕ) : ℂ :=
  finiteExponentialAllDepthAffineBalancedCauchyFeature
    finiteVonMangoldtRealWeight (fun n : ℕ => Real.log n)
    N i (1 / 2) w n

@[simp] theorem finiteVonMangoldtAllDepthAffineBalancedCauchyFeature_plus_eq_zero
    (N : ℕ) (i : Fin N) (n : ℕ) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyFeature N i (1 / 2) n = 0 := by
  rw [finiteVonMangoldtAllDepthAffineBalancedCauchyFeature,
    finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual,
    twoBoundaryCauchyAffineResidual_self_plus (1 / 2) (Real.log n) (by norm_num), mul_zero]

@[simp] theorem finiteVonMangoldtAllDepthAffineBalancedCauchyFeature_minus_eq_zero
    (N : ℕ) (i : Fin N) (n : ℕ) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyFeature N i (-1 / 2) n = 0 := by
  have hminus : (-1 / 2 : ℂ) = -(1 / 2 : ℂ) := by ring
  rw [hminus]
  rw [finiteVonMangoldtAllDepthAffineBalancedCauchyFeature,
    finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual,
    twoBoundaryCauchyAffineResidual_self_minus (1 / 2) (Real.log n) (by norm_num), mul_zero]

/-- Finite prefix of the cutoff-independent affine-balanced source packet. -/
def finiteVonMangoldtAllDepthAffineBalancedCauchyVector
    (M N : ℕ) (w : ℂ) : EuclideanSpace ℂ (Fin M × Fin N) :=
  WithLp.toLp 2 fun pi =>
    star (finiteVonMangoldtAllDepthAffineBalancedCauchyFeature
      N pi.2 w ((pi.1 : ℕ) + 2))

theorem finiteVonMangoldtAllDepthAffineBalancedCauchyVector_apply
    (M N : ℕ) (w : ℂ) (pi : Fin M × Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N w) pi =
      star (finiteVonMangoldtAllDepthAffineBalancedCauchyFeature
        N pi.2 w ((pi.1 : ℕ) + 2)) := by
  rfl

@[simp] theorem finiteVonMangoldtAllDepthAffineBalancedCauchyVector_plus_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N (1 / 2) = 0 := by
  apply WithLp.ofLp_injective 2
  funext pi
  simp only [finiteVonMangoldtAllDepthAffineBalancedCauchyVector, WithLp.ofLp_toLp]
  rw [finiteVonMangoldtAllDepthAffineBalancedCauchyFeature_plus_eq_zero
    N pi.2 ((pi.1 : ℕ) + 2)]
  simp

@[simp] theorem finiteVonMangoldtAllDepthAffineBalancedCauchyVector_minus_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N (-1 / 2) = 0 := by
  apply WithLp.ofLp_injective 2
  funext pi
  simp only [finiteVonMangoldtAllDepthAffineBalancedCauchyVector, WithLp.ofLp_toLp]
  rw [finiteVonMangoldtAllDepthAffineBalancedCauchyFeature_minus_eq_zero
    N pi.2 ((pi.1 : ℕ) + 2)]
  simp

/-- Prefix compatibility: increasing the aperture does not change any existing source
coordinate.  Unlike orthogonal compression, no cutoff-dependent projection coefficient occurs. -/
theorem finiteVonMangoldtAllDepthAffineBalancedCauchyVector_prefix
    {M M' : ℕ} (hMM' : M ≤ M') (N : ℕ) (w : ℂ)
    (p : Fin M) (i : Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthAffineBalancedCauchyVector M' N w)
        (Fin.castLE hMM' p, i) =
      WithLp.ofLp (finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N w) (p, i) := by
  simp only [finiteVonMangoldtAllDepthAffineBalancedCauchyVector_apply]
  rfl

/-- Positive finite Gram of the cutoff-compatible affine-balanced source vectors. -/
def finiteVonMangoldtAllDepthAffineBalancedCauchyGram
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.gram ℂ
    (fun a => finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N (w a))

theorem finiteVonMangoldtAllDepthAffineBalancedCauchyGram_posSemidef
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (finiteVonMangoldtAllDepthAffineBalancedCauchyGram M N w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

end

end RHTower
