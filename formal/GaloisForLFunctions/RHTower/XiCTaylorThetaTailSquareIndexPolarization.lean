import GaloisForLFunctions.RHTower.XiCTaylorThetaTailConvexCore
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPairCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMobiusConstraint

/-!
# Signed square-index polarization of the canonical theta-tail packet

The exact second-density polynomial has a Lorentzian difference-of-squares factorization.  This
module lifts that factorization from one ordered pair of square-index atoms to the complete
absolutely convergent density packet and to the theta-tail core current.  Both square channels
are nonnegative; no divisor data or zero information enters the identities.
-/

open scoped BigOperators
open Polynomial Real Set MeasureTheory Complex Filter Topology

namespace RHTower

noncomputable section

/-- The exact Lorentzian polarization of the canonical second-density polynomial. -/
theorem squareIndexDensityPolynomial_polarization (X Y : ℝ) :
    (1 - 24 * X + 16 * X ^ 2) * (1 - 24 * Y + 16 * Y ^ 2) =
      16 * (X + Y - 3 / 4 - 12 * X * Y) ^ 2 -
        8 * (1 - 16 * X * Y) ^ 2 := by
  ring

/-- Explicit value of one square-index atom of the exact density `4 T''`. -/
theorem thetaCuspTailSecondDensityAtom_value (n : ℕ) (x : ℝ) :
    thetaCuspTailSecondDensityAtom n x =
      Real.exp (x / 2) *
        (1 - 24 * (Real.pi * ((n : ℝ) * Real.exp x) ^ 2) +
          16 * (Real.pi * ((n : ℝ) * Real.exp x) ^ 2) ^ 2) *
        Real.exp (-(Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) := by
  unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
  rw [thetaCuspTailDerivativePolynomial_two]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The density product of two square-index atoms is an exact difference of Gaussian squares. -/
theorem thetaCuspTailSecondDensityAtom_mul_polarization
    (m n : ℕ) (x y : ℝ) :
    thetaCuspTailSecondDensityAtom m x *
        thetaCuspTailSecondDensityAtom n y =
      Real.exp (x / 2) * Real.exp (y / 2) *
        Real.exp (-(Real.pi * ((m : ℝ) * Real.exp x) ^ 2)) *
        Real.exp (-(Real.pi * ((n : ℝ) * Real.exp y) ^ 2)) *
        (16 *
            (Real.pi * ((m : ℝ) * Real.exp x) ^ 2 +
                Real.pi * ((n : ℝ) * Real.exp y) ^ 2 - 3 / 4 -
                12 * (Real.pi * ((m : ℝ) * Real.exp x) ^ 2) *
                  (Real.pi * ((n : ℝ) * Real.exp y) ^ 2)) ^ 2 -
          8 *
            (1 - 16 * (Real.pi * ((m : ℝ) * Real.exp x) ^ 2) *
              (Real.pi * ((n : ℝ) * Real.exp y) ^ 2)) ^ 2) := by
  rw [thetaCuspTailSecondDensityAtom_value,
    thetaCuspTailSecondDensityAtom_value]
  calc
    _ = Real.exp (x / 2) * Real.exp (y / 2) *
        Real.exp (-(Real.pi * ((m : ℝ) * Real.exp x) ^ 2)) *
        Real.exp (-(Real.pi * ((n : ℝ) * Real.exp y) ^ 2)) *
        ((1 - 24 * (Real.pi * ((m : ℝ) * Real.exp x) ^ 2) +
            16 * (Real.pi * ((m : ℝ) * Real.exp x) ^ 2) ^ 2) *
          (1 - 24 * (Real.pi * ((n : ℝ) * Real.exp y) ^ 2) +
            16 * (Real.pi * ((n : ℝ) * Real.exp y) ^ 2) ^ 2)) := by ring
    _ = _ := by rw [squareIndexDensityPolynomial_polarization]

/-- Pairing the two arithmetic orientations of a square-index pair gives one positive pair of
hyperbolic squares and one negative radial square. -/
theorem squareIndexSignedSwap_hyperbolic
    (W A B C L : ℝ) :
    W * Real.exp (-(A + B)) * (16 * (C + B) ^ 2 - 8 * L ^ 2) +
        W * Real.exp (-(A - B)) * (16 * (C - B) ^ 2 - 8 * L ^ 2) =
      16 * W * Real.exp (-A) *
        ((C - B) ^ 2 * Real.exp B + (C + B) ^ 2 * Real.exp (-B) -
          L ^ 2 * Real.cosh B) := by
  have hplus : Real.exp (-(A + B)) = Real.exp (-A) * Real.exp (-B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hminus : Real.exp (-(A - B)) = Real.exp (-A) * Real.exp B := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hplus, hminus, Real.cosh_eq]
  ring

/-- Abstract arithmetic swap form.  The hypotheses state that the two orientations have radial
scales `A+B` and `A-B` and the same square-index product `P`. -/
theorem squareIndexDensitySwap_polarization
    (W X Y X' Y' A B P : ℝ)
    (hplus : X + Y = A + B) (hminus : X' + Y' = A - B)
    (hprod : X * Y = P) (hprod' : X' * Y' = P) :
    W * Real.exp (-X) * Real.exp (-Y) *
          (16 * (X + Y - 3 / 4 - 12 * X * Y) ^ 2 -
            8 * (1 - 16 * X * Y) ^ 2) +
        W * Real.exp (-X') * Real.exp (-Y') *
          (16 * (X' + Y' - 3 / 4 - 12 * X' * Y') ^ 2 -
            8 * (1 - 16 * X' * Y') ^ 2) =
      16 * W * Real.exp (-A) *
        (((A - 3 / 4 - 12 * P) - B) ^ 2 * Real.exp B +
          ((A - 3 / 4 - 12 * P) + B) ^ 2 * Real.exp (-B) -
          (1 - 16 * P) ^ 2 * Real.cosh B) := by
  have hexp : Real.exp (-X) * Real.exp (-Y) = Real.exp (-(A + B)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hexp' : Real.exp (-X') * Real.exp (-Y') = Real.exp (-(A - B)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hQ : X + Y - 3 / 4 - 12 * X * Y =
      (A - 3 / 4 - 12 * P) + B := by
    rw [hplus]
    nlinarith [hprod]
  have hQ' : X' + Y' - 3 / 4 - 12 * X' * Y' =
      (A - 3 / 4 - 12 * P) - B := by
    rw [hminus]
    nlinarith [hprod']
  have hL : 1 - 16 * X * Y = 1 - 16 * P := by
    nlinarith [hprod]
  have hL' : 1 - 16 * X' * Y' = 1 - 16 * P := by
    nlinarith [hprod']
  calc
    _ = W * (Real.exp (-X) * Real.exp (-Y)) *
          (16 * (X + Y - 3 / 4 - 12 * X * Y) ^ 2 -
            8 * (1 - 16 * X * Y) ^ 2) +
        W * (Real.exp (-X') * Real.exp (-Y')) *
          (16 * (X' + Y' - 3 / 4 - 12 * X' * Y') ^ 2 -
            8 * (1 - 16 * X' * Y') ^ 2) := by ring
    _ = _ := by
      rw [hexp, hexp', hQ, hQ', hL, hL']
      exact squareIndexSignedSwap_hyperbolic W A B
        (A - 3 / 4 - 12 * P) (1 - 16 * P)

/-! ## Current carried by a spectral translation phase -/

/-- The entire phase induced by a real logarithmic source translation. -/
def spectralTranslationPhase (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((a : ℂ) * I) * z)

theorem hasDerivAt_spectralTranslationPhase (a : ℝ) (z : ℂ) :
    HasDerivAt (spectralTranslationPhase a)
      (((a : ℂ) * I) * spectralTranslationPhase a z) z := by
  unfold spectralTranslationPhase
  convert (Complex.hasDerivAt_exp (((a : ℂ) * I) * z)).comp z
    ((hasDerivAt_id z).const_mul ((a : ℂ) * I)) using 1 <;> ring

/-- Multiplication by a spectral translation phase changes oriented current only by the explicit
phase drift `a |F|²`, up to the positive squared modulus of the phase itself. -/
theorem orientedPhaseCurrent_identity (p F F' : ℂ) (a : ℝ) :
    (p * (F' + ((a : ℂ) * I) * F) *
        (starRingEnd ℂ) (p * F)).im =
      Complex.normSq p * ((F' * (starRingEnd ℂ) F).im +
        a * Complex.normSq F) := by
  simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
  ring

/-- The Gaussian scale belonging to the square index `n²` at logarithmic source position `x`. -/
def thetaSquareIndexScale (n : ℕ) (x : ℝ) : ℝ :=
  Real.pi * ((n : ℝ) * Real.exp x) ^ 2

/-- Mean radial scale of the two arithmetic orientations `(m,n)` and `(n,m)`. -/
def thetaSquareIndexSwapCenterScale (m n : ℕ) (x y : ℝ) : ℝ :=
  (thetaSquareIndexScale m x + thetaSquareIndexScale n y +
    (thetaSquareIndexScale n x + thetaSquareIndexScale m y)) / 2

/-- Oriented radial difference of the two arithmetic orientations. -/
def thetaSquareIndexSwapDifferenceScale (m n : ℕ) (x y : ℝ) : ℝ :=
  (thetaSquareIndexScale m x + thetaSquareIndexScale n y -
    (thetaSquareIndexScale n x + thetaSquareIndexScale m y)) / 2

/-- Common square-index product of the two swapped orientations. -/
def thetaSquareIndexSwapProductScale (m n : ℕ) (x y : ℝ) : ℝ :=
  thetaSquareIndexScale m x * thetaSquareIndexScale n y

/-- The actual `(m,n) ↔ (n,m)` arithmetic packet has the signed hyperbolic square form. -/
theorem thetaCuspTailSecondDensityAtom_swap_polarization
    (m n : ℕ) (x y : ℝ) :
    let A := thetaSquareIndexSwapCenterScale m n x y
    let B := thetaSquareIndexSwapDifferenceScale m n x y
    let P := thetaSquareIndexSwapProductScale m n x y
    thetaCuspTailSecondDensityAtom m x * thetaCuspTailSecondDensityAtom n y +
        thetaCuspTailSecondDensityAtom n x * thetaCuspTailSecondDensityAtom m y =
      16 * (Real.exp (x / 2) * Real.exp (y / 2)) * Real.exp (-A) *
        (((A - 3 / 4 - 12 * P) - B) ^ 2 * Real.exp B +
          ((A - 3 / 4 - 12 * P) + B) ^ 2 * Real.exp (-B) -
          (1 - 16 * P) ^ 2 * Real.cosh B) := by
  dsimp only
  rw [thetaCuspTailSecondDensityAtom_mul_polarization,
    thetaCuspTailSecondDensityAtom_mul_polarization]
  apply squareIndexDensitySwap_polarization
  · unfold thetaSquareIndexSwapCenterScale thetaSquareIndexSwapDifferenceScale
      thetaSquareIndexScale
    ring
  · unfold thetaSquareIndexSwapCenterScale thetaSquareIndexSwapDifferenceScale
      thetaSquareIndexScale
    ring
  · rfl
  · unfold thetaSquareIndexSwapProductScale thetaSquareIndexScale
    ring

/-- The common positive Gaussian weight of one ordered square-index pair. -/
def thetaSquareIndexPairWeight (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (p.1 / 2) * Real.exp (p.2 / 2) *
    Real.exp (-(thetaSquareIndexScale (q.1 + 1) p.1)) *
      Real.exp (-(thetaSquareIndexScale (q.2 + 1) p.2))

/-- The center/product form in the positive square channel. -/
def thetaSquareIndexCentralForm (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  thetaSquareIndexScale (q.1 + 1) p.1 +
    thetaSquareIndexScale (q.2 + 1) p.2 - 3 / 4 -
      12 * thetaSquareIndexScale (q.1 + 1) p.1 *
        thetaSquareIndexScale (q.2 + 1) p.2

/-- The pure product form in the negative square channel. -/
def thetaSquareIndexRadialForm (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  1 - 16 * thetaSquareIndexScale (q.1 + 1) p.1 *
    thetaSquareIndexScale (q.2 + 1) p.2

/-- Positive channel of the square-index polarization. -/
def thetaSquareIndexPositiveChannel (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  16 * thetaSquareIndexPairWeight q p * thetaSquareIndexCentralForm q p ^ 2

/-- Negative channel of the square-index polarization. -/
def thetaSquareIndexNegativeChannel (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  8 * thetaSquareIndexPairWeight q p * thetaSquareIndexRadialForm q p ^ 2

/-- The signed square-index packet carried by one ordered arithmetic pair. -/
def thetaSquareIndexSignedPolarization (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  thetaSquareIndexPositiveChannel q p - thetaSquareIndexNegativeChannel q p

theorem thetaSquareIndexPositiveChannel_nonneg (q : ℕ × ℕ) (p : ℝ × ℝ) :
    0 ≤ thetaSquareIndexPositiveChannel q p := by
  unfold thetaSquareIndexPositiveChannel thetaSquareIndexPairWeight
  positivity

theorem thetaSquareIndexNegativeChannel_nonneg (q : ℕ × ℕ) (p : ℝ × ℝ) :
    0 ≤ thetaSquareIndexNegativeChannel q p := by
  unfold thetaSquareIndexNegativeChannel thetaSquareIndexPairWeight
  positivity

/-- Every ordered density pair is its canonical positive channel minus its canonical negative
channel. -/
theorem thetaCuspTailSecondDensityAtom_mul_eq_squareIndexSignedPolarization
    (q : ℕ × ℕ) (p : ℝ × ℝ) :
    thetaCuspTailSecondDensityAtom (q.1 + 1) p.1 *
        thetaCuspTailSecondDensityAtom (q.2 + 1) p.2 =
      thetaSquareIndexSignedPolarization q p := by
  rw [thetaCuspTailSecondDensityAtom_mul_polarization]
  unfold thetaSquareIndexSignedPolarization thetaSquareIndexPositiveChannel
    thetaSquareIndexNegativeChannel thetaSquareIndexPairWeight
    thetaSquareIndexCentralForm thetaSquareIndexRadialForm thetaSquareIndexScale
  ring_nf

/-- The full product `ρ(x)ρ(y)` is the absolutely convergent signed square-index packet. -/
theorem thetaCuspTailSecondDensity_mul_eq_tsum_squareIndexSignedPolarization
    (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y =
      ∑' q : ℕ × ℕ, thetaSquareIndexSignedPolarization q (x, y) := by
  rw [thetaCuspTailSecondDensity_mul_eq_tsum_atomPair]
  apply tsum_congr
  intro q
  exact thetaCuspTailSecondDensityAtom_mul_eq_squareIndexSignedPolarization q (x, y)

/-! ## Independent dyadic parity polarization -/

/-- The even square-index sector of the complete canonical density. -/
def thetaSquareIndexEvenDensity (x : ℝ) : ℝ :=
  ∑' m : ℕ+, thetaCuspTailSecondDensityAtom ((2 : ℕ+) * m) x

/-- The complementary odd square-index sector. -/
def thetaSquareIndexOddDensity (x : ℝ) : ℝ :=
  thetaCuspTailSecondDensity x - thetaSquareIndexEvenDensity x

/-- The arithmetic parity character applied to the square-index packet. -/
def thetaSquareIndexParityDensity (x : ℝ) : ℝ :=
  thetaSquareIndexEvenDensity x - thetaSquareIndexOddDensity x

/-- The even square-index sector is exactly the critical dyadic translate of the full density. -/
theorem thetaSquareIndexEvenDensity_eq_dyadic_translate (x : ℝ) :
    thetaSquareIndexEvenDensity x =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log 2) := by
  unfold thetaSquareIndexEvenDensity
  simpa only [PNat.val_ofNat] using
    (tsum_thetaCuspTailSecondDensityAtom_pnat_mul (2 : ℕ+) x)

theorem thetaSquareIndexEven_add_odd (x : ℝ) :
    thetaSquareIndexEvenDensity x + thetaSquareIndexOddDensity x =
      thetaCuspTailSecondDensity x := by
  unfold thetaSquareIndexOddDensity
  ring

/-- The parity-signed full packet is an exact dyadic finite difference of the canonical density. -/
theorem thetaSquareIndexParityDensity_eq_dyadic_difference (x : ℝ) :
    thetaSquareIndexParityDensity x =
      2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log 2)) -
          thetaCuspTailSecondDensity x := by
  unfold thetaSquareIndexParityDensity thetaSquareIndexOddDensity
  rw [thetaSquareIndexEvenDensity_eq_dyadic_translate]
  ring

/-- Poisson/parity reflection in density coordinates.  The parity row reflects to the odd row at
the adjacent dyadic scale, with only the elementary completion character left over. -/
theorem thetaSquareIndexParityDensity_neg_reflection (x : ℝ) :
    thetaSquareIndexParityDensity (-x) =
      2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaSquareIndexOddDensity (x - Real.log 2) +
        2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspReflectionMode (x - Real.log 2) -
        thetaCuspReflectionMode x := by
  rw [thetaSquareIndexParityDensity_eq_dyadic_difference]
  have harg : -x + Real.log 2 = -(x - Real.log 2) := by ring
  rw [harg, thetaCuspTailSecondDensity_neg,
    thetaCuspTailSecondDensity_neg]
  unfold thetaSquareIndexOddDensity
  rw [thetaSquareIndexEvenDensity_eq_dyadic_translate]
  have hshift : x - Real.log 2 + Real.log 2 = x := by ring
  rw [hshift]
  have hw : (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  linear_combination
    (2 * thetaCuspTailSecondDensity x) * hw

/-- The full square-index product minus its parity-polarized product is exactly the two cross-parity
channels. -/
theorem thetaCuspTailSecondDensity_mul_sub_parity_mul
    (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y -
        thetaSquareIndexParityDensity x * thetaSquareIndexParityDensity y =
      2 * (thetaSquareIndexEvenDensity x * thetaSquareIndexOddDensity y +
        thetaSquareIndexOddDensity x * thetaSquareIndexEvenDensity y) := by
  unfold thetaSquareIndexParityDensity thetaSquareIndexOddDensity
  ring

/-! ## Cofinal `2`-adic Haar polarization -/

/-- Density carried by indices divisible by `2^k`, in its exact critical-translate form. -/
def thetaSquareIndexDyadicDensity (k : ℕ) (x : ℝ) : ℝ :=
  (((2 ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
    thetaCuspTailSecondDensity (x + Real.log (2 ^ k : ℕ))

/-- Indices of exact `2`-adic valuation `k`. -/
def thetaSquareIndexDyadicOddLayer (k : ℕ) (x : ℝ) : ℝ :=
  thetaSquareIndexDyadicDensity k x - thetaSquareIndexDyadicDensity (k + 1) x

/-- The signed Haar/parity layer at dyadic depth `k`. -/
def thetaSquareIndexDyadicParityLayer (k : ℕ) (x : ℝ) : ℝ :=
  2 * thetaSquareIndexDyadicDensity (k + 1) x - thetaSquareIndexDyadicDensity k x

theorem thetaSquareIndexDyadicDensity_zero (x : ℝ) :
    thetaSquareIndexDyadicDensity 0 x = thetaCuspTailSecondDensity x := by
  simp [thetaSquareIndexDyadicDensity]

private theorem real_log_two_pow (k : ℕ) :
    Real.log (((2 ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log 2 := by
  rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num]
  exact Real.log_pow 2 k

private theorem thetaSquareIndexDyadicWeight_succ (k : ℕ) :
    ((((2 ^ (k + 1) : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  rw [pow_succ]
  push_cast
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Every dyadic divisibility row is a critical rescaling and logarithmic translate of the full
canonical density. -/
theorem thetaSquareIndexDyadicDensity_eq_scaledDensity (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicDensity k x =
      ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        thetaCuspTailSecondDensity (x + (k : ℝ) * Real.log 2) := by
  unfold thetaSquareIndexDyadicDensity
  rw [real_log_two_pow]

/-- The exact-valuation row at depth `k` is the translated level-zero odd row. -/
theorem thetaSquareIndexDyadicOddLayer_eq_scaledOddDensity (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicOddLayer k x =
      ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        thetaSquareIndexOddDensity (x + (k : ℝ) * Real.log 2) := by
  rw [thetaSquareIndexDyadicOddLayer,
    thetaSquareIndexDyadicDensity_eq_scaledDensity,
    thetaSquareIndexDyadicDensity_eq_scaledDensity,
    thetaSquareIndexDyadicWeight_succ]
  unfold thetaSquareIndexOddDensity
  rw [thetaSquareIndexEvenDensity_eq_dyadic_translate]
  have hshift : x + ((k + 1 : ℕ) : ℝ) * Real.log 2 =
      x + (k : ℝ) * Real.log 2 + Real.log 2 := by
    push_cast
    ring
  rw [hshift]
  ring

/-- The parity row at depth `k` is the translated level-zero parity row. -/
theorem thetaSquareIndexDyadicParityLayer_eq_scaledParityDensity
    (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicParityLayer k x =
      ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        thetaSquareIndexParityDensity (x + (k : ℝ) * Real.log 2) := by
  rw [thetaSquareIndexDyadicParityLayer,
    thetaSquareIndexDyadicDensity_eq_scaledDensity,
    thetaSquareIndexDyadicDensity_eq_scaledDensity,
    thetaSquareIndexDyadicWeight_succ]
  rw [thetaSquareIndexParityDensity_eq_dyadic_difference]
  have hshift : x + ((k + 1 : ℕ) : ℝ) * Real.log 2 =
      x + (k : ℝ) * Real.log 2 + Real.log 2 := by
    push_cast
    ring
  rw [hshift]
  ring

/-- The logarithmic displacement forced by reflecting the depth-`k` parity row into the
depth-`k` exact-valuation row. -/
def thetaSquareIndexDyadicReflectionShift (k : ℕ) : ℝ :=
  (2 * k + 1 : ℕ) * Real.log 2

/-- The two elementary completion characters left by the depth-`k` parity reflection. -/
def thetaSquareIndexDyadicCompletionDefect (k : ℕ) (x : ℝ) : ℝ :=
  ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspReflectionMode (x - (k + 1 : ℕ) * Real.log 2) -
      thetaCuspReflectionMode (x - (k : ℝ) * Real.log 2))

/-- At one dyadic step, the growing completion character cancels and only the decaying character
survives. -/
theorem thetaSquareIndexCompletionCharacter_cancel (x : ℝ) :
    2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspReflectionMode (x - Real.log 2) -
      thetaCuspReflectionMode x = -(1 / 2 : ℝ) * Real.exp (-x / 2) := by
  unfold thetaCuspReflectionMode
  have h1 : Real.exp ((x - Real.log 2) / 2) =
      Real.exp (x / 2) * Real.exp (-(Real.log 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(x - Real.log 2) / 2) =
      Real.exp (-x / 2) * Real.exp (Real.log 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1, h2]
  have hneg : Real.exp (-(Real.log 2) / 2) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpos : Real.exp (Real.log 2 / 2) =
      (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hneg, hpos]
  have hww : (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hwr : (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  linear_combination Real.exp (x / 2) * hww - Real.exp (-x / 2) * hwr

/-- The completion defect in every reflected Haar layer is the same decaying character,
independent of the arithmetic depth. -/
theorem thetaSquareIndexDyadicCompletionDefect_eq (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicCompletionDefect k x =
      -(1 / 2 : ℝ) * Real.exp (-x / 2) := by
  unfold thetaSquareIndexDyadicCompletionDefect
  have hinside :=
    thetaSquareIndexCompletionCharacter_cancel (x - (k : ℝ) * Real.log 2)
  have hshift : x - (k : ℝ) * Real.log 2 - Real.log 2 =
      x - ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    ring
  rw [hshift] at hinside
  rw [hinside]
  have hw : ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(x - (k : ℝ) * Real.log 2) / 2) =
        Real.exp (-x / 2) := by
    rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    rw [show Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 by
      exact Real.log_pow 2 k]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
      (-(1 / 2 : ℝ) * Real.exp (-(x - (k : ℝ) * Real.log 2) / 2)) =
        -(1 / 2 : ℝ) *
          (((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(x - (k : ℝ) * Real.log 2) / 2)) by ring,
    hw]

private theorem thetaSquareIndexDyadicReflectionAmplitude_sq :
    (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 2 := by
  have hw : (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  nlinarith

/-- All-depth arithmetic reflection.  The parity row becomes the exact-valuation row translated
by `(2k+1) log 2`; its amplitude has square `2`, exactly the Haar coefficient ratio. -/
theorem thetaSquareIndexDyadicParityLayer_neg_reflection (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicParityLayer k (-x) =
      2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k) +
        thetaSquareIndexDyadicCompletionDefect k x := by
  rw [thetaSquareIndexDyadicParityLayer_eq_scaledParityDensity]
  have harg : -x + (k : ℝ) * Real.log 2 =
      -(x - (k : ℝ) * Real.log 2) := by ring
  rw [harg, thetaSquareIndexParityDensity_neg_reflection]
  rw [thetaSquareIndexDyadicOddLayer_eq_scaledOddDensity]
  unfold thetaSquareIndexDyadicReflectionShift
  have hodd :
      x - ((2 * k + 1 : ℕ) : ℝ) * Real.log 2 +
          (k : ℝ) * Real.log 2 =
        x - (k : ℝ) * Real.log 2 - Real.log 2 := by
    push_cast
    ring
  have href : x - (k : ℝ) * Real.log 2 - Real.log 2 =
      x - ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    ring
  rw [hodd, href]
  unfold thetaSquareIndexDyadicCompletionDefect
  ring

/-- Simplified all-depth reflection: the only surviving completion character is universal and
decays at the positive end. -/
theorem thetaSquareIndexDyadicParityLayer_neg_reflection_simplified
    (k : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicParityLayer k (-x) =
      2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k) -
        (1 / 2 : ℝ) * Real.exp (-x / 2) := by
  rw [thetaSquareIndexDyadicParityLayer_neg_reflection,
    thetaSquareIndexDyadicCompletionDefect_eq]
  ring

/-- Every finite coefficient packet of total mass zero removes the universal completion character
exactly.  What remains is a pure signed arithmetic translate packet of exact-valuation rows. -/
theorem thetaSquareIndexDyadicBalancedParityPacket_neg_reflection
    (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∑ k ∈ s, c k = 0) (x : ℝ) :
    (∑ k ∈ s, c k * thetaSquareIndexDyadicParityLayer k (-x)) =
      2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
          (x - thetaSquareIndexDyadicReflectionShift k) := by
  calc
    _ = ∑ k ∈ s, c k *
        (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicOddLayer k
              (x - thetaSquareIndexDyadicReflectionShift k) -
          (1 / 2 : ℝ) * Real.exp (-x / 2)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [thetaSquareIndexDyadicParityLayer_neg_reflection_simplified]
    _ = 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k)) -
        ((1 / 2 : ℝ) * Real.exp (-x / 2)) * (∑ k ∈ s, c k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = _ := by rw [hc]; ring

/-- Product polarization for a balanced finite packet.  The completion character has disappeared,
and the square of the reflection amplitude is exactly `2`. -/
theorem thetaSquareIndexDyadicBalancedParityPacket_mul_neg_reflection
    (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∑ k ∈ s, c k = 0) (x y : ℝ) :
    (∑ k ∈ s, c k * thetaSquareIndexDyadicParityLayer k (-x)) *
        (∑ k ∈ s, c k * thetaSquareIndexDyadicParityLayer k (-y)) =
      2 *
        (∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
          (x - thetaSquareIndexDyadicReflectionShift k)) *
        (∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
          (y - thetaSquareIndexDyadicReflectionShift k)) := by
  rw [thetaSquareIndexDyadicBalancedParityPacket_neg_reflection s c hc x,
    thetaSquareIndexDyadicBalancedParityPacket_neg_reflection s c hc y]
  have ha := thetaSquareIndexDyadicReflectionAmplitude_sq
  calc
    _ = (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
        (∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
          (x - thetaSquareIndexDyadicReflectionShift k)) *
        (∑ k ∈ s, c k * thetaSquareIndexDyadicOddLayer k
          (y - thetaSquareIndexDyadicReflectionShift k)) := by ring
    _ = _ := by rw [ha]

/-- Finite weighted bilinear variance identity.  It splits a diagonal quadratic packet into one
rank-one mean direction and pairwise balanced difference packets. -/
theorem two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    {ι : Type*} (s : Finset ι) (w a b : ι → ℝ) :
    2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) =
      2 * (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) +
        ∑ i ∈ s, ∑ j ∈ s,
          w i * w j * (a i - a j) * (b i - b j) := by
  let L0 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a j * b j
  let L1 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a i * b i
  let C0 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a i * b j
  let C1 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a j * b i
  have hWC : (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) = L0 := by
    dsimp [L0]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hAB : (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) = C0 := by
    dsimp [C0]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hL : L0 = L1 := by
    dsimp [L0, L1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hC : C0 = C1 := by
    dsimp [C0, C1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [show (2 * (∑ i ∈ s, w i)) * (∑ i ∈ s, w i * a i * b i) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i)) by ring,
    show (2 * (∑ i ∈ s, w i * a i)) * (∑ i ∈ s, w i * b i) =
      2 * ((∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) by ring,
    hWC, hAB]
  calc
    2 * L0 = L0 + L1 := by rw [← hL]; ring
    _ = 2 * C0 + (L1 + L0 - C0 - C1) := by rw [← hC]; ring
    _ = 2 * C0 + ∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (a i - a j) * (b i - b j) := by
      congr 1
      dsimp [L0, L1, C0, C1]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- The weighted mean of the first `N` parity rows telescopes to one dyadic top row minus the full
canonical density. -/
theorem thetaSquareIndexDyadicParityLayer_weightedSum (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N,
      (2 : ℝ) ^ k * thetaSquareIndexDyadicParityLayer k x) =
        (2 : ℝ) ^ N * thetaSquareIndexDyadicDensity N x -
          thetaCuspTailSecondDensity x := by
  induction N with
  | zero => simp [thetaSquareIndexDyadicDensity_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold thetaSquareIndexDyadicParityLayer
      rw [pow_succ]
      ring

/-- Weighted-variance polarization of the complete finite parity diagonal.  Every double-sum term
is a balanced two-depth packet; the only unbalanced direction is the explicit top-row-minus-full-
density rank one. -/
theorem thetaSquareIndexDyadicParityDiagonal_variancePolarization
    (N : ℕ) (x y : ℝ) :
    2 * (∑ k ∈ Finset.range N, (2 : ℝ) ^ k) *
        (∑ k ∈ Finset.range N,
          (2 : ℝ) ^ k * thetaSquareIndexDyadicParityLayer k x *
            thetaSquareIndexDyadicParityLayer k y) =
      2 * ((2 : ℝ) ^ N * thetaSquareIndexDyadicDensity N x -
          thetaCuspTailSecondDensity x) *
        ((2 : ℝ) ^ N * thetaSquareIndexDyadicDensity N y -
          thetaCuspTailSecondDensity y) +
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (2 : ℝ) ^ i * (2 : ℝ) ^ j *
          (thetaSquareIndexDyadicParityLayer i x -
            thetaSquareIndexDyadicParityLayer j x) *
          (thetaSquareIndexDyadicParityLayer i y -
            thetaSquareIndexDyadicParityLayer j y) := by
  rw [← thetaSquareIndexDyadicParityLayer_weightedSum N x,
    ← thetaSquareIndexDyadicParityLayer_weightedSum N y]
  exact two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    (Finset.range N) (fun k => (2 : ℝ) ^ k)
      (fun k => thetaSquareIndexDyadicParityLayer k x)
      (fun k => thetaSquareIndexDyadicParityLayer k y)

/-- After reflection, the positive exact-valuation square and negative parity square cancel
exactly.  Only the two explicit completion-character cross terms and their square remain. -/
theorem thetaSquareIndexDyadicHaarLayer_reflected_polarization
    (k : ℕ) (x y : ℝ) :
    (2 : ℝ) ^ (k + 1) *
          thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k) *
          thetaSquareIndexDyadicOddLayer k
            (y - thetaSquareIndexDyadicReflectionShift k) -
        (2 : ℝ) ^ k *
          thetaSquareIndexDyadicParityLayer k (-x) *
            thetaSquareIndexDyadicParityLayer k (-y) =
      -(2 : ℝ) ^ k *
        (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicOddLayer k
              (x - thetaSquareIndexDyadicReflectionShift k) *
            thetaSquareIndexDyadicCompletionDefect k y +
          2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicCompletionDefect k x *
            thetaSquareIndexDyadicOddLayer k
              (y - thetaSquareIndexDyadicReflectionShift k) +
          thetaSquareIndexDyadicCompletionDefect k x *
            thetaSquareIndexDyadicCompletionDefect k y) := by
  rw [thetaSquareIndexDyadicParityLayer_neg_reflection,
    thetaSquareIndexDyadicParityLayer_neg_reflection, pow_succ]
  have ha := thetaSquareIndexDyadicReflectionAmplitude_sq
  calc
    _ = (2 : ℝ) ^ k *
        ((2 - (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) *
            thetaSquareIndexDyadicOddLayer k
              (x - thetaSquareIndexDyadicReflectionShift k) *
            thetaSquareIndexDyadicOddLayer k
              (y - thetaSquareIndexDyadicReflectionShift k) -
          2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicOddLayer k
              (x - thetaSquareIndexDyadicReflectionShift k) *
            thetaSquareIndexDyadicCompletionDefect k y -
          2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicCompletionDefect k x *
            thetaSquareIndexDyadicOddLayer k
              (y - thetaSquareIndexDyadicReflectionShift k) -
          thetaSquareIndexDyadicCompletionDefect k x *
            thetaSquareIndexDyadicCompletionDefect k y) := by ring
    _ = _ := by rw [ha]; ring

/-- Simplified reflected Haar polarization.  Its only source terms are two odd-row/decaying-
character cross terms and one favorable negative radial square. -/
theorem thetaSquareIndexDyadicHaarLayer_reflected_polarization_simplified
    (k : ℕ) (x y : ℝ) :
    (2 : ℝ) ^ (k + 1) *
          thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k) *
          thetaSquareIndexDyadicOddLayer k
            (y - thetaSquareIndexDyadicReflectionShift k) -
        (2 : ℝ) ^ k *
          thetaSquareIndexDyadicParityLayer k (-x) *
            thetaSquareIndexDyadicParityLayer k (-y) =
      (2 : ℝ) ^ k *
        ((2 : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaSquareIndexDyadicOddLayer k
              (x - thetaSquareIndexDyadicReflectionShift k) *
            Real.exp (-y / 2) +
          (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-x / 2) *
            thetaSquareIndexDyadicOddLayer k
              (y - thetaSquareIndexDyadicReflectionShift k) -
          (1 / 4 : ℝ) * Real.exp (-x / 2) * Real.exp (-y / 2)) := by
  rw [thetaSquareIndexDyadicHaarLayer_reflected_polarization,
    thetaSquareIndexDyadicCompletionDefect_eq,
    thetaSquareIndexDyadicCompletionDefect_eq]
  ring

/-- The dyadic translate is exactly the full row of square indices divisible by `2^k`. -/
theorem thetaSquareIndexDyadicDensity_eq_multiples_row (k : ℕ) (x : ℝ) :
    (∑' m : ℕ+,
      thetaCuspTailSecondDensityAtom
        ((⟨2 ^ k, pow_pos (by norm_num) k⟩ : ℕ+) * m) x) =
      thetaSquareIndexDyadicDensity k x := by
  simpa [thetaSquareIndexDyadicDensity] using
    (tsum_thetaCuspTailSecondDensityAtom_pnat_mul
      (⟨2 ^ k, pow_pos (by norm_num) k⟩ : ℕ+) x)

theorem thetaSquareIndexDyadicDensity_nonneg
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ thetaSquareIndexDyadicDensity k x := by
  rw [← thetaSquareIndexDyadicDensity_eq_multiples_row]
  exact tsum_nonneg fun m =>
    (thetaCuspTailSecondDensityAtom_pos
      (Nat.mul_pos (pow_pos (by norm_num) k) m.pos) hx).le

/-- Explicit double-exponential Gaussian bound for the dyadic top row on the positive source
half-line. -/
theorem thetaSquareIndexDyadicDensity_le_geometric
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    thetaSquareIndexDyadicDensity k x ≤
      (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * ((2 ^ k : ℕ) : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
          ∑' m : ℕ+, (m : ℝ) *
            (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1) := by
  simpa [thetaSquareIndexDyadicDensity] using
    (criticalThetaCuspDensityTranslate_le_geometric hx
      (⟨2 ^ k, pow_pos (by norm_num) k⟩ : ℕ+))

/-- The explicit dyadic top-row majorant tends to zero at a double-exponential rate. -/
theorem tendsto_thetaSquareIndexDyadicGeometricMajorant (x : ℝ) :
    Tendsto
      (fun k : ℕ =>
        (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
            Real.exp (-x)) * ((2 ^ k : ℕ) : ℝ) *
          (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
            ∑' m : ℕ+, (m : ℝ) *
              (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1))
      atTop (nhds 0) := by
  let q : ℝ := Real.exp (-(Real.pi / 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; linarith)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) * q ^ n) atTop (nhds 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 1 hq0 hq1)
  have htwo : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hcomp := hpow.comp htwo
  have hconst : Tendsto
      (fun _ : ℕ =>
        (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) *
          (∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)))
      atTop (nhds
        ((4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) *
          (∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)))) := tendsto_const_nhds
  have hmul := hconst.mul hcomp
  convert hmul using 1
  · funext k
    simp only [Function.comp_apply, q]
    ring
  · ring

/-- Every fixed positive-half-line value of the dyadic top row tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicDensity_zero
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun k : ℕ => thetaSquareIndexDyadicDensity k x) atTop (nhds 0) := by
  apply squeeze_zero
  · exact thetaSquareIndexDyadicDensity_nonneg hx
  · exact thetaSquareIndexDyadicDensity_le_geometric hx
  · exact tendsto_thetaSquareIndexDyadicGeometricMajorant x

/-- Named form of the explicit pointwise top-row majorant. -/
def thetaSquareIndexDyadicGeometricMajorant (x : ℝ) (k : ℕ) : ℝ :=
  (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
      Real.exp (-x)) * ((2 ^ k : ℕ) : ℝ) *
    (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
      ∑' m : ℕ+, (m : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1)

/-- Source coefficient of the top row in the finite Haar polarization. -/
def thetaSquareIndexDyadicRemainderSource (k : ℕ) (x y : ℝ) : ℝ :=
  (2 : ℝ) ^ k * thetaSquareIndexDyadicDensity k x *
    thetaSquareIndexDyadicDensity k y

/-- Product majorant for the dyadic Haar top-row source. -/
def thetaSquareIndexDyadicRemainderMajorant (k : ℕ) (x y : ℝ) : ℝ :=
  (2 : ℝ) ^ k * thetaSquareIndexDyadicGeometricMajorant x k *
    thetaSquareIndexDyadicGeometricMajorant y k

theorem thetaSquareIndexDyadicRemainderSource_le_majorant
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    thetaSquareIndexDyadicRemainderSource k x y ≤
      thetaSquareIndexDyadicRemainderMajorant k x y := by
  unfold thetaSquareIndexDyadicRemainderSource
    thetaSquareIndexDyadicRemainderMajorant
  have hdx := thetaSquareIndexDyadicDensity_nonneg hx k
  have hdy := thetaSquareIndexDyadicDensity_nonneg hy k
  have hmx : thetaSquareIndexDyadicDensity k x ≤
      thetaSquareIndexDyadicGeometricMajorant x k := by
    exact thetaSquareIndexDyadicDensity_le_geometric hx k
  have hmy : thetaSquareIndexDyadicDensity k y ≤
      thetaSquareIndexDyadicGeometricMajorant y k := by
    exact thetaSquareIndexDyadicDensity_le_geometric hy k
  have hmx0 : 0 ≤ thetaSquareIndexDyadicGeometricMajorant x k := hdx.trans hmx
  gcongr

/-- The explicit top-row product majorant tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicRemainderMajorant_zero (x y : ℝ) :
    Tendsto (fun k : ℕ => thetaSquareIndexDyadicRemainderMajorant k x y)
      atTop (nhds 0) := by
  let q : ℝ := Real.exp (-(Real.pi / 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; linarith)
  have hqSq0 : 0 ≤ q * q := mul_nonneg hq0 hq0
  have hqSq1 : q * q < 1 := by nlinarith
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * (q * q) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 3 hqSq0 hqSq1
  have htwo : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hcomp := hpow.comp htwo
  let C : ℝ :=
    (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
        Real.exp (-x)) *
      (∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)) *
    ((4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
        Real.exp (-y)) *
      (∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)))
  have hconst : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
  have hmul := hconst.mul hcomp
  convert hmul using 1
  · funext k
    simp only [Function.comp_apply]
    unfold thetaSquareIndexDyadicRemainderMajorant
      thetaSquareIndexDyadicGeometricMajorant
    dsimp [C, q]
    rw [mul_pow]
    push_cast
    ring
  · ring

/-- Pointwise, the complete top-row source in the Haar polarization tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicRemainderSource_zero
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Tendsto (fun k : ℕ => thetaSquareIndexDyadicRemainderSource k x y)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    unfold thetaSquareIndexDyadicRemainderSource
    exact mul_nonneg
      (mul_nonneg (by positivity) (thetaSquareIndexDyadicDensity_nonneg hx k))
      (thetaSquareIndexDyadicDensity_nonneg hy k)
  · exact thetaSquareIndexDyadicRemainderSource_le_majorant hx hy
  · exact tendsto_thetaSquareIndexDyadicRemainderMajorant_zero x y

/-! ## Integrated dyadic top-row moments -/

/-- Explicit Gaussian majorant for the `m`th moment of the depth-`k` dyadic top row. -/
def thetaSquareIndexDyadicMomentMajorant (m k : ℕ) : ℝ :=
  (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2)) *
    ((2 ^ k : ℕ) : ℝ) *
    (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
    (∑' n : ℕ+, (n : ℝ) *
      (Real.exp (-(Real.pi / 2))) ^ ((n : ℕ) - 1)) * m.factorial

/-- Every polynomial moment of a dyadic top row is integrable on the positive source half-line. -/
theorem integrableOn_pow_mul_thetaSquareIndexDyadicDensity (m k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * thetaSquareIndexDyadicDensity k x)
      (Ioi 0) := by
  let A : ℝ :=
    (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2)) *
      ((2 ^ k : ℕ) : ℝ) *
      (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
      ∑' n : ℕ+, (n : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ ((n : ℕ) - 1)
  have hg : IntegrableOn (fun x : ℝ => A * (x ^ m * Real.exp (-x))) (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [show (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-x)) =
          (m.factorial : ℝ) by
        simpa using integral_pow_mul_exp_nat_neg m 1 (by omega)]
      positivity
    exact hbase.const_mul A
  refine hg.mono' ?_ ?_
  · have hrho : Continuous thetaCuspTailSecondDensity :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspTailDerivative 2 x).continuousAt.const_mul 4
    exact ((continuous_pow m).mul
      ((hrho.comp (continuous_id.add continuous_const)).const_mul _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hrow := thetaSquareIndexDyadicDensity_le_geometric hx0 k
    have hrow0 := thetaSquareIndexDyadicDensity_nonneg hx0 k
    dsimp [A]
    calc
      ‖x ^ m * thetaSquareIndexDyadicDensity k x‖ =
          x ^ m * thetaSquareIndexDyadicDensity k x := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (pow_nonneg hx0 _) hrow0)]
      _ ≤ x ^ m * ((4 * thetaCuspGaussianConstant
            (thetaCuspTailDerivativePolynomial 2) * Real.exp (-x)) *
            ((2 ^ k : ℕ) : ℝ) *
            (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
            ∑' n : ℕ+, (n : ℝ) *
              (Real.exp (-(Real.pi / 2))) ^ ((n : ℕ) - 1)) :=
        mul_le_mul_of_nonneg_left hrow (pow_nonneg hx0 _)
      _ = _ := by ring

/-- The explicit majorant bounds the actual `m`th top-row moment. -/
theorem integral_pow_mul_thetaSquareIndexDyadicDensity_le_majorant (m k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ m * thetaSquareIndexDyadicDensity k x) ≤
      thetaSquareIndexDyadicMomentMajorant m k := by
  let A : ℝ :=
    (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2)) *
      ((2 ^ k : ℕ) : ℝ) *
      (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
      ∑' n : ℕ+, (n : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ ((n : ℕ) - 1)
  have hf := integrableOn_pow_mul_thetaSquareIndexDyadicDensity m k
  have hg : IntegrableOn (fun x : ℝ => A * (x ^ m * Real.exp (-x))) (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [show (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-x)) =
          (m.factorial : ℝ) by
        simpa using integral_pow_mul_exp_nat_neg m 1 (by omega)]
      positivity
    exact hbase.const_mul A
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, A * (x ^ m * Real.exp (-x)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hrow := thetaSquareIndexDyadicDensity_le_geometric hx0 k
      dsimp [A]
      calc
        x ^ m * thetaSquareIndexDyadicDensity k x ≤
            x ^ m * ((4 * thetaCuspGaussianConstant
              (thetaCuspTailDerivativePolynomial 2) * Real.exp (-x)) *
              ((2 ^ k : ℕ) : ℝ) *
              (Real.exp (-(Real.pi / 2))) ^ (2 ^ k : ℕ) *
              ∑' n : ℕ+, (n : ℝ) *
                (Real.exp (-(Real.pi / 2))) ^ ((n : ℕ) - 1)) :=
          mul_le_mul_of_nonneg_left hrow (pow_nonneg hx0 _)
        _ = _ := by ring
    _ = thetaSquareIndexDyadicMomentMajorant m k := by
      rw [integral_const_mul]
      rw [show (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-x)) =
          (m.factorial : ℝ) by
        simpa using integral_pow_mul_exp_nat_neg m 1 (by omega)]
      rfl

/-- Every fixed-moment majorant tends to zero at the same double-exponential rate as the row. -/
theorem tendsto_thetaSquareIndexDyadicMomentMajorant_zero (m : ℕ) :
    Tendsto (fun k : ℕ => thetaSquareIndexDyadicMomentMajorant m k)
      atTop (nhds 0) := by
  have h := (tendsto_thetaSquareIndexDyadicGeometricMajorant 0).mul_const
    (m.factorial : ℝ)
  convert h using 1
  · funext k
    simp [thetaSquareIndexDyadicMomentMajorant]
  · ring

/-- Every fixed polynomial moment of the cofinal dyadic top row tends to zero. -/
theorem tendsto_integral_pow_mul_thetaSquareIndexDyadicDensity_zero (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : ℝ in Ioi 0, x ^ m * thetaSquareIndexDyadicDensity k x)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _)
      (thetaSquareIndexDyadicDensity_nonneg hx.le k)
  · exact integral_pow_mul_thetaSquareIndexDyadicDensity_le_majorant m
  · exact tendsto_thetaSquareIndexDyadicMomentMajorant_zero m

/-- Weighted product of two dyadic top-row moments, in the normalization occurring in the Haar
remainder current. -/
def thetaSquareIndexDyadicWeightedMomentProduct (m n k : ℕ) : ℝ :=
  (2 : ℝ) ^ k *
    (∫ x : ℝ in Ioi 0, x ^ m * thetaSquareIndexDyadicDensity k x) *
    (∫ y : ℝ in Ioi 0, y ^ n * thetaSquareIndexDyadicDensity k y)

/-- Explicit product majorant for two weighted dyadic moments. -/
def thetaSquareIndexDyadicWeightedMomentProductMajorant (m n k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * thetaSquareIndexDyadicMomentMajorant m k *
    thetaSquareIndexDyadicMomentMajorant n k

theorem thetaSquareIndexDyadicWeightedMomentProduct_le_majorant (m n k : ℕ) :
    thetaSquareIndexDyadicWeightedMomentProduct m n k ≤
      thetaSquareIndexDyadicWeightedMomentProductMajorant m n k := by
  unfold thetaSquareIndexDyadicWeightedMomentProduct
    thetaSquareIndexDyadicWeightedMomentProductMajorant
  have hm0 : 0 ≤ ∫ x : ℝ in Ioi 0,
      x ^ m * thetaSquareIndexDyadicDensity k x := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _)
      (thetaSquareIndexDyadicDensity_nonneg hx.le k)
  have hn0 : 0 ≤ ∫ x : ℝ in Ioi 0,
      x ^ n * thetaSquareIndexDyadicDensity k x := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _)
      (thetaSquareIndexDyadicDensity_nonneg hx.le k)
  have hMm0 : 0 ≤ thetaSquareIndexDyadicMomentMajorant m k :=
    hm0.trans (integral_pow_mul_thetaSquareIndexDyadicDensity_le_majorant m k)
  gcongr
  · exact integral_pow_mul_thetaSquareIndexDyadicDensity_le_majorant m k
  · exact integral_pow_mul_thetaSquareIndexDyadicDensity_le_majorant n k

/-- The explicit weighted two-moment product majorant tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicWeightedMomentProductMajorant_zero
    (m n : ℕ) :
    Tendsto
      (fun k : ℕ => thetaSquareIndexDyadicWeightedMomentProductMajorant m n k)
      atTop (nhds 0) := by
  have h := (tendsto_thetaSquareIndexDyadicRemainderMajorant_zero 0 0).mul_const
    ((m.factorial : ℝ) * n.factorial)
  convert h using 1
  · funext k
    unfold thetaSquareIndexDyadicWeightedMomentProductMajorant
      thetaSquareIndexDyadicMomentMajorant
      thetaSquareIndexDyadicRemainderMajorant
      thetaSquareIndexDyadicGeometricMajorant
    simp
    ring
  · ring

/-- Every weighted product of two fixed polynomial moments in the Haar top row tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicWeightedMomentProduct_zero (m n : ℕ) :
    Tendsto (fun k : ℕ => thetaSquareIndexDyadicWeightedMomentProduct m n k)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    unfold thetaSquareIndexDyadicWeightedMomentProduct
    have hm0 : 0 ≤ ∫ x : ℝ in Ioi 0,
        x ^ m * thetaSquareIndexDyadicDensity k x := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _)
        (thetaSquareIndexDyadicDensity_nonneg hx.le k)
    have hn0 : 0 ≤ ∫ x : ℝ in Ioi 0,
        x ^ n * thetaSquareIndexDyadicDensity k x := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _)
        (thetaSquareIndexDyadicDensity_nonneg hx.le k)
    exact mul_nonneg (mul_nonneg (by positivity) hm0) hn0
  · exact thetaSquareIndexDyadicWeightedMomentProduct_le_majorant m n
  · exact tendsto_thetaSquareIndexDyadicWeightedMomentProductMajorant_zero m n

/-! ## Finite Taylor packets carried by the dyadic top row -/

/-- The complexified `m`th moment of the depth-`k` dyadic density row.  It is defined as the
complexification of the real moment so that conjugation is definitionally transparent. -/
def thetaSquareIndexDyadicComplexMoment (m k : ℕ) : ℂ :=
  ((∫ x : ℝ in Ioi 0,
    x ^ m * thetaSquareIndexDyadicDensity k x : ℝ) : ℂ)

theorem thetaSquareIndexDyadicComplexMoment_conj (m k : ℕ) :
    (starRingEnd ℂ) (thetaSquareIndexDyadicComplexMoment m k) =
      thetaSquareIndexDyadicComplexMoment m k := by
  simp [thetaSquareIndexDyadicComplexMoment]

/-- Haar-normalized products of two complexified moments vanish. -/
theorem tendsto_thetaSquareIndexDyadicWeightedComplexMomentProduct_zero
    (m n : ℕ) :
    Tendsto (fun k : ℕ =>
      (2 : ℂ) ^ k * thetaSquareIndexDyadicComplexMoment m k *
        thetaSquareIndexDyadicComplexMoment n k) atTop (nhds 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_thetaSquareIndexDyadicWeightedMomentProduct_zero m n)
  convert h using 1
  funext k
  unfold thetaSquareIndexDyadicComplexMoment
    thetaSquareIndexDyadicWeightedMomentProduct
  simp only [Function.comp_apply]
  push_cast
  ring

/-- An arbitrary finite complex linear packet of dyadic top-row moments. -/
def thetaSquareIndexDyadicFiniteMomentPacket {ι : Type*}
    (s : Finset ι) (exponent : ι → ℕ) (coefficient : ι → ℂ)
    (k : ℕ) : ℂ :=
  ∑ i ∈ s, coefficient i *
    thetaSquareIndexDyadicComplexMoment (exponent i) k

/-- Any Haar-normalized product of two fixed finite moment packets vanishes.  This is the
finite-coefficient form needed for every fixed Taylor section. -/
theorem tendsto_thetaSquareIndexDyadicWeightedFiniteMomentPacketProduct_zero
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (m : ι → ℕ) (n : κ → ℕ) (a : ι → ℂ) (b : κ → ℂ) :
    Tendsto (fun k : ℕ =>
      (2 : ℂ) ^ k * thetaSquareIndexDyadicFiniteMomentPacket s m a k *
        thetaSquareIndexDyadicFiniteMomentPacket t n b k)
      atTop (nhds 0) := by
  have hpair : ∀ i ∈ s, ∀ j ∈ t,
      Tendsto (fun k : ℕ =>
        (a i * b j) *
          ((2 : ℂ) ^ k * thetaSquareIndexDyadicComplexMoment (m i) k *
            thetaSquareIndexDyadicComplexMoment (n j) k))
        atTop (nhds 0) := by
    intro i _hi j _hj
    simpa using (tendsto_const_nhds.mul
      (tendsto_thetaSquareIndexDyadicWeightedComplexMomentProduct_zero
        (m i) (n j)))
  have hsum : Tendsto (fun k : ℕ =>
      ∑ j ∈ t, ∑ i ∈ s,
        (a i * b j) *
          ((2 : ℂ) ^ k * thetaSquareIndexDyadicComplexMoment (m i) k *
            thetaSquareIndexDyadicComplexMoment (n j) k))
      atTop (nhds 0) := by
    simpa using tendsto_finset_sum t (fun j hj =>
      tendsto_finset_sum s (fun i hi => hpair i hi j hj))
  convert hsum using 1
  funext k
  unfold thetaSquareIndexDyadicFiniteMomentPacket
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem thetaSquareIndexDyadicComplexMoment_eq_integral (m k : ℕ) :
    thetaSquareIndexDyadicComplexMoment m k =
      ∫ x : ℝ in Ioi 0,
        (thetaSquareIndexDyadicDensity k x : ℂ) * (x : ℂ) ^ m := by
  unfold thetaSquareIndexDyadicComplexMoment
  rw [show (fun x : ℝ =>
      (thetaSquareIndexDyadicDensity k x : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * thetaSquareIndexDyadicDensity k x : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  exact (integral_ofReal (X := ℝ) (μ := volume.restrict (Ioi 0))
    (𝕜 := ℂ)).symm

theorem integrableOn_thetaSquareIndexDyadicDensity_mul_complexPower
    (m k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (thetaSquareIndexDyadicDensity k x : ℂ) * (x : ℂ) ^ m) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ =>
      ((x ^ m * thetaSquareIndexDyadicDensity k x : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_pow_mul_thetaSquareIndexDyadicDensity m k).ofReal
  convert h using 1
  funext x
  push_cast
  ring

/-- Integration against a dyadic row sends a finite source-power packet to its finite moment
packet exactly. -/
theorem integral_thetaSquareIndexDyadicDensity_mul_finitePowerPacket
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℂ) (k : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (thetaSquareIndexDyadicDensity k x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) =
      thetaSquareIndexDyadicFiniteMomentPacket s m a k := by
  rw [show (fun x : ℝ =>
      (thetaSquareIndexDyadicDensity k x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) =
      fun x : ℝ => ∑ i ∈ s,
        a i * ((thetaSquareIndexDyadicDensity k x : ℂ) * (x : ℂ) ^ m i) by
    funext x
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  rw [MeasureTheory.integral_finset_sum]
  · unfold thetaSquareIndexDyadicFiniteMomentPacket
    apply Finset.sum_congr rfl
    intro i _hi
    rw [MeasureTheory.integral_const_mul,
      ← thetaSquareIndexDyadicComplexMoment_eq_integral]
  · intro i _hi
    exact (integrableOn_thetaSquareIndexDyadicDensity_mul_complexPower
      (m i) k).const_mul (a i)

theorem thetaSquareIndexDyadicFiniteMomentPacket_conj
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℂ) (k : ℕ) :
    (starRingEnd ℂ) (thetaSquareIndexDyadicFiniteMomentPacket s m a k) =
      thetaSquareIndexDyadicFiniteMomentPacket s m
        (fun i => (starRingEnd ℂ) (a i)) k := by
  unfold thetaSquareIndexDyadicFiniteMomentPacket
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul, thetaSquareIndexDyadicComplexMoment_conj]

/-- Coefficient of `x^(2r+2)` in the finite theta-tail section. -/
def thetaCuspTailSecondSectionSourceCoefficient (z : ℂ) (r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * z ^ (2 * r) / (2 * r + 2).factorial

/-- Coefficient of `x^(2r+2)` in the spectral derivative of the section. -/
def thetaCuspTailSecondSectionDerivativeSourceCoefficient
    (z : ℂ) (r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * ((2 * r : ℕ) : ℂ) * z ^ (2 * r - 1) /
    (2 * r + 2).factorial

/-- Coefficient of `x^(2r+2)` in the spectral derivative of the core atom. -/
def thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient
    (z : ℂ) (r : ℕ) : ℂ :=
  -2 * z * thetaCuspTailSecondSectionSourceCoefficient z r -
    (z ^ 2 + 1 / 4) *
      thetaCuspTailSecondSectionDerivativeSourceCoefficient z r

/-- Dyadic moment packet representing the finite theta-tail section. -/
def thetaSquareIndexDyadicSectionMomentPacket
    (d : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  thetaSquareIndexDyadicFiniteMomentPacket (Finset.range (d + 1))
    (fun r => 2 * r + 2) (thetaCuspTailSecondSectionSourceCoefficient z) k

/-- Dyadic moment packet representing the spectral derivative of the finite core atom. -/
def thetaSquareIndexDyadicCoreAtomDerivativeMomentPacket
    (d : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  thetaSquareIndexDyadicFiniteMomentPacket (Finset.range (d + 1))
    (fun r => 2 * r + 2)
    (thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z) k

theorem thetaCuspTailSecondSection_eq_sourcePowerPacket
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSection d z x =
      ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondSectionSourceCoefficient z r *
          (x : ℂ) ^ (2 * r + 2) := by
  unfold thetaCuspTailSecondSection
    thetaCuspTailSecondSectionSourceCoefficient
  apply Finset.sum_congr rfl
  intro r _hr
  ring

theorem thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondCoreAtomDerivative d z x =
      ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
          (x : ℂ) ^ (2 * r + 2) := by
  unfold thetaCuspTailSecondCoreAtomDerivative
    thetaCuspTailSecondSection thetaCuspTailSecondSectionDerivative
    thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient
    thetaCuspTailSecondSectionSourceCoefficient
    thetaCuspTailSecondSectionDerivativeSourceCoefficient
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  push_cast
  ring

/-- The core value averaged against the depth-`k` square-index row. -/
def thetaSquareIndexDyadicCoreAtomAverage
    (d : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaSquareIndexDyadicDensity k x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x

/-- The core spectral derivative averaged against the depth-`k` square-index row. -/
def thetaSquareIndexDyadicCoreAtomDerivativeAverage
    (d : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaSquareIndexDyadicDensity k x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x

theorem thetaSquareIndexDyadicCoreAtomAverage_eq_momentPacket
    (d : ℕ) (z : ℂ) (k : ℕ) :
    thetaSquareIndexDyadicCoreAtomAverage d z k =
      thetaSquareIndexDyadicComplexMoment 0 k -
        (z ^ 2 + 1 / 4) *
          thetaSquareIndexDyadicSectionMomentPacket d z k := by
  unfold thetaSquareIndexDyadicCoreAtomAverage thetaCuspTailSecondCoreAtom
  simp_rw [thetaCuspTailSecondSection_eq_sourcePowerPacket]
  rw [show (fun x : ℝ =>
      (thetaSquareIndexDyadicDensity k x : ℂ) *
        (1 - (z ^ 2 + 1 / 4) *
          ∑ r ∈ Finset.range (d + 1),
            thetaCuspTailSecondSectionSourceCoefficient z r *
              (x : ℂ) ^ (2 * r + 2))) =
      fun x : ℝ =>
        (thetaSquareIndexDyadicDensity k x : ℂ) * (x : ℂ) ^ 0 -
          (z ^ 2 + 1 / 4) *
            ((thetaSquareIndexDyadicDensity k x : ℂ) *
              ∑ r ∈ Finset.range (d + 1),
                thetaCuspTailSecondSectionSourceCoefficient z r *
                  (x : ℂ) ^ (2 * r + 2)) by
    funext x
    simp only [pow_zero]
    ring]
  rw [integral_sub]
  · rw [MeasureTheory.integral_const_mul,
      ← thetaSquareIndexDyadicComplexMoment_eq_integral]
    unfold thetaSquareIndexDyadicSectionMomentPacket
    rw [integral_thetaSquareIndexDyadicDensity_mul_finitePowerPacket]
  · exact integrableOn_thetaSquareIndexDyadicDensity_mul_complexPower 0 k
  · have hp : IntegrableOn (fun x : ℝ =>
        (thetaSquareIndexDyadicDensity k x : ℂ) *
          ∑ r ∈ Finset.range (d + 1),
            thetaCuspTailSecondSectionSourceCoefficient z r *
              (x : ℂ) ^ (2 * r + 2)) (Ioi 0) := by
      rw [show (fun x : ℝ =>
          (thetaSquareIndexDyadicDensity k x : ℂ) *
            ∑ r ∈ Finset.range (d + 1),
              thetaCuspTailSecondSectionSourceCoefficient z r *
                (x : ℂ) ^ (2 * r + 2)) =
          fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
            thetaCuspTailSecondSectionSourceCoefficient z r *
              ((thetaSquareIndexDyadicDensity k x : ℂ) *
                (x : ℂ) ^ (2 * r + 2)) by
        funext x
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring]
      exact MeasureTheory.integrable_finset_sum _ fun r _hr =>
        (integrableOn_thetaSquareIndexDyadicDensity_mul_complexPower
          (2 * r + 2) k).const_mul
            (thetaCuspTailSecondSectionSourceCoefficient z r)
    exact hp.const_mul (z ^ 2 + 1 / 4)

theorem thetaSquareIndexDyadicCoreAtomDerivativeAverage_eq_momentPacket
    (d : ℕ) (z : ℂ) (k : ℕ) :
    thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k =
      thetaSquareIndexDyadicCoreAtomDerivativeMomentPacket d z k := by
  unfold thetaSquareIndexDyadicCoreAtomDerivativeAverage
    thetaSquareIndexDyadicCoreAtomDerivativeMomentPacket
  simp_rw [thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket]
  rw [integral_thetaSquareIndexDyadicDensity_mul_finitePowerPacket]

/-- For every fixed Taylor section and spectral point, the Haar-normalized top-row value/derivative
correlation tends to zero. -/
theorem tendsto_thetaSquareIndexDyadicWeightedCoreAverages_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun k : ℕ =>
      (2 : ℂ) ^ k * thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k *
        (starRingEnd ℂ) (thetaSquareIndexDyadicCoreAtomAverage d z k))
      atTop (nhds 0) := by
  let s := Finset.range (d + 1)
  let e : ℕ → ℕ := fun r => 2 * r + 2
  let a : ℕ → ℂ :=
    thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z
  let b : ℕ → ℂ := thetaCuspTailSecondSectionSourceCoefficient z
  have hD0 :=
    tendsto_thetaSquareIndexDyadicWeightedFiniteMomentPacketProduct_zero
      s ({0} : Finset ℕ) e id a (fun _ => 1)
  have hDS :=
    tendsto_thetaSquareIndexDyadicWeightedFiniteMomentPacketProduct_zero
      s s e e a (fun r => (starRingEnd ℂ) (b r))
  have h := hD0.sub (hDS.const_mul
    ((starRingEnd ℂ) (z ^ 2 + 1 / 4)))
  convert h using 1
  funext k
  rw [thetaSquareIndexDyadicCoreAtomDerivativeAverage_eq_momentPacket,
    thetaSquareIndexDyadicCoreAtomAverage_eq_momentPacket]
  rw [map_sub, map_mul, thetaSquareIndexDyadicComplexMoment_conj]
  unfold thetaSquareIndexDyadicCoreAtomDerivativeMomentPacket
    thetaSquareIndexDyadicSectionMomentPacket
  rw [thetaSquareIndexDyadicFiniteMomentPacket_conj]
  dsimp only [s, e, a, b]
  simp only [thetaSquareIndexDyadicFiniteMomentPacket,
    Finset.sum_singleton, id_eq, one_mul]
  ring

/-- One exact Haar step: a divisibility row is the positive exact-valuation square, minus the
parity-wavelet square, plus the next divisibility row. -/
theorem thetaSquareIndexDyadic_oneStep (k : ℕ) (x y : ℝ) :
    (2 : ℝ) ^ k *
        thetaSquareIndexDyadicDensity k x * thetaSquareIndexDyadicDensity k y =
      (2 : ℝ) ^ (k + 1) *
          thetaSquareIndexDyadicOddLayer k x * thetaSquareIndexDyadicOddLayer k y -
        (2 : ℝ) ^ k *
          thetaSquareIndexDyadicParityLayer k x * thetaSquareIndexDyadicParityLayer k y +
        (2 : ℝ) ^ (k + 1) *
          thetaSquareIndexDyadicDensity (k + 1) x *
            thetaSquareIndexDyadicDensity (k + 1) y := by
  unfold thetaSquareIndexDyadicOddLayer thetaSquareIndexDyadicParityLayer
  rw [pow_succ]
  ring

/-- Finite cofinal arithmetic polarization of the entire square-index packet.  The only remainder
is the row divisible by `2^N`, shifted to the positive cusp. -/
theorem thetaCuspTailSecondDensity_mul_dyadicHaarPolarization
    (N : ℕ) (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y =
      ∑ k ∈ Finset.range N,
        ((2 : ℝ) ^ (k + 1) *
            thetaSquareIndexDyadicOddLayer k x * thetaSquareIndexDyadicOddLayer k y -
          (2 : ℝ) ^ k *
            thetaSquareIndexDyadicParityLayer k x *
              thetaSquareIndexDyadicParityLayer k y) +
        (2 : ℝ) ^ N *
          thetaSquareIndexDyadicDensity N x * thetaSquareIndexDyadicDensity N y := by
  induction N with
  | zero => simp [thetaSquareIndexDyadicDensity_zero]
  | succ N ih =>
      rw [ih, Finset.sum_range_succ]
      rw [thetaSquareIndexDyadic_oneStep N x y]
      ring

/-- One signed dyadic Haar layer coupled to the exact oriented-current kernel. -/
def xiCTaylorThetaTailCoreDyadicHaarLayerKernel
    (d : ℕ) (z : ℂ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  ((2 : ℝ) ^ (k + 1) *
      thetaSquareIndexDyadicOddLayer k p.1 * thetaSquareIndexDyadicOddLayer k p.2 -
    (2 : ℝ) ^ k *
      thetaSquareIndexDyadicParityLayer k p.1 *
        thetaSquareIndexDyadicParityLayer k p.2) *
    xiCTaylorThetaTailCorePairCurrent d z p

/-- The sole top row left after `N` dyadic Haar splittings. -/
def xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
    (d : ℕ) (z : ℂ) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  ((2 : ℝ) ^ N *
      thetaSquareIndexDyadicDensity N p.1 * thetaSquareIndexDyadicDensity N p.2) *
    xiCTaylorThetaTailCorePairCurrent d z p

/-- Pointwise current-source polarization into cofinal dyadic Haar layers and one shifted top
row. -/
theorem xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_dyadicHaarPolarization
    (d : ℕ) (z : ℂ) (N : ℕ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p =
      (∑ k ∈ Finset.range N,
        xiCTaylorThetaTailCoreDyadicHaarLayerKernel d z k p) +
      xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z N p := by
  rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul,
    thetaCuspTailSecondDensity_mul_dyadicHaarPolarization]
  unfold xiCTaylorThetaTailCoreDyadicHaarLayerKernel
    xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
  rw [add_mul, Finset.sum_mul]

/-- Exact current-level cofinal arithmetic signed polarization. -/
theorem xiCTaylorThetaTailCore_current_eq_dyadicHaarPolarization
    (d : ℕ) (z : ℂ) (N : ℕ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∫ p : ℝ × ℝ,
          ((∑ k ∈ Finset.range N,
              xiCTaylorThetaTailCoreDyadicHaarLayerKernel d z k p) +
            xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z N p)
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_symmetricCorrelationIntegral]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply integral_congr_ae
  filter_upwards [] with p
  exact xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_dyadicHaarPolarization d z N p

/-- One square-index signed source pair coupled to the exact oriented-current kernel. -/
def xiCTaylorThetaTailCoreSquareIndexPolarizedPairKernel
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  thetaSquareIndexSignedPolarization q p *
    xiCTaylorThetaTailCorePairCurrent d z p

theorem xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_squareIndexPolarized
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p =
      xiCTaylorThetaTailCoreSquareIndexPolarizedPairKernel d z q p := by
  unfold xiCTaylorThetaTailCoreAtomPairCorrelationKernel
    xiCTaylorThetaTailCoreSquareIndexPolarizedPairKernel
  rw [thetaCuspTailSecondDensityAtom_mul_eq_squareIndexSignedPolarization]

/-- Pointwise, the complete symmetric current source is the full signed square-index packet. -/
theorem xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_squareIndexPolarized
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p =
      ∑' q : ℕ × ℕ,
        xiCTaylorThetaTailCoreSquareIndexPolarizedPairKernel d z q p := by
  rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_atomPair]
  apply tsum_congr
  intro q
  exact xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_squareIndexPolarized d z q p

/-- Exact current-level lift of the independent signed square-index polarization. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_squareIndexPolarizedPairIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' q : ℕ × ℕ,
          ∫ p : ℝ × ℝ,
            xiCTaylorThetaTailCoreSquareIndexPolarizedPairKernel d z q p
              ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_tsum_atomPairIntegral]
  congr 1
  apply tsum_congr
  intro q
  apply integral_congr_ae
  filter_upwards [] with p
  exact xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_squareIndexPolarized d z q p

end

end RHTower
