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
open Polynomial Real Set MeasureTheory Complex

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

/-- The dyadic translate is exactly the full row of square indices divisible by `2^k`. -/
theorem thetaSquareIndexDyadicDensity_eq_multiples_row (k : ℕ) (x : ℝ) :
    (∑' m : ℕ+,
      thetaCuspTailSecondDensityAtom
        ((⟨2 ^ k, pow_pos (by norm_num) k⟩ : ℕ+) * m) x) =
      thetaSquareIndexDyadicDensity k x := by
  simpa [thetaSquareIndexDyadicDensity] using
    (tsum_thetaCuspTailSecondDensityAtom_pnat_mul
      (⟨2 ^ k, pow_pos (by norm_num) k⟩ : ℕ+) x)

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
