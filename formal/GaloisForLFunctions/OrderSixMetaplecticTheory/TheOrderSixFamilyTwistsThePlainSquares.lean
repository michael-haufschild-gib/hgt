import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFirstMomentIsReal
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicThetaFunctionIsConjugationSymmetric
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists

/-!
# The order-six family twists the plain squares

Since `(ω²λ²)² = 9` (`omega_sq_mul_lambda_sq_sq`), the cubic symbol of `9` is the square of the symbol of
`ω²λ²`, and the coefficient of STCC's 3-adic twist `S_{ω²λ²}(w) = Σ_A (ω²λ²/c_A)₃² σ(A) N(A)^{−w}` is the plain
conjugate square of the normalized cubic Gauss sum (`twisted_coefficient_eq_plain_square`):

`(ω²λ²/c)₃² σ(c) = \overline{G̃(c)}²`.

So `S_{ω²λ²}` is the plain mean of the squared Gauss sums, and the order-six weight is its 2-adic Weil twist
(`orderSixWeight_eq_conj_plain`): `ω₆(c) = Γ(c) χ₂(c) \overline{(ω²λ²/c)₃² σ(c)}`. The natural partner of the
order-six family is `S_{ω²λ²}`, not `S₁`.

In the Rankin–Selberg series of `θ²` the twist `S_{ω²λ²}` carries the weight `(T(ω²λ²)/T(1))²`, a nonnegative real
number (`plain_square_weight_nonneg`): `ω²λ²` is fixed by conjugation and the theta function is conjugation
symmetric.
-/

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

theorem lambda_sq_eq' : lambda ^ 2 = -3 * omega := by
  unfold lambda
  linear_combination omega_sq_add

/-- `(ω²λ²)² = 9`. -/
theorem omega_sq_mul_lambda_sq_sq : (omega ^ 2 * lambda ^ 2) ^ 2 = 9 := by
  rw [mul_pow, lambda_sq_eq']
  linear_combination 9 * (omega ^ 3 + 1) * omega_primitive.pow_eq_one

/-- `(9/c)₃ = (ω²λ²/c)₃²`. -/
theorem symbol_nine_eq_sq (c : O) : symbol 9 c = symbol (omega ^ 2 * lambda ^ 2) c ^ 2 := by
  rw [← omega_sq_mul_lambda_sq_sq, sq (omega ^ 2 * lambda ^ 2), symbol_mul_numerator]
  ring

theorem nine_coprime_of_primary {c : O} (hc : lambda ^ 2 ∣ c - 1) : IsCoprime (9 : O) c := by
  have hc3 : IsCoprime (3 : O) c := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 _ hc
  convert hc3.mul_left hc3 using 1
  norm_num

/-- **The coefficient of `S_{ω²λ²}` is the plain conjugate square:** `(ω²λ²/c)₃² σ(c) = \overline{G̃(c)}²`. -/
theorem twisted_coefficient_eq_plain_square (c : O) (hc : lambda ^ 2 ∣ c - 1) :
    ringComplex (symbol (omega ^ 2 * lambda ^ 2) c) ^ 2 * thetaSquareWeight (Ideal.span {c}) =
      star (normalizedCubicUnitGauss c) ^ 2 := by
  have h3 := symbol_cube_of_isCoprime 9 c hc (nine_coprime_of_primary hc)
  set s := symbol (omega ^ 2 * lambda ^ 2) c
  have hs6 : ringComplex s ^ 6 = 1 := by
    rw [← map_pow, show s ^ 6 = (s ^ 2) ^ 3 by ring, ← symbol_nine_eq_sq, h3, map_one]
  unfold thetaSquareWeight
  rw [primaryIdealGenerator_span c (primary_ne_zero c hc) hc, symbol_nine_eq_sq, map_pow]
  calc ringComplex s ^ 2 * (ringComplex s ^ 2 * star (normalizedCubicUnitGauss c)) ^ 2
      = ringComplex s ^ 6 * star (normalizedCubicUnitGauss c) ^ 2 := by ring
    _ = _ := by rw [hs6, one_mul]

/-- **The order-six weight is the 2-adic Weil twist of the conjugate coefficient of `S_{ω²λ²}`.** -/
theorem orderSixWeight_eq_conj_plain (c : O) (hc : lambda ^ 2 ∣ c - 1) :
    orderSixWeight c = fixedDualAverage c * cubicTwoChar c *
      star (ringComplex (symbol (omega ^ 2 * lambda ^ 2) c) ^ 2 * thetaSquareWeight (Ideal.span {c})) := by
  rw [twisted_coefficient_eq_plain_square c hc, star_pow, star_star]
  rfl

/-- On ideals: the order-six coefficient of a squarefree odd row is the Weil twist of the conjugate
coefficient of `S_{ω²λ²}`. -/
theorem orderSixCoefficient_eq_conj_plain (A : Ideal O) (hA : Squarefree A)
    (hg : primaryIdealGenerator A ≠ 0) (h2 : ¬ (2 : O) ∣ primaryIdealGenerator A) :
    orderSixCoefficient A = fixedDualAverage (primaryIdealGenerator A) * cubicTwoChar (primaryIdealGenerator A) *
      star (ringComplex (symbol (omega ^ 2 * lambda ^ 2) (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A) := by
  obtain ⟨hspan, hp⟩ := primaryIdealGenerator_spec A hg
  unfold orderSixCoefficient
  rw [if_pos ⟨hA, hg, h2⟩, orderSixWeight_eq_conj_plain _ hp, hspan]

/-- **The Rankin–Selberg weight of `S_{ω²λ²}` is a nonnegative real number:** `(T(ω²λ²)/T(1))² ≥ 0`. -/
theorem plain_square_weight_nonneg :
    ((rationalSourceResidualFourierCoefficient (omega ^ 2 * lambda ^ 2) /
        rationalSourceResidualFourierCoefficient 1) ^ 2).im = 0 ∧
      0 ≤ ((rationalSourceResidualFourierCoefficient (omega ^ 2 * lambda ^ 2) /
        rationalSourceResidualFourierCoefficient 1) ^ 2).re := by
  have h1 := rationalSourceResidualFourierCoefficient_conj 1 one_ne_zero
  rw [map_one] at h1
  have h2 := rationalSourceResidualFourierCoefficient_omega_sq_lambda_sq_star
  set x := rationalSourceResidualFourierCoefficient (omega ^ 2 * lambda ^ 2) /
    rationalSourceResidualFourierCoefficient 1
  have hx : (starRingEnd ℂ) x = x := by
    change star x = x
    rw [star_div₀, h2, ← h1]
  rw [← Complex.conj_eq_iff_re.mp hx]
  refine ⟨by rw [← Complex.ofReal_pow, Complex.ofReal_im], ?_⟩
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

end GaloisForLFunctions.OrderSixMetaplecticTheory
