import GaloisForLFunctions.RHTower.InfiniteMobiusLaplaceMultiplier

/-!
# The all-prime signed Möbius Schur multiplier on the closed right half-plane

The finite-aperture Schur bound is already formalized in `MobiusFiniteSchurTransfer.lean`.  This
module carries the *cofinal* statement of
`mobius-signed-coisometry-schur-transfer-law.md`, equations `(9)`--`(13)`:

```text
tau_omega(z) = sum_d mu(d) P_omega(d) d^(-z)
             = zeta(2 sigma)/(zeta(sigma) zeta(sigma+z)) ,       Re z >= 0,
|tau_omega(z)| <= 1 ,                                            Re z >= 0,
tau_omega(0)   = zeta(2 sigma)/zeta(sigma)^2 .
```

The contraction bound is the exact probabilistic one: `tau_omega` is a signed average of unimodular
characters against the squarefree probability measure, so its modulus never exceeds the total mass
`1`.  This is the complex-frequency form of the already formalized real-frequency multiplier
`infiniteMobiusLaplaceMultiplier`.
-/

open Complex ArithmeticFunction LSeries
open scoped LSeries.notation Moebius

noncomputable section
namespace RHTower

/-- The signed squarefree Schur summand at complex frequency `z`. -/
def mobiusSchurTerm (sigma : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  signedMobiusProbability sigma n * (n : ℂ) ^ (-z)

/-- The all-prime signed Möbius Schur multiplier. -/
def mobiusSchurTransfer (sigma : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, mobiusSchurTerm sigma z n

theorem mobiusSchurTerm_zero (sigma : ℝ) (z : ℂ) : mobiusSchurTerm sigma z 0 = 0 := by
  simp [mobiusSchurTerm, signedMobiusProbability]

/-- Every summand is dominated by the squarefree probability throughout the closed right
half-plane. -/
theorem norm_mobiusSchurTerm_le
    {sigma : ℝ} (hsigma : 1 < sigma) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖mobiusSchurTerm sigma z n‖ ≤ squarefreeMobiusProbability sigma n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [mobiusSchurTerm_zero, norm_zero]
    exact squarefreeMobiusProbability_nonneg hsigma 0
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [mobiusSchurTerm, norm_mul, norm_signedMobiusProbability hsigma,
      norm_natCast_cpow_of_pos hn]
    have hpow : (n : ℝ) ^ (-z).re ≤ 1 := by
      have : (-z).re ≤ 0 := by simpa using hz
      calc (n : ℝ) ^ (-z).re ≤ (n : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 this
        _ = 1 := Real.rpow_zero _
    have hP : 0 ≤ squarefreeMobiusProbability sigma n :=
      squarefreeMobiusProbability_nonneg hsigma n
    nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) (-z).re]

theorem summable_mobiusSchurTerm
    {sigma : ℝ} (hsigma : 1 < sigma) {z : ℂ} (hz : 0 ≤ z.re) :
    Summable (mobiusSchurTerm sigma z) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_mobiusSchurTerm_le hsigma hz) (summable_squarefreeMobiusProbability hsigma)

/-- **Card `(11)`--`(12)`.**  The all-prime signed Möbius multiplier is a Schur function of the
closed right half-plane. -/
theorem norm_mobiusSchurTransfer_le_one
    {sigma : ℝ} (hsigma : 1 < sigma) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖mobiusSchurTransfer sigma z‖ ≤ 1 := by
  have hnormsummable : Summable (fun n : ℕ => ‖mobiusSchurTerm sigma z n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_mobiusSchurTerm_le hsigma hz) (summable_squarefreeMobiusProbability hsigma)
  calc ‖mobiusSchurTransfer sigma z‖ ≤ ∑' n : ℕ, ‖mobiusSchurTerm sigma z n‖ :=
        norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℕ, squarefreeMobiusProbability sigma n :=
        Summable.tsum_mono hnormsummable (summable_squarefreeMobiusProbability hsigma)
          (norm_mobiusSchurTerm_le hsigma hz)
    _ = 1 := tsum_squarefreeMobiusProbability hsigma

/-- Each summand is the normalized Möbius `L`-series term at the shifted parameter. -/
theorem mobiusSchurTerm_eq_LSeries_term (sigma : ℝ) (z : ℂ) (n : ℕ) :
    mobiusSchurTerm sigma z n =
      (squarefreeMobiusTotal sigma : ℂ)⁻¹ * LSeries.term (↗μ) ((sigma : ℂ) + z) n := by
  by_cases hn0 : n = 0
  · subst n
    simp [mobiusSchurTerm, signedMobiusProbability]
  · by_cases hsq : Squarefree n
    · rw [mobiusSchurTerm, signedMobiusProbability, squarefreeMobiusProbability,
        squarefreeMobiusMass, if_pos hsq, LSeries.term_of_ne_zero hn0]
      rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_cast, Complex.cpow_neg]
      rw [Complex.cpow_add (sigma : ℂ) z (Nat.cast_ne_zero.mpr hn0), Complex.cpow_neg]
      rw [show (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) by norm_cast]
      field_simp
    · rw [mobiusSchurTerm, signedMobiusProbability, squarefreeMobiusProbability,
        squarefreeMobiusMass, if_neg hsq,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq,
        LSeries.term_of_ne_zero hn0]
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- **Card `(9)`.**  The exact Schur transfer function. -/
theorem mobiusSchurTransfer_eq_zetaRatio
    {sigma : ℝ} (hsigma : 1 < sigma) {z : ℂ} (hz : 0 ≤ z.re) :
    mobiusSchurTransfer sigma z =
      riemannZeta (2 * (sigma : ℂ)) /
        (riemannZeta (sigma : ℂ) * riemannZeta ((sigma : ℂ) + z)) := by
  have hshift : 1 < ((sigma : ℂ) + z).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hsigmaZeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hshiftZeta : riemannZeta ((sigma : ℂ) + z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hshift
  have htwo : 1 < (2 * (sigma : ℂ)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  have htwoZeta : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwo
  have hsum : mobiusSchurTransfer sigma z =
      (squarefreeMobiusTotal sigma : ℂ)⁻¹ * L ↗μ ((sigma : ℂ) + z) := by
    unfold mobiusSchurTransfer
    rw [show (∑' n : ℕ, mobiusSchurTerm sigma z n) =
        ∑' n : ℕ, (squarefreeMobiusTotal sigma : ℂ)⁻¹ *
          LSeries.term (↗μ) ((sigma : ℂ) + z) n from
      tsum_congr (mobiusSchurTerm_eq_LSeries_term sigma z)]
    rw [tsum_mul_left]
    rfl
  rw [hsum, LSeries_moebius_eq_inv_riemannZeta hshift,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
  field_simp

/-- **Card `(13)`.**  The value at the constant character. -/
theorem mobiusSchurTransfer_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    mobiusSchurTransfer sigma 0 =
      riemannZeta (2 * (sigma : ℂ)) / riemannZeta (sigma : ℂ) ^ 2 := by
  rw [mobiusSchurTransfer_eq_zetaRatio hsigma (by simp), add_zero]
  ring

/-- Consistency: on the real Laplace ray the complex multiplier is the already formalized
real-frequency multiplier. -/
theorem mobiusSchurTransfer_ofReal
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    mobiusSchurTransfer sigma ((Real.pi * x : ℝ) : ℂ) =
      infiniteMobiusLaplaceMultiplier sigma x := by
  have hre : (0 : ℝ) ≤ (((Real.pi * x : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    positivity
  rw [mobiusSchurTransfer_eq_zetaRatio hsigma hre,
    infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigma hx]
  congr 2
  push_cast
  ring

end RHTower
