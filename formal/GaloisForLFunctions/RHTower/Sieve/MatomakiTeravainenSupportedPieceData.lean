import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainScaleSupport

/-!
# Proposition 2.2 data from supported convolution factors

Once a box factor is proved to have the required exact support and divisor bound, these
constructors package it into the literal Type-I or Type-I/II structure without changing the
arithmetic function.
-/

namespace RHTower.Sieve

open ArithmeticFunction

noncomputable section

/-- Package one dyadically supported long factor and one narrow constant factor as Type I. -/
def mtTypeIPieceDataOfSupported
    {X Y delta epsilon M1 M2 : ℝ} (F : ArithmeticFunction ℂ)
    (hM1 : 0 < M1) (hM2 : 0 < M2)
    (_hFsupport : MTRealScaleSupported F M1 (2 * M1))
    (hFbounded : MTPolynomialDivisorBounded (fun n => F n))
    (hM1le : M1 ≤ X ^ (1 / 2 + epsilon))
    (hproduct : Y / 2 < M1 * M2 ∧ M1 * M2 ≤ 4 * Y) :
    MTTypeIPieceData X Y delta epsilon where
  M₁ := M1
  M₂ := M2
  α := fun n => F n
  M₁_pos := hM1
  M₂_pos := hM2
  α_divisorBounded := hFbounded
  M₁_le := hM1le
  product_mem := hproduct

theorem mtTypeIPieceDataOfSupported_pieceAF_eq
    {X Y delta epsilon M1 M2 : ℝ} (F : ArithmeticFunction ℂ)
    (hM1 : 0 < M1) (hM2 : 0 < M2)
    (hFsupport : MTRealScaleSupported F M1 (2 * M1))
    (hFbounded : MTPolynomialDivisorBounded (fun n => F n))
    (hM1le : M1 ≤ X ^ (1 / 2 + epsilon))
    (hproduct : Y / 2 < M1 * M2 ∧ M1 * M2 ≤ 4 * Y) :
    (mtTypeIPieceDataOfSupported (delta := delta) F hM1 hM2 hFsupport hFbounded
      hM1le hproduct).pieceAF =
      F * mtRealIntervalAF (fun _ => 1) M2 ((1 + delta) * M2) := by
  change mtRealIntervalAF (fun n => F n) M1 (2 * M1) *
      mtRealIntervalAF (fun _ => 1) M2 ((1 + delta) * M2) = _
  rw [mtRealIntervalAF_coe_eq_of_scaleSupported hFsupport]

/-- Package two dyadically supported factors and one narrow constant factor as Type I/II. -/
def mtTypeI_II_PieceDataOfSupported
    {X Y delta epsilon M1 M2 M3 : ℝ}
    (F G : ArithmeticFunction ℂ)
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (_hFsupport : MTRealScaleSupported F M1 (2 * M1))
    (_hGsupport : MTRealScaleSupported G M2 (2 * M2))
    (hFbounded : MTPolynomialDivisorBounded (fun n => F n))
    (hGbounded : MTPolynomialDivisorBounded (fun n => G n))
    (hsquare : M1 ^ 2 * M2 ≤ X ^ (1 - epsilon))
    (hM2le : M2 ≤ X ^ (1 / 4 - epsilon))
    (hproduct : Y / 2 < M1 * M2 * M3 ∧ M1 * M2 * M3 ≤ 4 * Y) :
    MTTypeI_II_PieceData X Y delta epsilon where
  M₁ := M1
  M₂ := M2
  M₃ := M3
  α := fun n => F n
  β := fun n => G n
  M₁_pos := hM1
  M₂_pos := hM2
  M₃_pos := hM3
  α_divisorBounded := hFbounded
  β_divisorBounded := hGbounded
  square_product_le := hsquare
  M₂_le := hM2le
  product_mem := hproduct

theorem mtTypeI_II_PieceDataOfSupported_pieceAF_eq
    {X Y delta epsilon M1 M2 M3 : ℝ}
    (F G : ArithmeticFunction ℂ)
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hFsupport : MTRealScaleSupported F M1 (2 * M1))
    (hGsupport : MTRealScaleSupported G M2 (2 * M2))
    (hFbounded : MTPolynomialDivisorBounded (fun n => F n))
    (hGbounded : MTPolynomialDivisorBounded (fun n => G n))
    (hsquare : M1 ^ 2 * M2 ≤ X ^ (1 - epsilon))
    (hM2le : M2 ≤ X ^ (1 / 4 - epsilon))
    (hproduct : Y / 2 < M1 * M2 * M3 ∧ M1 * M2 * M3 ≤ 4 * Y) :
    (mtTypeI_II_PieceDataOfSupported (delta := delta)
      F G hM1 hM2 hM3 hFsupport hGsupport
      hFbounded hGbounded hsquare hM2le hproduct).pieceAF =
      (F * G) * mtRealIntervalAF (fun _ => 1) M3 ((1 + delta) * M3) := by
  change (mtRealIntervalAF (fun n => F n) M1 (2 * M1) *
      mtRealIntervalAF (fun n => G n) M2 (2 * M2)) *
        mtRealIntervalAF (fun _ => 1) M3 ((1 + delta) * M3) = _
  rw [mtRealIntervalAF_coe_eq_of_scaleSupported hFsupport,
    mtRealIntervalAF_coe_eq_of_scaleSupported hGsupport]

end

end RHTower.Sieve
