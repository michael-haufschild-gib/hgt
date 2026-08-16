import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSummability
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

open Complex ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace RHTower.Sieve

private def zetaFourNat : ArithmeticFunction ℕ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * ArithmeticFunction.zeta) *
    (ArithmeticFunction.zeta * ArithmeticFunction.zeta)

private def zetaFourComplex : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) *
    (ArithmeticFunction.zeta * ArithmeticFunction.zeta)

private theorem zetaFourNat_cast (n : ℕ) :
    ((zetaFourNat n : ℕ) : ℂ) = zetaFourComplex n := by
  change (((zetaFourNat : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) = _
  unfold zetaFourNat zetaFourComplex
  simp only [ArithmeticFunction.natCoe_mul]

private theorem card_divisors_sq_le_zetaFourNat (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 2 ≤ zetaFourNat n := by
  have h := card_divisors_pow_le_zeta_pow 2 n hn
  simpa only [zetaFourNat, show (2 ^ 2 : ℕ) = 4 by norm_num,
    pow_succ, pow_zero, one_mul, mul_assoc] using h

private theorem LSeries_zetaFourComplex_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => zetaFourComplex n) s = riemannZeta s ^ 4 := by
  have hz : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hz2 := ArithmeticFunction.LSeriesSummable_mul hz hz
  have hzval : LSeries
      (fun n : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s =
        riemannZeta s := by
    simpa using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  unfold zetaFourComplex
  rw [ArithmeticFunction.LSeries_mul' hz2 hz2,
    ArithmeticFunction.LSeries_mul' hz hz, hzval]
  ring

theorem summable_divisorSquare_mul_rpow_neg
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable fun n : ℕ =>
      (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-sigma) := by
  have hsComplex : 1 < ((sigma : ℂ)).re := by simpa
  have hnorm := summable_norm_iff.mpr
    (divisorSquareLSeriesSummable (s := (sigma : ℂ)) hsComplex)
  apply hnorm.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos hnpos, Complex.ofReal_re]
    push_cast
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem tsum_divisorSquare_rpow_le_near_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-sigma)) ≤
      (1 + 1 / (sigma - 1)) ^ 4 := by
  let f : ℕ → ℝ := fun n =>
    (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-sigma)
  let g : ℕ → ℝ := fun n => (zetaFourNat n : ℝ) * (n : ℝ) ^ (-sigma)
  have hsComplex : 1 < ((sigma : ℂ)).re := by simpa
  have hf : Summable f := by
    simpa only [f] using summable_divisorSquare_mul_rpow_neg hsigma
  have hgComplex : LSeriesSummable
      (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) (sigma : ℂ) := by
    have hcoeff : (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) =
        fun n : ℕ => zetaFourComplex n := by
      funext n
      exact zetaFourNat_cast n
    rw [hcoeff]
    have hz : LSeriesSummable
        (fun n : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)
          (sigma : ℂ) :=
      ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsComplex
    exact ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul hz hz)
      (ArithmeticFunction.LSeriesSummable_mul hz hz)
  have hg : Summable g := by
    have hnorm := summable_norm_iff.mpr hgComplex
    apply hnorm.congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [g, zetaFourNat, LSeries.term]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos hnpos, Complex.ofReal_re]
      dsimp only [g]
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f, g, zetaFourNat]
    · exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_divisors_sq_le_zetaFourNat n hn)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsum := hf.tsum_le_tsum hfg hg
  have hg0 : 0 ≤ ∑' n, g n := tsum_nonneg fun n => by
    dsimp only [g]
    positivity
  have hcast : ((∑' n, g n : ℝ) : ℂ) =
      LSeries (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) (sigma : ℂ) := by
    rw [Complex.ofReal_tsum g]
    unfold LSeries
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [g, zetaFourNat, LSeries.term]
    · rw [LSeries.term_of_ne_zero hn]
      dsimp only [g]
      have hpowCast : (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) =
          (n : ℂ) ^ (-((sigma : ℝ) : ℂ)) := by
        have h := Complex.ofReal_cpow (x := (n : ℝ)) (Nat.cast_nonneg n) (-sigma)
        rw [h, Complex.ofReal_natCast]
        congr 1
        push_cast
        ring
      rw [Complex.ofReal_mul, Complex.ofReal_natCast, hpowCast,
        Complex.cpow_neg, div_eq_mul_inv]
  have hsumNorm : (∑' n, g n) =
      ‖LSeries (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) (sigma : ℂ)‖ := by
    rw [← hcast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
  have hseries :
      LSeries (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) (sigma : ℂ) =
        riemannZeta (sigma : ℂ) ^ 4 := by
    have hcoeff : (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ)) =
        fun n : ℕ => zetaFourComplex n := by
      funext n
      exact zetaFourNat_cast n
    rw [hcoeff]
    exact LSeries_zetaFourComplex_eq hsComplex
  have hzeta := norm_riemannZeta_real_le hsigma
  calc
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-sigma)) =
        ∑' n, f n := by rfl
    _ ≤ ∑' n, g n := hsum
    _ = ‖LSeries (fun n : ℕ => ((zetaFourNat n : ℕ) : ℂ))
        (sigma : ℂ)‖ := hsumNorm
    _ = ‖riemannZeta (sigma : ℂ)‖ ^ 4 := by rw [hseries, norm_pow]
    _ ≤ (1 + 1 / (sigma - 1)) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hzeta 4

end RHTower.Sieve
