import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicPerronError
import GaloisForLFunctions.RHTower.Sieve.PerronShortInterval
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound

/-!
# Factorized short-interval Perron formula for Heath--Brown boxes

This module identifies the finite coefficient polynomial inside Perron's integral with the exact
product of the individual dyadic Möbius, zeta, and logarithm Dirichlet polynomials.  The alternating
binomial scalar stays outside those factors.  This is the literal finite-product integrand used by
the Maynard/Heath--Brown large-values argument.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set

/-- Exact signed product attached to one dyadic term box. -/
def heathBrownDyadicTermProduct
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ (m + k + 1) * (k.choose m : ℂ) *
    ((∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) (a i))) s) *
      (∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (b i))) s) *
      LSeries (complexCoeff (arithmeticDyadicBlock
        (coeffTrunc ArithmeticFunction.log X) q)) s)

theorem LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownDyadicTermBox L X k m a b q)) s := by
  have hneg : LSeriesSummable
      (complexCoeff (-1 : ArithmeticFunction ℝ)) s := by
    simpa using LSeriesSummable_complexCoeff_intCast (-1) s
  have hchoose := LSeriesSummable_complexCoeff_natCast (k.choose m) s
  have hcore := LSeriesSummable_complexCoeff_heathBrownDyadicCoreBox
    L X (k - m) a b q s
  rw [heathBrownDyadicTermBox]
  exact LSeriesSummable_complexCoeff_mul
    (LSeriesSummable_complexCoeff_mul
      (LSeriesSummable_complexCoeff_pow hneg (m + k + 1)) hchoose) hcore

/-- **L-series of a signed box is its literal `2j`-factor dyadic product.** -/
theorem LSeries_heathBrownDyadicTermBox
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownDyadicTermBox L X k m a b q)) s =
      heathBrownDyadicTermProduct L X k m a b q s := by
  have hneg : LSeriesSummable
      (complexCoeff (-1 : ArithmeticFunction ℝ)) s := by
    simpa using LSeriesSummable_complexCoeff_intCast (-1) s
  have hnegSeries : LSeries (complexCoeff (-1 : ArithmeticFunction ℝ)) s = (-1 : ℂ) := by
    simpa using LSeries_complexCoeff_intCast (-1) s
  have hnegpow := LSeriesSummable_complexCoeff_pow hneg (m + k + 1)
  have hchoose := LSeriesSummable_complexCoeff_natCast (k.choose m) s
  have hcore := LSeriesSummable_complexCoeff_heathBrownDyadicCoreBox
    L X (k - m) a b q s
  rw [heathBrownDyadicTermBox,
    LSeries_complexCoeff_mul (LSeriesSummable_complexCoeff_mul hnegpow hchoose) hcore,
    LSeries_complexCoeff_mul hnegpow hchoose,
    LSeries_complexCoeff_pow hneg (m + k + 1), hnegSeries,
    LSeries_complexCoeff_natCast (k.choose m) s,
    LSeries_heathBrownDyadicCoreBox]
  rfl

/-- The finite coefficient sum over the exact upper support equals the box L-series. -/
theorem sum_Icc_heathBrownDyadicTermBox_cpow_eq_LSeries
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (w : ℂ) :
    let M := heathBrownDyadicCoreUpper (k - m) a b q
    ∑ n ∈ Finset.Icc 1 M,
        complexCoeff (heathBrownDyadicTermBox L X k m a b q) n * (n : ℂ) ^ (-w) =
      LSeries (complexCoeff (heathBrownDyadicTermBox L X k m a b q)) w := by
  dsimp only
  let F := heathBrownDyadicTermBox L X k m a b q
  let M := heathBrownDyadicCoreUpper (k - m) a b q
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro hzero
      apply hn
      simp [complexCoeff_apply, hzero]
    exact upperSupported_heathBrownDyadicTermBox L X k m a b q n hnF
  simpa [F, M] using sum_mul_cpow_neg_eq_LSeries hs0 hsupp w

/-- **Perron prefix integral with the fully factorized dyadic product inside.** -/
theorem perronPrefixIntegral_heathBrownDyadicTermBox_eq
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q N : ℕ) (σ T : ℝ) :
    let M := heathBrownDyadicCoreUpper (k - m) a b q
    let c := complexCoeff (heathBrownDyadicTermBox L X k m a b q)
    perronPrefixIntegral c M N σ T =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        heathBrownDyadicTermProduct L X k m a b q ((σ : ℂ) + (t : ℝ) * I) *
          (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
            / ((σ : ℂ) + (t : ℝ) * I)) := by
  dsimp only
  rw [perronPrefixIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only
  rw [sum_Icc_heathBrownDyadicTermBox_cpow_eq_LSeries,
    LSeries_heathBrownDyadicTermBox]

end RHTower.Sieve
