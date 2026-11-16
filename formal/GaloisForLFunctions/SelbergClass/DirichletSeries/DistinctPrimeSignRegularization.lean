import GaloisForLFunctions.SelbergClass.DirichletSeries.DistinctPrimeSignCorrection
import GaloisForLFunctions.SelbergClass.DirichletSeries.DistinctPrimeSignEulerProduct
import GaloisForLFunctions.BezoutValuationIncidence.SingularSeries.TwinPrimeConstant
import GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The distinct-prime continuation and its double zero

The arithmetic Dirichlet series factors into reciprocal zeta, the prime-two
correction and a normally convergent odd-prime product. At one, the last
factor is half the gap-two Hardy–Littlewood singular series. The first two
factors have simple zeros, giving the exact curvature `8 C₂ log 2`.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass

private def correctionPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime-two correction supplies the extra zero at one. -/
def distinctPrimeTwoCorrection (s : ℂ) : ℂ :=
  (1 - 2 * distinctPrimeDecay correctionPrimeTwo s) /
    (1 - distinctPrimeDecay correctionPrimeTwo s) ^ 2

/-- The regularized Euler factorization, using the removable value of reciprocal zeta. -/
def distinctPrimeSignContinuation (s : ℂ) : ℂ :=
  distinctPrimeTwoCorrection s * RHTower.Sieve.invZeta s * oddPrimeCorrection s

/-- The isolated prime-two factor vanishes at one. -/
theorem distinctPrimeTwoCorrection_one : distinctPrimeTwoCorrection 1 = 0 := by
  norm_num [distinctPrimeTwoCorrection, distinctPrimeDecay_one, correctionPrimeTwo]

/-- The reciprocal-zeta zero supplies one of the two vanishing factors. -/
theorem distinctPrimeSignContinuation_one : distinctPrimeSignContinuation 1 = 0 := by
  simp only [distinctPrimeSignContinuation, RHTower.Sieve.invZeta_one, mul_zero, zero_mul]

/-- The factorization continues the actual arithmetic series on its domain of convergence. -/
theorem distinctPrimeSignContinuation_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    distinctPrimeSignContinuation s =
      LSeries (fun n => (distinctPrimeSign n : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith only [hs]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hbase : HasProd (fun p => 1 - distinctPrimeDecay p s) (RHTower.Sieve.invZeta s) := by
    rw [RHTower.Sieve.invZeta_eq_inv hs1]
    exact (RHTower.hasProd_one_sub_primeCpow_neg hs).congr_fun
      (fun p => by rw [distinctPrimeDecay_eq_cpow])
  have htwo := hasProd_ite_eq correctionPrimeTwo (distinctPrimeTwoCorrection s)
  have hproduct := (htwo.mul hbase).mul
    (hasProd_oddPrimeCorrection (s := s) (by linarith only [hs]))
  have hlocal : HasProd (fun p : Nat.Primes =>
      (1 - 2 * distinctPrimeDecay p s) / (1 - distinctPrimeDecay p s))
      (distinctPrimeSignContinuation s) := by
    apply hproduct.congr_fun
    intro p
    have hd := one_sub_distinctPrimeDecay_ne_zero p hs0
    by_cases hp : p = correctionPrimeTwo
    · subst p
      have hfactor : oddPrimeCorrectionFactor correctionPrimeTwo s = 1 := if_pos rfl
      rw [if_pos (rfl : correctionPrimeTwo = correctionPrimeTwo), hfactor, mul_one]
      dsimp only [distinctPrimeTwoCorrection]
      field_simp
    · have hp2 : (p : ℕ) ≠ 2 := fun he => hp (Subtype.ext he)
      rw [if_neg hp, one_mul, oddPrimeCorrectionFactor_eq p hs0, if_neg hp2]
      field_simp
  have hseries : HasProd (fun p : Nat.Primes =>
      (1 - 2 * distinctPrimeDecay p s) / (1 - distinctPrimeDecay p s))
      (LSeries (fun n => (distinctPrimeSign n : ℂ)) s) :=
    (distinctPrimeSign_eulerProduct_hasProd hs).congr_fun
      (fun p => by simp only [distinctPrimeDecay_eq_cpow])
  exact hlocal.unique hseries

/-- The analytic local correction specializes to the prime-pair factor. -/
theorem oddPrimeCorrectionFactor_one (p : Nat.Primes) :
    oddPrimeCorrectionFactor p 1 =
      (BezoutValuationIncidence.twinPrimeFactor p : ℂ) := by
  unfold oddPrimeCorrectionFactor BezoutValuationIncidence.twinPrimeFactor
  split_ifs with hp
  · simp only [Complex.ofReal_one]
  · rw [distinctPrimeDecay_one]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast p.prop.ne_one)
    push_cast
    field_simp

/-- The holomorphic correction takes the positive twin-prime value at one. -/
theorem oddPrimeCorrection_one :
    oddPrimeCorrection 1 = (BezoutValuationIncidence.twinPrimeConstant : ℂ) := by
  have h : HasProd BezoutValuationIncidence.twinPrimeFactor
      BezoutValuationIncidence.twinPrimeConstant := by
    rw [BezoutValuationIncidence.twinPrimeConstant_eq_singularSeries]
    exact BezoutValuationIncidence.hasProd_twinPrimeFactor
  exact ((h.map Complex.ofRealHom Complex.continuous_ofReal).congr_fun
    oddPrimeCorrectionFactor_one).tprod_eq

private theorem twoDecay_one : distinctPrimeDecay correctionPrimeTwo 1 = 1 / 2 := by
  rw [distinctPrimeDecay_one]
  norm_num [correctionPrimeTwo]

private theorem analyticAt_twoDecay_one :
    AnalyticAt ℂ (distinctPrimeDecay correctionPrimeTwo) 1 := by
  change AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(z * (Real.log 2 : ℂ)))) 1
  exact ((analyticAt_id.mul analyticAt_const).neg).cexp

private theorem analyticAt_invZeta_one : AnalyticAt ℂ RHTower.Sieve.invZeta 1 := by
  change AnalyticAt ℂ (fun s : ℂ => (s - 1) * (RHTower.zetaResidueUnit s)⁻¹) 1
  exact (analyticAt_id.sub analyticAt_const).mul
    ((RHTower.analyticAt_zetaResidueUnit 1).inv
      (by rw [RHTower.zetaResidueUnit_one]; norm_num))

private theorem analyticAt_twoCorrection_one : AnalyticAt ℂ distinctPrimeTwoCorrection 1 := by
  have hx := analyticAt_twoDecay_one
  exact (analyticAt_const.sub (analyticAt_const.mul hx)).div
    ((analyticAt_const.sub hx).pow 2) (by
      change (1 - distinctPrimeDecay correctionPrimeTwo 1) ^ 2 ≠ 0
      rw [twoDecay_one]
      norm_num)

/-- The Euler continuation is holomorphic at one, with the zeta pole removed. -/
theorem analyticAt_distinctPrimeSignContinuation_one :
    AnalyticAt ℂ distinctPrimeSignContinuation 1 :=
  (analyticAt_twoCorrection_one.mul analyticAt_invZeta_one).mul
    (analyticOnNhd_oddPrimeCorrection 1 (by norm_num))

private theorem hasDerivAt_twoDecay_one :
    HasDerivAt (distinctPrimeDecay correctionPrimeTwo) (-(Real.log 2 : ℂ) / 2) 1 := by
  have h := (((hasDerivAt_id (𝕜 := ℂ) 1).mul_const (Real.log 2 : ℂ)).neg).cexp
  change HasDerivAt (distinctPrimeDecay correctionPrimeTwo)
    (distinctPrimeDecay correctionPrimeTwo 1 * -(1 * (Real.log 2 : ℂ))) 1 at h
  rw [twoDecay_one] at h
  convert h using 1
  ring

/-- The derivative of the prime-two correction is exactly four log two. -/
theorem deriv_distinctPrimeTwoCorrection_one :
    deriv distinctPrimeTwoCorrection 1 = 4 * (Real.log 2 : ℂ) := by
  have hx := hasDerivAt_twoDecay_one
  have hn := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (HasDerivAt.const_mul (2 : ℂ) hx)
  have hd := ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hx).pow 2
  have hden : (1 - distinctPrimeDecay correctionPrimeTwo 1) ^ 2 ≠ 0 := by
    rw [twoDecay_one]
    norm_num
  have h := (hn.div hd hden).deriv
  change deriv distinctPrimeTwoCorrection 1 = _ at h
  rw [h]
  simp only [Pi.pow_apply, Pi.sub_apply, twoDecay_one]
  ring

private theorem deriv_twoCorrection_mul_invZeta_one :
    deriv (distinctPrimeTwoCorrection * RHTower.Sieve.invZeta) 1 = 0 := by
  rw [deriv_mul analyticAt_twoCorrection_one.differentiableAt
    analyticAt_invZeta_one.differentiableAt, distinctPrimeTwoCorrection_one,
    RHTower.Sieve.invZeta_one]
  ring

/-- Both first-order contributions vanish because each contains the other zero factor. -/
theorem deriv_distinctPrimeSignContinuation_one :
    deriv distinctPrimeSignContinuation 1 = 0 := by
  change deriv ((distinctPrimeTwoCorrection * RHTower.Sieve.invZeta) * oddPrimeCorrection) 1 = 0
  rw [deriv_mul (analyticAt_twoCorrection_one.mul analyticAt_invZeta_one).differentiableAt
    (analyticOnNhd_oddPrimeCorrection 1 (by norm_num)).differentiableAt,
    deriv_twoCorrection_mul_invZeta_one]
  simp only [Pi.mul_apply, distinctPrimeTwoCorrection_one, zero_mul, zero_add]

private theorem secondDeriv_twoCorrection_mul_invZeta_one :
    iteratedDeriv 2 (distinctPrimeTwoCorrection * RHTower.Sieve.invZeta) 1 =
      8 * (Real.log 2 : ℂ) := by
  rw [iteratedDeriv_mul analyticAt_twoCorrection_one.contDiffAt analyticAt_invZeta_one.contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    distinctPrimeTwoCorrection_one, RHTower.Sieve.invZeta_one,
    deriv_distinctPrimeTwoCorrection_one, RHTower.Sieve.deriv_invZeta_one]
  ring

/-- The exact curvature of the arithmetic continuation is the twin-prime constant times
eight log two. Only the mixed first derivatives survive the product rule. -/
theorem secondDeriv_distinctPrimeSignContinuation_one :
    iteratedDeriv 2 distinctPrimeSignContinuation 1 =
      (8 * BezoutValuationIncidence.twinPrimeConstant * Real.log 2 : ℝ) := by
  change iteratedDeriv 2
    ((distinctPrimeTwoCorrection * RHTower.Sieve.invZeta) * oddPrimeCorrection) 1 = _
  rw [iteratedDeriv_mul (analyticAt_twoCorrection_one.mul analyticAt_invZeta_one).contDiffAt
    (analyticOnNhd_oddPrimeCorrection 1 (by norm_num)).contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    deriv_twoCorrection_mul_invZeta_one, secondDeriv_twoCorrection_mul_invZeta_one,
    Pi.mul_apply, distinctPrimeTwoCorrection_one, oddPrimeCorrection_one]
  ring

/-- The curvature is positive, so the zero at one is exactly double. -/
theorem secondDeriv_distinctPrimeSignContinuation_one_pos :
    0 < (iteratedDeriv 2 distinctPrimeSignContinuation 1).re := by
  rw [secondDeriv_distinctPrimeSignContinuation_one, Complex.ofReal_re]
  exact mul_pos (mul_pos (by norm_num) BezoutValuationIncidence.twinPrimeConstant_pos)
    (Real.log_pos (by norm_num))

/-- The same curvature is four log two times the existing gap-two covariance singular series. -/
theorem secondDeriv_distinctPrimeSignContinuation_eq_singularSeries :
    iteratedDeriv 2 distinctPrimeSignContinuation 1 =
      (4 * Real.log 2 * BezoutValuationIncidence.hardyLittlewoodSingularSeries 2 : ℝ) := by
  rw [secondDeriv_distinctPrimeSignContinuation_one,
    BezoutValuationIncidence.twinPrimeConstant_eq_singularSeries]
  push_cast
  ring

#print axioms oddPrimeCorrection_one
#print axioms distinctPrimeSignContinuation_eq_LSeries
#print axioms analyticAt_distinctPrimeSignContinuation_one
#print axioms deriv_distinctPrimeSignContinuation_one
#print axioms secondDeriv_distinctPrimeSignContinuation_one
#print axioms secondDeriv_distinctPrimeSignContinuation_one_pos
#print axioms secondDeriv_distinctPrimeSignContinuation_eq_singularSeries
end GaloisForLFunctions.SelbergClass
