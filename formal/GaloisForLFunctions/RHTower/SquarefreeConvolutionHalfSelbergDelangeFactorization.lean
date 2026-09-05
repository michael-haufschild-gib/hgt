import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfEulerSummability
import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.HTGeometry.ArcsineCentralBinomial
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Analysis.Complex.Order

/-!
# Selberg--Delange factorization of the squarefree convolution half

The canonical signed square root of the squarefree Euler source factors as a positive zeta half
convolved with a square-supported correction.  At every prime, the positive factor has local series
`(1-X)⁻¹ᐟ²`; the undilated correction half has local series `(1-X)¹ᐟ²`, and its square dilation has
local series `(1-X²)¹ᐟ²`.

This is the coefficient-algebra input for a Selberg--Delange asymptotic.  No Tauberian conclusion is
claimed here: the remaining analytic inputs are a fractional Wiener--Ikehara theorem for the
nonnegative zeta half and a regularly-varying convolution-transfer theorem.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators Moebius ArithmeticFunction.zeta Nat ComplexOrder

noncomputable section

namespace RHTower

private def liouvilleC : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)

/-- Pointwise Liouville twisting commutes with Dirichlet convolution. -/
private theorem liouvilleC_pmul_mul (f g : ArithmeticFunction ℂ) :
    liouvilleC.pmul (f * g) = (liouvilleC.pmul f) * (liouvilleC.pmul g) := by
  ext n
  rw [pmul_apply, mul_apply, mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxn := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hliouville : liouvilleC n = liouvilleC x.1 * liouvilleC x.2 := by
    rw [← hxn]
    simp [liouvilleC, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.liouville_apply_mul]
  rw [hliouville]
  simp only [pmul_apply]
  ring

/-- The local `(1-X)^(1/2)` coefficient system, obtained by Liouville twisting the already
formalized `(1+X)^(1/2)` squarefree half. -/
def moebiusBinomialHalf : ArithmeticFunction ℂ :=
  liouvilleC.pmul squarefreeBinomialHalf

@[simp] theorem moebiusBinomialHalf_apply_one : moebiusBinomialHalf 1 = 1 := by
  simp [moebiusBinomialHalf, liouvilleC, ArithmeticFunction.liouville_apply_one]

theorem moebiusBinomialHalf_isMultiplicative :
    moebiusBinomialHalf.IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_liouville.intCast.pmul
    squarefreeBinomialHalf_isMultiplicative

theorem moebiusBinomialHalf_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    moebiusBinomialHalf (p ^ k) =
      (-1 : ℂ) ^ k * Ring.choose (1 / 2 : ℂ) k := by
  rw [moebiusBinomialHalf, pmul_apply, squarefreeBinomialHalf_apply_prime_pow hp]
  congr 1
  rw [liouvilleC, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.liouville_apply (pow_ne_zero k hp.ne_zero),
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  norm_num

private theorem liouvilleC_pmul_squarefreeIndicator :
    liouvilleC.pmul squarefreeIndicator =
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  ext n
  by_cases hn : Squarefree n
  · have hn0 : n ≠ 0 := hn.ne_zero
    rw [pmul_apply, liouvilleC, squarefreeIndicator]
    change ((ArithmeticFunction.liouville n : ℤ) : ℂ) *
      (((μ n : ℤ) * μ n : ℤ) : ℂ) = ((μ n : ℤ) : ℂ)
    rw [
      ArithmeticFunction.liouville_apply hn0,
      ArithmeticFunction.moebius_apply_of_squarefree hn]
    push_cast
    have hsign : (-1 : ℂ) ^ ArithmeticFunction.cardFactors n *
        (-1 : ℂ) ^ ArithmeticFunction.cardFactors n = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hsign, mul_one]
  · simp [liouvilleC, squarefreeIndicator, pmul_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

/-- The Liouville-twisted binomial half squares to the complex-cast Möbius function. -/
theorem moebiusBinomialHalf_mul_self :
    moebiusBinomialHalf * moebiusBinomialHalf =
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  rw [moebiusBinomialHalf, ← liouvilleC_pmul_mul,
    squarefreeBinomialHalf_mul_self, liouvilleC_pmul_squarefreeIndicator]

theorem norm_moebiusBinomialHalf_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    ‖moebiusBinomialHalf n‖ ≤ (n.divisors.card : ℝ) := by
  have h := HTGeometry.norm_le_card_divisors
    moebiusBinomialHalf_isMultiplicative (fun p k hp => by
      rw [moebiusBinomialHalf_apply_prime_pow hp, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
      exact (norm_choose_complex_half_le_one k).trans (by norm_num)) hn
  exact h

theorem LSeriesSummable_moebiusBinomialHalf {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable moebiusBinomialHalf s := by
  apply Summable.of_norm_bounded
    (g := fun n => ‖LSeries.term (fun n : ℕ => (n.divisors.card : ℂ)) s n‖)
    (RHTower.Sieve.LSeriesSummable_card_divisors hs).norm
  intro n
  apply LSeries.norm_term_le
  by_cases hn : n = 0
  · subst n
    simp
  · simpa using norm_moebiusBinomialHalf_le_card_divisors hn

/-- Multiplicative coefficient system with local series `(1-X)^(-1/2)`. -/
def zetaBinomialHalf : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      n.factorization.prod fun _p k =>
        (-1 : ℂ) ^ k * Ring.choose (-1 / 2 : ℂ) k,
    by simp⟩

@[simp] theorem zetaBinomialHalf_apply_one : zetaBinomialHalf 1 = 1 := by
  simp [zetaBinomialHalf]

theorem zetaBinomialHalf_isMultiplicative : zetaBinomialHalf.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨zetaBinomialHalf_apply_one, ?_⟩
  intro m n hm hn hcop
  have hdisj : Disjoint m.factorization.support n.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hcop.disjoint_primeFactors
  rw [zetaBinomialHalf, coe_mk, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn,
    Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint hdisj]

theorem zetaBinomialHalf_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    zetaBinomialHalf (p ^ k) =
      (-1 : ℂ) ^ k * Ring.choose (-1 / 2 : ℂ) k := by
  rw [zetaBinomialHalf, coe_mk, if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index]
  simp

private theorem zetaBinomialLocal_eq_centralBinom (k : ℕ) :
    (-1 : ℂ) ^ k * Ring.choose (-1 / 2 : ℂ) k =
      (((Nat.centralBinom k : ℝ) / 4 ^ k : ℝ) : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_choose, GaloisForLFunctions.choose_neg_half]
  push_cast
  have hsign : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mul_div_assoc, ← mul_assoc, hsign, one_mul]

/-- Closed positive local coefficient formula for the zeta half. -/
theorem zetaBinomialHalf_apply_prime_pow_eq_centralBinom {p k : ℕ} (hp : p.Prime) :
    zetaBinomialHalf (p ^ k) =
      ((Nat.centralBinom k : ℝ) / 4 ^ k : ℝ) := by
  rw [zetaBinomialHalf_apply_prime_pow hp, zetaBinomialLocal_eq_centralBinom]

theorem zetaBinomialHalf_apply_nonneg (n : ℕ) :
    0 ≤ (zetaBinomialHalf n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [zetaBinomialHalf, coe_mk, if_neg hn, Finsupp.prod]
  simp_rw [zetaBinomialLocal_eq_centralBinom]
  have hprod :
      (∏ p ∈ n.factorization.support,
        ((((Nat.centralBinom (n.factorization p) : ℝ) /
          4 ^ n.factorization p : ℝ) : ℂ))) =
      (((∏ p ∈ n.factorization.support,
        (Nat.centralBinom (n.factorization p) : ℝ) /
          4 ^ n.factorization p) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, Complex.ofReal_re]
  apply Finset.prod_nonneg
  intro p hp
  positivity

/-- Every coefficient of the zeta half is real. -/
theorem zetaBinomialHalf_apply_im (n : ℕ) :
    (zetaBinomialHalf n).im = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [zetaBinomialHalf, coe_mk, if_neg hn, Finsupp.prod]
  simp_rw [zetaBinomialLocal_eq_centralBinom]
  have hprod :
      (∏ p ∈ n.factorization.support,
        ((((Nat.centralBinom (n.factorization p) : ℝ) /
          4 ^ n.factorization p : ℝ) : ℂ))) =
      (((∏ p ∈ n.factorization.support,
        (Nat.centralBinom (n.factorization p) : ℝ) /
          4 ^ n.factorization p) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, Complex.ofReal_im]

/-- Positivity in the ordered copy of `ℝ` inside `ℂ`. -/
theorem zetaBinomialHalf_apply_nonneg_complex (n : ℕ) :
    0 ≤ zetaBinomialHalf n := by
  rw [Complex.nonneg_iff]
  exact ⟨zetaBinomialHalf_apply_nonneg n, (zetaBinomialHalf_apply_im n).symm⟩

/-- Coefficients of the positive zeta half have norm at most one. -/
theorem norm_zetaBinomialHalf_le_one (n : ℕ) :
    ‖zetaBinomialHalf n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaBinomialHalf]
  rw [zetaBinomialHalf, coe_mk, if_neg hn, Finsupp.prod]
  refine (Finset.norm_prod_le _ _).trans ?_
  calc
    ∏ p ∈ n.factorization.support,
        ‖(-1 : ℂ) ^ n.factorization p *
          Ring.choose (-1 / 2 : ℂ) (n.factorization p)‖ =
        ∏ p ∈ n.factorization.support,
          (Nat.centralBinom (n.factorization p) : ℝ) /
            4 ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [zetaBinomialLocal_eq_centralBinom, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    _ ≤ 1 := by
      apply Finset.prod_le_one
      · intro p hp
        positivity
      · intro p hp
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.centralBinom_le_four_pow (n.factorization p)

theorem zetaBinomialHalf_mul_self :
    zetaBinomialHalf * zetaBinomialHalf = (ζ : ArithmeticFunction ℂ) := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (zetaBinomialHalf_isMultiplicative.mul zetaBinomialHalf_isMultiplicative) _
    ArithmeticFunction.isMultiplicative_zeta.natCast).mpr ?_
  intro p i hp
  rw [ArithmeticFunction.mul_apply,
    GaloisForLFunctions.HTGeometry.divisorsAntidiagonal_prime_pow
      (⟨p, hp⟩ : Nat.Primes) i, Finset.sum_map]
  change (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
      zetaBinomialHalf (p ^ x.1) * zetaBinomialHalf (p ^ x.2)) = _
  simp_rw [zetaBinomialHalf_apply_prime_pow hp]
  have hcoeff := congrArg (PowerSeries.coeff i)
    (PowerSeries.binomialSeries_add (A := ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ))
  simp only [PowerSeries.coeff_mul, PowerSeries.binomialSeries_coeff, smul_eq_mul,
    mul_one] at hcoeff
  norm_num at hcoeff
  have hcoeff' :
      Ring.choose (-1 : ℂ) i =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
          Ring.choose (-1 / 2 : ℂ) x.1 * Ring.choose (-1 / 2 : ℂ) x.2 := by
    simpa [neg_div] using hcoeff
  calc
    (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
        ((-1 : ℂ) ^ x.1 * Ring.choose (-1 / 2 : ℂ) x.1) *
          ((-1 : ℂ) ^ x.2 * Ring.choose (-1 / 2 : ℂ) x.2)) =
        (-1 : ℂ) ^ i *
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
            Ring.choose (-1 / 2 : ℂ) x.1 * Ring.choose (-1 / 2 : ℂ) x.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hsum : x.1 + x.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      calc
        (-1 : ℂ) ^ x.1 * Ring.choose (-1 / 2 : ℂ) x.1 *
            ((-1 : ℂ) ^ x.2 * Ring.choose (-1 / 2 : ℂ) x.2) =
            ((-1 : ℂ) ^ x.1 * (-1 : ℂ) ^ x.2) *
              (Ring.choose (-1 / 2 : ℂ) x.1 *
                Ring.choose (-1 / 2 : ℂ) x.2) := by ring
        _ = (-1 : ℂ) ^ i *
              (Ring.choose (-1 / 2 : ℂ) x.1 *
                Ring.choose (-1 / 2 : ℂ) x.2) := by rw [← pow_add, hsum]
    _ = (-1 : ℂ) ^ i * Ring.choose (-1 : ℂ) i := by rw [← hcoeff']
    _ = 1 := by
      have hchoose : Ring.choose (-1 : ℂ) i = (-1 : ℂ) ^ i := by
        rw [Ring.choose_neg]
        have harg : (1 : ℂ) + (i : ℂ) - 1 = (i : ℂ) := by ring
        rw [harg, Ring.choose_natCast, Nat.choose_self]
        norm_num only [Nat.cast_one]
        calc
          (i : ℤ).negOnePow • (1 : ℂ) = (((i : ℤ).negOnePow : ℤ) : ℂ) :=
            Int.smul_one_eq_cast _
          _ = (-1 : ℂ) ^ i := Int.cast_negOnePow_natCast ℂ i
      rw [hchoose, ← mul_pow]
      norm_num
    _ = (ζ : ArithmeticFunction ℂ) (p ^ i) := by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        if_neg (pow_ne_zero i hp.ne_zero)]
      norm_num

/-- The explicit positive local system is the canonical convolution half of zeta. -/
theorem zetaBinomialHalf_eq_convolutionHalf_zeta :
    zetaBinomialHalf = convolutionHalf (ζ : ArithmeticFunction ℂ) :=
  convolutionHalf_unique (ζ : ArithmeticFunction ℂ) zetaBinomialHalf
    zetaBinomialHalf_apply_one zetaBinomialHalf_mul_self

theorem norm_zetaBinomialHalf_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    ‖zetaBinomialHalf n‖ ≤ (n.divisors.card : ℝ) := by
  have h := HTGeometry.norm_le_card_divisors
    zetaBinomialHalf_isMultiplicative (fun p k hp => by
      rw [zetaBinomialHalf_apply_prime_pow_eq_centralBinom hp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hcast : (Nat.centralBinom k : ℝ) ≤ (4 ^ k : ℕ) := by
        exact_mod_cast Nat.centralBinom_le_four_pow k
      rw [div_le_iff₀ (by positivity)]
      exact hcast.trans (by norm_num)) hn
  exact h

theorem LSeriesSummable_zetaBinomialHalf {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable zetaBinomialHalf s := by
  apply Summable.of_norm_bounded
    (g := fun n => ‖LSeries.term (fun n : ℕ => (n.divisors.card : ℂ)) s n‖)
    (RHTower.Sieve.LSeriesSummable_card_divisors hs).norm
  intro n
  apply LSeries.norm_term_le
  by_cases hn : n = 0
  · subst n
    simp
  · simpa using norm_zetaBinomialHalf_le_card_divisors hn

/-- Square-supported signed correction in the Selberg--Delange factorization. -/
def squareDilatedMoebiusBinomialHalf : ArithmeticFunction ℂ :=
  mPart 2 moebiusBinomialHalf

@[simp] theorem squareDilatedMoebiusBinomialHalf_apply_one :
    squareDilatedMoebiusBinomialHalf 1 = 1 := by
  rw [squareDilatedMoebiusBinomialHalf, show (1 : ℕ) = 1 ^ 2 by norm_num,
    mPart_apply_pow two_ne_zero, moebiusBinomialHalf_apply_one]

theorem LSeriesSummable_squareDilatedMoebiusBinomialHalf {s : ℂ}
    (hs : 1 / 2 < s.re) :
    LSeriesSummable squareDilatedMoebiusBinomialHalf s := by
  rw [squareDilatedMoebiusBinomialHalf, LSeriesSummable_mPart_iff two_ne_zero]
  apply LSeriesSummable_moebiusBinomialHalf
  norm_num at hs ⊢
  linarith

private theorem arithmeticFunction_eq_of_LSeries_eq_real_gt_one
    (f g : ArithmeticFunction ℂ)
    (hf : LSeriesSummable f (2 : ℂ)) (hg : LSeriesSummable g (2 : ℂ))
    (hfg : ∀ x : ℝ, 1 < x → LSeries f (x : ℂ) = LSeries g (x : ℂ)) : f = g := by
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  exact LSeries.eq_of_LSeries_eventually_eq
    (hf.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    (hg.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact hfg x hx)
    hn

/-- Dilation commutes with the required convolution square.  The proof uses uniqueness of
Dirichlet coefficients on a far-right ray, avoiding a separate finite divisor reindexing lemma. -/
theorem squareDilatedMoebiusBinomialHalf_mul_self :
    squareDilatedMoebiusBinomialHalf * squareDilatedMoebiusBinomialHalf =
      mPart 2 ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  have hc2 : LSeriesSummable squareDilatedMoebiusBinomialHalf (2 : ℂ) :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num)
  have hleftSumm := ArithmeticFunction.LSeriesSummable_mul hc2 hc2
  have hmu4 : LSeriesSummable
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (4 : ℂ) := by
    have hfun : (⇑(((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) : ℕ → ℂ) =
        (fun n => (μ n : ℂ)) := by
      funext n
      simp [ArithmeticFunction.intCoe_apply]
    rw [hfun]
    exact LSeriesSummable_moebius_iff.mpr (show 1 < (4 : ℂ).re by norm_num)
  have hrightSumm : LSeriesSummable
      (mPart 2 ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) := by
    rw [LSeriesSummable_mPart_iff two_ne_zero]
    convert hmu4 using 1
    all_goals norm_num
  apply arithmeticFunction_eq_of_LSeries_eq_real_gt_one _ _ hleftSumm hrightSumm
  intro x hx
  have hc : LSeriesSummable squareDilatedMoebiusBinomialHalf (x : ℂ) :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num at hx ⊢; linarith)
  have hu : LSeriesSummable moebiusBinomialHalf ((2 : ℂ) * (x : ℂ)) :=
    LSeriesSummable_moebiusBinomialHalf (by norm_num at hx ⊢; linarith)
  calc
    LSeries (⇑((squareDilatedMoebiusBinomialHalf *
        squareDilatedMoebiusBinomialHalf) : ArithmeticFunction ℂ)) (x : ℂ) =
        LSeries squareDilatedMoebiusBinomialHalf (x : ℂ) *
          LSeries squareDilatedMoebiusBinomialHalf (x : ℂ) :=
      ArithmeticFunction.LSeries_mul' hc hc
    _ = LSeries moebiusBinomialHalf ((2 : ℂ) * (x : ℂ)) *
          LSeries moebiusBinomialHalf ((2 : ℂ) * (x : ℂ)) := by
      rw [squareDilatedMoebiusBinomialHalf, LSeries_mPart two_ne_zero]
      norm_num
    _ = LSeries (⇑((moebiusBinomialHalf * moebiusBinomialHalf) : ArithmeticFunction ℂ))
          ((2 : ℂ) * (x : ℂ)) :=
      (ArithmeticFunction.LSeries_mul' hu hu).symm
    _ = LSeries (⇑(((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)))
          ((2 : ℂ) * (x : ℂ)) := by rw [moebiusBinomialHalf_mul_self]
    _ = LSeries (⇑(mPart 2
          ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ))) (x : ℂ) :=
      (LSeries_mPart two_ne_zero _ _).symm

/-- Algebraic Selberg--Delange factorization of the canonical signed squarefree half. -/
theorem squarefreeConvolutionHalf_eq_zetaBinomialHalf_mul_squareCorrection :
    squarefreeConvolutionHalf =
      zetaBinomialHalf * squareDilatedMoebiusBinomialHalf := by
  symm
  apply convolutionHalf_unique squarefreeIndicator
  · simp
  · calc
      (zetaBinomialHalf * squareDilatedMoebiusBinomialHalf) *
          (zetaBinomialHalf * squareDilatedMoebiusBinomialHalf) =
          (zetaBinomialHalf * zetaBinomialHalf) *
            (squareDilatedMoebiusBinomialHalf * squareDilatedMoebiusBinomialHalf) := by ring
      _ = (ζ : ArithmeticFunction ℂ) *
          mPart 2 ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
        rw [zetaBinomialHalf_mul_self, squareDilatedMoebiusBinomialHalf_mul_self]
      _ = squarefreeIndicator := by
        have hcast := congrArg
          (fun f : ArithmeticFunction ℤ => (f : ArithmeticFunction ℂ))
          (mPart_moebius_mul_zeta (m := 2) two_ne_zero)
        rw [ArithmeticFunction.intCoe_mul, mPart_intCoe, intCoe_natCoe] at hcast
        simpa [squarefreeIndicator, ← mFreeIndicator_two, mul_comm] using hcast

end RHTower
