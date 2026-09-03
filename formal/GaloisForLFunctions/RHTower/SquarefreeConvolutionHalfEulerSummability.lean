import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfRigidity
import GaloisForLFunctions.RHTower.EulerProduct
import GaloisForLFunctions.HTGeometry.PrimeRadialFusionNaturality
import GaloisForLFunctions.HTGeometry.SquareIndexSymmetricSquare
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Euler-chamber summability of the squarefree convolution half

The normalized Dirichlet-convolution square root of the squarefree indicator is not merely a
recursive coefficient system.  It is the multiplicative system whose local series is
`(1 + X)^(1/2)`.  Consequently its prime-power coefficients are the generalized binomial
coefficients `choose (1/2) k`.

The one-step binomial recurrence bounds every such coefficient by one.  Multiplicativity then
transfers the local bound to the divisor bound, proving absolute convergence of the associated
Dirichlet series on `Re s > 1`.  There its square is exactly `ζ(s) / ζ(2s)`.

This closes the report's coefficient-algebra and Euler-chamber convergence claims.  It supplies no
continuation across `Re s = 1`: extending this holomorphic germ to `Re s > 1/2` remains exactly the
parity-ladder edge.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators Moebius ArithmeticFunction.zeta Nat

noncomputable section

namespace RHTower

/-- Multiplicative coefficient system with local series `(1 + X)^(1/2)`. -/
def squarefreeBinomialHalf : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      n.factorization.prod fun _p k => Ring.choose (1 / 2 : ℂ) k,
    by simp⟩

@[simp] theorem squarefreeBinomialHalf_apply_one : squarefreeBinomialHalf 1 = 1 := by
  simp [squarefreeBinomialHalf]

theorem squarefreeBinomialHalf_isMultiplicative :
    squarefreeBinomialHalf.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeBinomialHalf_apply_one, ?_⟩
  intro m n hm hn hcop
  have hdisj : Disjoint m.factorization.support n.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hcop.disjoint_primeFactors
  rw [squarefreeBinomialHalf, coe_mk, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn,
    Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint hdisj]

theorem squarefreeBinomialHalf_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    squarefreeBinomialHalf (p ^ k) = Ring.choose (1 / 2 : ℂ) k := by
  rw [squarefreeBinomialHalf, coe_mk, if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index]
  simp

theorem squarefreeIndicator_isMultiplicative : squarefreeIndicator.IsMultiplicative := by
  exact (ArithmeticFunction.isMultiplicative_moebius.pmul
    ArithmeticFunction.isMultiplicative_moebius).intCast

/-- The explicit binomial local factors convolve to the squarefree indicator. -/
theorem squarefreeBinomialHalf_mul_self :
    squarefreeBinomialHalf * squarefreeBinomialHalf = squarefreeIndicator := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (squarefreeBinomialHalf_isMultiplicative.mul squarefreeBinomialHalf_isMultiplicative) _
    squarefreeIndicator_isMultiplicative).mpr ?_
  intro p i hp
  rw [ArithmeticFunction.mul_apply,
    GaloisForLFunctions.HTGeometry.divisorsAntidiagonal_prime_pow
      (⟨p, hp⟩ : Nat.Primes) i, Finset.sum_map]
  change (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
      squarefreeBinomialHalf (p ^ x.1) * squarefreeBinomialHalf (p ^ x.2)) = _
  simp_rw [squarefreeBinomialHalf_apply_prime_pow hp]
  have hcoeff := congrArg (PowerSeries.coeff i)
    (PowerSeries.binomialSeries_add (A := ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ))
  simp only [PowerSeries.coeff_mul, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] at hcoeff
  rw [← hcoeff]
  norm_num
  by_cases hi0 : i = 0
  · subst i
    simp
  by_cases hi1 : i = 1
  · subst i
    simpa using (squarefreeIndicator_apply_prime hp).symm
  have hchoose : Ring.choose (1 : ℂ) i = 0 := by
    have hcast := Ring.choose_natCast (R := ℂ) 1 i
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hcast
    simpa using hcast
  have hindicator : squarefreeIndicator (p ^ i) = 0 := by
    rw [squarefreeIndicator, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.pmul_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp hi0]
    simp [hi1]
  rw [hchoose, hindicator]

/-- The recursive convolution half is exactly the source-defined multiplicative binomial system. -/
theorem squarefreeBinomialHalf_eq_squarefreeConvolutionHalf :
    squarefreeBinomialHalf = squarefreeConvolutionHalf :=
  convolutionHalf_unique squarefreeIndicator squarefreeBinomialHalf
    squarefreeBinomialHalf_apply_one squarefreeBinomialHalf_mul_self

theorem squarefreeConvolutionHalf_isMultiplicative :
    squarefreeConvolutionHalf.IsMultiplicative := by
  rw [← squarefreeBinomialHalf_eq_squarefreeConvolutionHalf]
  exact squarefreeBinomialHalf_isMultiplicative

/-- All local coefficients of the canonical convolution half. -/
theorem squarefreeConvolutionHalf_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    squarefreeConvolutionHalf (p ^ k) = Ring.choose (1 / 2 : ℂ) k := by
  rw [← squarefreeBinomialHalf_eq_squarefreeConvolutionHalf]
  exact squarefreeBinomialHalf_apply_prime_pow hp

private theorem choose_succ_field_complex (a : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * Ring.choose a (n + 1) = Ring.choose a n * (a - n) := by
  have key := Ring.descPochhammer_eq_factorial_smul_choose (R := ℂ) a (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
      Ring.descPochhammer_eq_factorial_smul_choose (R := ℂ) a n] at key
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    npow_one, pow_zero, mul_one, nsmul_eq_mul, Nat.factorial_succ] at key
  push_cast at key
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : (n ! : ℂ) * (((n : ℂ) + 1) * Ring.choose a (n + 1)) =
      (n ! : ℂ) * (Ring.choose a n * (a - n)) := by
    linear_combination -key
  exact mul_left_cancel₀ hfac h2

/-- The generalized binomial coefficients of `(1 + X)^(1/2)` have norm at most one. -/
theorem norm_choose_complex_half_le_one (n : ℕ) :
    ‖Ring.choose (1 / 2 : ℂ) n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec := choose_succ_field_complex (1 / 2 : ℂ) n
      have hden : ((n : ℂ) + 1) ≠ 0 := by
        exact_mod_cast (show (n : ℤ) + 1 ≠ 0 by omega)
      have hform : Ring.choose (1 / 2 : ℂ) (n + 1) =
          Ring.choose (1 / 2 : ℂ) n * ((1 / 2 : ℂ) - n) / ((n : ℂ) + 1) := by
        rw [eq_div_iff hden]
        simpa [mul_comm] using hrec
      rw [hform, norm_div, norm_mul]
      have hnum : ‖(1 / 2 : ℂ) - n‖ ≤ (n : ℝ) + 1 := by
        calc
          ‖(1 / 2 : ℂ) - n‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
          _ = 1 / 2 + (n : ℝ) := by norm_num
          _ ≤ (n : ℝ) + 1 := by linarith
      have hdennorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
        calc
          ‖(n : ℂ) + 1‖ = ‖((n + 1 : ℕ) : ℂ)‖ := by norm_num
          _ = ((n + 1 : ℕ) : ℝ) := Complex.norm_natCast _
          _ = (n : ℝ) + 1 := by norm_num
      have hratio : ‖(1 / 2 : ℂ) - n‖ / ‖(n : ℂ) + 1‖ ≤ 1 := by
        rw [hdennorm]
        exact (div_le_one (by positivity)).2 hnum
      calc
        ‖Ring.choose (1 / 2 : ℂ) n‖ * ‖(1 / 2 : ℂ) - n‖ / ‖(n : ℂ) + 1‖ =
            ‖Ring.choose (1 / 2 : ℂ) n‖ *
              (‖(1 / 2 : ℂ) - n‖ / ‖(n : ℂ) + 1‖) := by ring
        _ ≤ 1 * 1 := mul_le_mul ih hratio (by positivity) (by norm_num)
        _ = 1 := one_mul 1

/-- Global divisor bound for the canonical convolution half. -/
theorem norm_squarefreeConvolutionHalf_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    ‖squarefreeConvolutionHalf n‖ ≤ (n.divisors.card : ℝ) := by
  have h := HTGeometry.norm_le_card_divisors
    squarefreeBinomialHalf_isMultiplicative (fun p k hp => by
      rw [squarefreeBinomialHalf_apply_prime_pow hp]
      exact (norm_choose_complex_half_le_one k).trans (by norm_num)) hn
  simpa only [squarefreeBinomialHalf_eq_squarefreeConvolutionHalf] using h

/-- Absolute convergence of the canonical half's Dirichlet series on the Euler chamber. -/
theorem LSeriesSummable_squarefreeConvolutionHalf {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable squarefreeConvolutionHalf s := by
  apply Summable.of_norm_bounded
    (g := fun n => ‖LSeries.term (fun n : ℕ => (n.divisors.card : ℂ)) s n‖)
    (RHTower.Sieve.LSeriesSummable_card_divisors hs).norm
  intro n
  apply LSeries.norm_term_le
  by_cases hn : n = 0
  · subst n
    simp
  simpa using norm_squarefreeConvolutionHalf_le_card_divisors hn

/-- On `Re s > 1`, the source-defined half series squares to the squarefree Euler quotient. -/
theorem LSeries_squarefreeConvolutionHalf_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries squarefreeConvolutionHalf s ^ 2 =
      riemannZeta s / riemannZeta (2 * s) := by
  calc
    LSeries squarefreeConvolutionHalf s ^ 2 =
        LSeries squarefreeConvolutionHalf s * LSeries squarefreeConvolutionHalf s := by ring
    _ = LSeries (⇑((squarefreeConvolutionHalf * squarefreeConvolutionHalf) :
        ArithmeticFunction ℂ)) s :=
      (ArithmeticFunction.LSeries_mul'
        (LSeriesSummable_squarefreeConvolutionHalf hs)
        (LSeriesSummable_squarefreeConvolutionHalf hs)).symm
    _ = LSeries squarefreeIndicator s := by rw [squarefreeConvolutionHalf_mul_self]
    _ = riemannZeta s / riemannZeta (2 * s) := by
      have hfun : (⇑squarefreeIndicator : ℕ → ℂ) =
          (fun n => ((ArithmeticFunction.pmul
            (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
            ArithmeticFunction.moebius) n : ℂ)) := by
        funext n
        simp [squarefreeIndicator, ArithmeticFunction.intCoe_apply]
      rw [hfun]
      exact LSeries_squarefree_eq_riemannZeta_div hs

theorem abscissaOfAbsConv_squarefreeConvolutionHalf_le_one :
    LSeries.abscissaOfAbsConv squarefreeConvolutionHalf ≤ (1 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact LSeriesSummable_squarefreeConvolutionHalf (by simpa using hy)

/-- Holomorphy of the canonical coefficient half throughout its proved Euler chamber. -/
theorem analyticOnNhd_LSeries_squarefreeConvolutionHalf :
    AnalyticOnNhd ℂ (LSeries squarefreeConvolutionHalf) {s : ℂ | 1 < s.re} := by
  apply (LSeries_analyticOnNhd squarefreeConvolutionHalf).mono
  intro s hs
  change 1 < s.re at hs
  exact lt_of_le_of_lt abscissaOfAbsConv_squarefreeConvolutionHalf_le_one (by exact_mod_cast hs)

/-- Dirichlet-polynomial truncations converge compact-open to the canonical half on `Re s > 1`. -/
theorem tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums :
    TendstoLocallyUniformlyOn
      (fun N s => ∑ n ∈ Finset.range N, LSeries.term squarefreeConvolutionHalf s n)
      (LSeries squarefreeConvolutionHalf) atTop {s : ℂ | 1 < s.re} := by
  intro u hu x hx
  let sigma : ℝ := (1 + x.re) / 2
  have hfar : 1 < x.re := hx
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hsigma_x : sigma < x.re := by
    dsimp [sigma]
    linarith
  let t : Set ℂ := {z | sigma < z.re}
  have htopen : IsOpen t := isOpen_lt continuous_const continuous_re
  have hxt : x ∈ t := hsigma_x
  refine ⟨t, mem_nhdsWithin_of_mem_nhds (htopen.mem_nhds hxt), ?_⟩
  have hmajor := (LSeriesSummable_squarefreeConvolutionHalf
    (s := (sigma : ℂ)) (by simpa using hsigma)).norm
  have hconv := tendstoUniformlyOn_tsum_nat
    (f := fun n (z : ℂ) => LSeries.term squarefreeConvolutionHalf z n) (s := t)
    hmajor (fun n z hz => by
      change sigma < z.re at hz
      exact LSeries.norm_term_le_of_re_le_re squarefreeConvolutionHalf
        (by simpa using le_of_lt hz) n)
  change ∀ᶠ N in atTop, ∀ y ∈ t,
    ((∑' n, LSeries.term squarefreeConvolutionHalf y n),
      ∑ n ∈ Finset.range N, LSeries.term squarefreeConvolutionHalf y n) ∈ u
  exact hconv u hu

end RHTower
