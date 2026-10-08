import GaloisForLFunctions.RHTower.WeilWorkDeficitBesselCorrelation
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature

/-!
# The exact product-kernel budget for all prime correlations

The actual Riemann-kernel derivative correlations share one product kernel.
Regrouping the complete absolutely convergent prime/divisor family uses
`Λ * d = d * log / 2` and retains every prime power and every positive factor pair.

This reduces the uniform derivative-order problem to the weighted absolute
mass of `productKernel`. It supplies no uniform-in-order estimate and no
upper bound for the spectral deficit.
-/

noncomputable section
open MeasureTheory Set Polynomial Real ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta
open GaloisForLFunctions.HTGeometry
namespace RHTower.WeilWorkDeficitPrimeKernel
open WeilWorkDeficitBessel

/-- The finite Bessel polynomial from the actual derivative correlation. -/
def productKernel (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^k * ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
    ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
      (riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l *
        (x^(j+l) * realModifiedBesselKOrder (2*Real.pi*x) ((j:ℝ)-l))

private theorem divisor_card (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_left_divisors, Finset.card_map]

private theorem zeta_square (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^2) n = (n.divisors.card : ℝ) := by
  rw [pow_two, ArithmeticFunction.coe_mul_zeta_apply]
  calc (∑ d ∈ n.divisors, (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d) =
      ∑ _d ∈ n.divisors, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]
       _ = _ := by simp

private theorem prime_divisor_convolution (n : ℕ) :
    ∑ p ∈ n.divisorsAntidiagonal, vonMangoldt p.1 * (p.2.divisorsAntidiagonal.card : ℝ) =
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n / 2 := by
  have hd : logDerivation ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^2) =
      2 • (vonMangoldt * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)^2) := by
    rw [pow_two, logDerivation_mul, logDerivation_zeta, ← ArithmeticFunction.zeta_mul_vonMangoldt]
    simp only [two_smul]
    ring
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) hd
  simp only [two_smul, logDerivation_apply, zeta_square, ArithmeticFunction.add_apply,
    ArithmeticFunction.mul_apply] at he
  simp only [divisor_card]
  linarith

private theorem log_monomial_bound (j l n : ℕ) :
    0 ≤ (n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n ∧
    (n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n ≤
      (n.divisorsAntidiagonal.card : ℝ) * besselMonomial (j+1) (l+1) 0 n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hp := (realModifiedBesselKOrder_pos (by positivity : 0 < 2*Real.pi*(n:ℝ)) ((j:ℝ)-l)).le
    have hl : 0 ≤ Real.log n := log_nonneg hnr
    have hlb : Real.log n ≤ (n:ℝ)^2 := by
      have h := log_le_sub_one_of_pos (by positivity : (0:ℝ)<n)
      nlinarith
    simp only [besselMonomial, zero_div, exp_zero, mul_one, one_mul]
    have ho : ((j+1:ℕ):ℝ)-(l+1:ℕ) = (j:ℝ)-l := by push_cast; ring
    rw [ho]
    constructor
    · positivity
    · calc _ ≤ (n.divisorsAntidiagonal.card : ℝ) * (n:ℝ)^2 *
          ((n:ℝ)^(j+l) * realModifiedBesselKOrder (2*Real.pi*n) ((j:ℝ)-l)) := by gcongr
           _ = _ := by rw [show j+1+(l+1)=2+(j+l) by omega, pow_add]; ring

private theorem summable_log_monomial (j l : ℕ) :
    Summable (fun n : ℕ => (n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n) :=
  Summable.of_nonneg_of_le (fun n => (log_monomial_bound j l n).1)
    (fun n => (log_monomial_bound j l n).2) (summable_divisor_bessel (j+1) (l+1) 0)

private theorem kernel_abs_bound (k n : ℕ) :
    |productKernel k n| ≤
      ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
        ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
          |(riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l| *
            |besselMonomial j l 0 n| := by
  unfold productKernel
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  simp only [abs_mul, besselMonomial, zero_div, exp_zero, mul_one, one_mul]
  exact le_rfl

private theorem log_weight_nonneg (n : ℕ) : 0 ≤ (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast hn))

private theorem weighted_kernel_bound (k n : ℕ) :
    (n.divisorsAntidiagonal.card : ℝ) * Real.log n * |productKernel k n| ≤
      ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
        ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
          |(riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l| *
            ((n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n) := by
  refine (mul_le_mul_of_nonneg_left (kernel_abs_bound k n) (log_weight_nonneg n)).trans_eq ?_
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  have he : (n.divisorsAntidiagonal.card : ℝ) * Real.log n * |besselMonomial j l 0 n| =
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n := by
    calc _ = |(n.divisorsAntidiagonal.card : ℝ) * Real.log n * besselMonomial j l 0 n| := by
           rw [abs_mul, abs_of_nonneg (log_weight_nonneg n)]
         _ = _ := abs_of_nonneg (log_monomial_bound j l n).1
  calc _ = |(riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l| *
      ((n.divisorsAntidiagonal.card : ℝ) * Real.log n * |besselMonomial j l 0 n|) := by ring
       _ = _ := by rw [he]

/-- Every derivative order has a finite full logarithmic divisor budget. -/
theorem summable_log_productKernel (k : ℕ) :
    Summable (fun n : ℕ => (n.divisorsAntidiagonal.card : ℝ) * Real.log n * |productKernel k n|) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (log_weight_nonneg n) (abs_nonneg _))
    (weighted_kernel_bound k)
  apply summable_sum
  intro j hj
  apply summable_sum
  intro l hl
  exact (summable_log_monomial j l).mul_left _

private theorem fiber_identity (k m : ℕ) :
    ∑ p ∈ m.divisorsAntidiagonal, vonMangoldt p.1 * (p.2.divisorsAntidiagonal.card : ℝ) *
      |productKernel k (p.1*p.2 : ℕ)| =
      (m.divisorsAntidiagonal.card : ℝ) * Real.log m * |productKernel k m| / 2 := by
  have he : (∑ p ∈ m.divisorsAntidiagonal, vonMangoldt p.1 * (p.2.divisorsAntidiagonal.card : ℝ) *
      |productKernel k (p.1*p.2 : ℕ)|) =
      (∑ p ∈ m.divisorsAntidiagonal, vonMangoldt p.1 * (p.2.divisorsAntidiagonal.card : ℝ)) *
        |productKernel k m| := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
  rw [he, prime_divisor_convolution]
  ring

private def primePair (k : ℕ) (p : ℕ × ℕ) : ℝ :=
  vonMangoldt p.1 * (p.2.divisorsAntidiagonal.card : ℝ) * |productKernel k (p.1*p.2 : ℕ)|

private theorem primePair_nonneg (k : ℕ) (p : ℕ × ℕ) : 0 ≤ primePair k p := by
  exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (abs_nonneg _)

private theorem primePair_axes (k : ℕ) (p : ℕ × ℕ) (hp : p.1=0 ∨ p.2=0) : primePair k p = 0 := by
  rcases hp with hp | hp <;> simp [primePair, hp]

private theorem summable_primePair (k : ℕ) : Summable (primePair k) := by
  let f := primePair k
  have hzero : ∀ p, (p.1=0 ∨ p.2=0) → f p=0 := primePair_axes k
  have hfiber (m : ℕ) : (∑' p : {p : ℕ × ℕ | p.1*p.2=m}, f p) =
      ∑ p ∈ m.divisorsAntidiagonal, f p := by
    rw [tsum_subtype]
    rcases m.eq_zero_or_pos with rfl | hm
    · simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
      have hz : ∀ p : ℕ × ℕ, ({q : ℕ × ℕ | q.1*q.2=0}).indicator f p = 0 := by
        intro p
        by_cases hp : p.1*p.2=0
        · rw [indicator_of_mem (show p ∈ {q : ℕ × ℕ | q.1*q.2=0} from hp),
            hzero p (mul_eq_zero.mp hp)]
        · rw [indicator_of_notMem (show p ∉ {q : ℕ × ℕ | q.1*q.2=0} from hp)]
      simp only [hz, tsum_zero]
    · rw [tsum_eq_sum (s := m.divisorsAntidiagonal)]
      · apply Finset.sum_congr rfl
        intro p hp
        exact indicator_of_mem (show p ∈ {q : ℕ × ℕ | q.1*q.2=m} from (Nat.mem_divisorsAntidiagonal.mp hp).1) f
      · intro p hp
        apply indicator_of_notMem
        intro h
        exact hp (Nat.mem_divisorsAntidiagonal.mpr ⟨h,hm.ne'⟩)
  apply (summable_partition (primePair_nonneg k) (s := fun m => {p : ℕ × ℕ | p.1*p.2=m})
    (fun p => ⟨p.1*p.2,rfl,fun _ h => h.symm⟩)).mpr
  constructor
  · intro m
    rcases m.eq_zero_or_pos with rfl | hm
    · have hz : (fun p : {p : ℕ × ℕ | p.1*p.2=0} => f p) = fun _ => 0 := by
        funext p
        exact hzero p (mul_eq_zero.mp p.property)
      rw [hz]
      exact summable_zero
    · have he : {p : ℕ × ℕ | p.1*p.2=m} = (m.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
        ext p
        simp only [mem_setOf_eq, Finset.mem_coe, Nat.mem_divisorsAntidiagonal, and_iff_left hm.ne']
      have hfin : Finite {p : ℕ × ℕ | p.1*p.2=m} := by rw [he]; infer_instance
      letI := Fintype.ofFinite {p : ℕ × ℕ | p.1*p.2=m}
      exact hasSum_fintype _ |>.summable
  · change Summable (fun m => ∑' p : {p : ℕ × ℕ | p.1*p.2=m}, f p)
    have he (m : ℕ) : (∑' p : {p : ℕ × ℕ | p.1*p.2=m}, f p) =
        (m.divisorsAntidiagonal.card : ℝ)*Real.log m*|productKernel k m|/2 := by
      rw [hfiber]
      exact fiber_identity k m
    simp_rw [he]
    exact (summable_log_productKernel k).div_const 2

private theorem kernel_hasSum (k : ℕ) (y : ℝ) :
    HasSum (fun N : ℕ => (N.divisorsAntidiagonal.card : ℝ) * exp (y/2) *
      productKernel k ((N:ℝ)*exp y))
      (∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-y)).re) := by
  have h := (hasSum_sum (s := Finset.range ((riemannKernelPoly k).natDegree+1))
    (fun j _ => hasSum_sum (s := Finset.range ((riemannKernelPoly k).natDegree+1))
      (fun l _ => (summable_divisor_bessel j l y).hasSum.mul_left
        ((riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l)))).mul_left ((-1:ℝ)^k)
  convert h using 1 <;> try rfl
  · funext N
    simp only [productKernel, besselMonomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  · exact derivative_correlation_bessel k k y

/-- Exact correlation at every real shift; no asymptotic or truncation is used. -/
theorem correlation_productKernel (k : ℕ) (y : ℝ) :
    (∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-y)).re) =
      exp (y/2) * ∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) *
        productKernel k ((N:ℝ)*exp y) := by
  rw [← (kernel_hasSum k y).tsum_eq, ← tsum_mul_left]
  congr 1
  funext N
  ring

private theorem summable_kernel_row (k n : ℕ) (hn : 0 < n) :
    Summable (fun N : ℕ => (N.divisorsAntidiagonal.card : ℝ) * productKernel k (n*N:ℕ)) := by
  have h := (kernel_hasSum k (Real.log n)).summable.div_const (exp (Real.log n/2))
  convert h using 1 <;> try rfl
  funext N
  rw [exp_log (by positivity : (0:ℝ)<n)]
  push_cast
  rw [mul_comm (N:ℝ) (n:ℝ)]
  field_simp

private theorem correlation_nat (k n : ℕ) (hn : 0 < n) :
    (∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-Real.log n)).re) =
      √(n:ℝ) * ∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) * productKernel k (n*N:ℕ) := by
  rw [correlation_productKernel, exp_half, exp_log (by positivity : (0:ℝ)<n)]
  congr 1
  congr 1
  funext N
  push_cast
  rw [mul_comm (N:ℝ) (n:ℝ)]

private theorem prime_correlation_le_row (k n : ℕ) :
    vonMangoldt n / √(n:ℝ) *
      |∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-Real.log n)).re| ≤
        ∑' N : ℕ, primePair k (n,N) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [primePair]
  · rw [correlation_nat k n hn, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
    have hsqrt : √(n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.2 (by positivity))
    rw [show vonMangoldt n / √(n:ℝ) * (√(n:ℝ) *
        |∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) * productKernel k (n*N:ℕ)|) =
        vonMangoldt n * |∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) *
          productKernel k (n*N:ℕ)| by field_simp]
    calc _ ≤ vonMangoldt n * ∑' N : ℕ,
          |(N.divisorsAntidiagonal.card : ℝ) * productKernel k (n*N:ℕ)| := by
            apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
            simpa only [Real.norm_eq_abs] using
              norm_tsum_le_tsum_norm (summable_kernel_row k n hn).norm
         _ = _ := by
            rw [← tsum_mul_left]
            congr 1
            funext N
            simp only [primePair, abs_mul,
              abs_of_nonneg (Nat.cast_nonneg N.divisorsAntidiagonal.card : (0:ℝ) ≤ _)]
            ring

private theorem summable_prime_correlation (k : ℕ) :
    Summable (fun n : ℕ => vonMangoldt n / √(n:ℝ) *
      |∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-Real.log n)).re|) :=
  Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (div_nonneg vonMangoldt_nonneg (sqrt_nonneg _)) (abs_nonneg _))
    (prime_correlation_le_row k) (summable_primePair k).prod

/-- The complete absolute prime-correlation budget is controlled by one
logarithmically weighted product-kernel sum. All sums are convergent. -/
theorem full_prime_correlation_budget (k : ℕ) :
    (∑' n : ℕ, vonMangoldt n / √(n:ℝ) *
      |∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-Real.log n)).re|) ≤
      (∑' m : ℕ, (m.divisorsAntidiagonal.card : ℝ) * Real.log m * |productKernel k m|) / 2 := by
  have hs := summable_primePair k
  have hr := hasSum_divisorsAntidiagonal_regroup hs (primePair_axes k)
  calc _ ≤ ∑' n : ℕ, ∑' N : ℕ, primePair k (n,N) :=
          (summable_prime_correlation k).tsum_le_tsum (prime_correlation_le_row k) hs.prod
       _ = ∑' p : ℕ × ℕ, primePair k p := hs.tsum_prod.symm
       _ = ∑' m : ℕ, ∑ p ∈ m.divisorsAntidiagonal, primePair k p := hr.tsum_eq.symm
       _ = _ := by
          simp only [primePair]
          simp_rw [fiber_identity]
          exact tsum_div_const

end RHTower.WeilWorkDeficitPrimeKernel
