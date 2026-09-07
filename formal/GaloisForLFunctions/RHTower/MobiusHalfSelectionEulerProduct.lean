import GaloisForLFunctions.RHTower.MobiusDivisorBernoulliPrimeEnergy
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Euler product of the literal half-selection Möbius source

The actual Bernoulli mean uses `a(n)=μ(n)/2^ω(n)`. This module retains those
coefficients in an arithmetic function, proves multiplicativity and absolute
convergence on `Re s > 1`, and identifies the local factor `1-p^(-s)/2`.
Its square times zeta is the exact prime-square correction product
`∏ₚ (1 + p^(-2s)/(4(1-p^(-s))))`. Analytic continuation of the correction
is proved separately; these identities alone assert no growth obstruction or RH.
-/

noncomputable section
open Finset Filter Topology
open scoped ArithmeticFunction.zeta
namespace RHTower

/-- The literal real half-selection coefficients, cast into arithmetic-function form. -/
def halfSelectionMoebiusAF : ArithmeticFunction ℂ :=
  ⟨fun n => (halfSelectionMoebiusWeight n : ℂ), by simp [halfSelectionMoebiusWeight]⟩

/-- Exact equality with the coefficients of the already formal Bernoulli mean. -/
theorem halfSelectionMoebiusAF_apply (n : ℕ) :
    halfSelectionMoebiusAF n = (halfSelectionMoebiusWeight n : ℂ) := rfl

/-- The source has the required unit coefficient. -/
@[simp] theorem halfSelectionMoebiusAF_one : halfSelectionMoebiusAF 1 = 1 := by
  simp [halfSelectionMoebiusAF_apply,halfSelectionMoebiusWeight]

/-- Coprime prime-factor supports make the literal source multiplicative. -/
theorem halfSelectionMoebiusAF_isMultiplicative : halfSelectionMoebiusAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨halfSelectionMoebiusAF_one, ?_⟩
  intro m n hm hn hcop
  have hmu := ArithmeticFunction.isMultiplicative_moebius.2 hcop
  simp only [halfSelectionMoebiusAF_apply,halfSelectionMoebiusWeight,
    Nat.primeFactors_mul hm hn,card_union_of_disjoint hcop.disjoint_primeFactors,pow_add,hmu]
  push_cast
  ring

/-- Every source coefficient has norm at most one. -/
theorem norm_halfSelectionMoebiusAF_le_one (n : ℕ) : ‖halfSelectionMoebiusAF n‖ ≤ 1 := by
  rw [halfSelectionMoebiusAF_apply,Complex.norm_real,Real.norm_eq_abs,halfSelectionMoebiusWeight,
    abs_div,abs_of_nonneg (by positivity : (0:ℝ)≤2^n.primeFactors.card)]
  have hm : |((ArithmeticFunction.moebius n : ℤ):ℝ)|≤1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  have hp : (1:ℝ)≤2^n.primeFactors.card := one_le_pow₀ (by norm_num)
  exact (div_le_one (by positivity)).2 (hm.trans hp)

/-- The first local coefficient is minus one half. -/
theorem halfSelectionMoebiusAF_prime {p : ℕ} (hp : p.Prime) :
    halfSelectionMoebiusAF p = -(1/2:ℂ) := by
  norm_num [halfSelectionMoebiusAF_apply,halfSelectionMoebiusWeight,ArithmeticFunction.moebius_apply_prime hp,hp.primeFactors]

/-- All higher local coefficients vanish by Möbius squarefreeness. -/
theorem halfSelectionMoebiusAF_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2≤k) :
    halfSelectionMoebiusAF (p^k) = 0 := by
  simp [halfSelectionMoebiusAF_apply,halfSelectionMoebiusWeight,ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k≠0),
    show k≠1 by omega]

/-- Absolute summability throughout the Euler half-plane. -/
theorem LSeriesSummable_halfSelectionMoebiusAF {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable halfSelectionMoebiusAF s := by
  refine Summable.of_norm_bounded (summable_riemannZetaSummand hs) ?_
  intro n
  rw [LSeries.term_def]
  split_ifs with hn
  · simp [hn]
  · change ‖halfSelectionMoebiusAF n / (n:ℂ)^s‖ ≤ ‖(n:ℂ)^(-s)‖
    rw [Complex.cpow_neg,div_eq_mul_inv,norm_mul]
    simpa using mul_le_mul_of_nonneg_right (norm_halfSelectionMoebiusAF_le_one n)
      (norm_nonneg ((n:ℂ)^s)⁻¹)

private theorem halfSelection_term_mul {m n : ℕ} (hcop : m.Coprime n) (s : ℂ) :
    LSeries.term halfSelectionMoebiusAF s (m*n) =
      LSeries.term halfSelectionMoebiusAF s m*LSeries.term halfSelectionMoebiusAF s n := by
  simp only [LSeries.term_def₀ (show halfSelectionMoebiusAF 0=0 from halfSelectionMoebiusAF.map_zero)]
  have hpow : ((m*n:ℕ):ℂ)^(-s)=(m:ℂ)^(-s)*(n:ℂ)^(-s) := by
    simpa only [Nat.cast_mul,Complex.ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)
  rw [halfSelectionMoebiusAF_isMultiplicative.2 hcop,hpow]
  ring

private theorem halfSelection_local_sum (p : Nat.Primes) (s : ℂ) :
    (∑' k : ℕ, LSeries.term halfSelectionMoebiusAF s ((p:ℕ)^k)) =
      1-((p:ℕ):ℂ)^(-s)/2 := by
  have hsupport : ∀ k ∉ ({0,1}:Finset ℕ),
      LSeries.term halfSelectionMoebiusAF s ((p:ℕ)^k)=0 := by
    intro k hk
    have hk2 : 2≤k := by simp only [mem_insert,mem_singleton,not_or] at hk; omega
    simp [LSeries.term_def₀ (show halfSelectionMoebiusAF 0=0 from halfSelectionMoebiusAF.map_zero),
      halfSelectionMoebiusAF_prime_pow p.2 hk2]
  rw [tsum_eq_sum hsupport]
  simp [LSeries.term_def₀ (show halfSelectionMoebiusAF 0=0 from halfSelectionMoebiusAF.map_zero),
    halfSelectionMoebiusAF_prime p.2]
  ring

/-- The local Euler factors of the actual half-selection source. -/
theorem hasProd_halfSelectionMoebiusAF {s : ℂ} (hs : 1<s.re) :
    HasProd (fun p : Nat.Primes => 1-((p:ℕ):ℂ)^(-s)/2) (LSeries halfSelectionMoebiusAF s) := by
  have hp := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term halfSelectionMoebiusAF s)
    (by simp) (fun {m n} hc => halfSelection_term_mul hc s)
    (LSeriesSummable_halfSelectionMoebiusAF hs).norm (by simp)
  simpa only [halfSelection_local_sum,LSeries] using hp

/-- The prime-square correction left after squaring the actual local factor. -/
def halfSelectionEulerCorrectionLocal (p : Nat.Primes) (s : ℂ) : ℂ :=
  1+(((p:ℕ):ℂ)^(-s))^2/(4*(1-((p:ℕ):ℂ)^(-s)))

/-- The source-defined prime-square correction product. -/
def halfSelectionEulerCorrection (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, halfSelectionEulerCorrectionLocal p s

/-- Every prime kernel lies in the open unit disc when the real part is positive. -/
theorem norm_halfSelection_prime_cpow_neg_lt_one (p : Nat.Primes) {s : ℂ} (hs : 0<s.re) :
    ‖((p:ℕ):ℂ)^(-s)‖<1 := by
  have hp : (1:ℝ)<(p:ℕ) := by exact_mod_cast p.2.one_lt
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos,Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hs)

private theorem halfSelection_correction_identity {x : ℂ} (hx : 1-x≠0) :
    (1-x/2)*(1-x/2)*(1-x)⁻¹ = 1+x^2/(4*(1-x)) := by
  field_simp
  ring

/-- Exact squared Euler identity, with its convergent product certificate. -/
theorem hasProd_halfSelectionEulerCorrection {s : ℂ} (hs : 1<s.re) :
    HasProd (fun p : Nat.Primes => halfSelectionEulerCorrectionLocal p s)
      ((LSeries halfSelectionMoebiusAF s)^2*riemannZeta s) := by
  have hp := ((hasProd_halfSelectionMoebiusAF hs).mul
    (hasProd_halfSelectionMoebiusAF hs)).mul (riemannZeta_eulerProduct_hasProd hs)
  have hlocal (p : Nat.Primes) :
      (1-((p:ℕ):ℂ)^(-s)/2)*(1-((p:ℕ):ℂ)^(-s)/2)*(1-((p:ℕ):ℂ)^(-s))⁻¹ =
        halfSelectionEulerCorrectionLocal p s := by
    apply halfSelection_correction_identity
    exact sub_ne_zero.mpr (fun h => by
      have hb := norm_halfSelection_prime_cpow_neg_lt_one p (lt_trans zero_lt_one hs)
      rw [← h] at hb
      norm_num at hb)
  simpa only [hlocal,pow_two] using hp

/-- The correction equals the squared actual source times zeta on `Re s > 1`. -/
theorem halfSelectionEulerCorrection_eq_LSeries_sq_mul_zeta {s : ℂ} (hs : 1<s.re) :
    halfSelectionEulerCorrection s = (LSeries halfSelectionMoebiusAF s)^2*riemannZeta s :=
  (hasProd_halfSelectionEulerCorrection hs).tprod_eq

end RHTower
