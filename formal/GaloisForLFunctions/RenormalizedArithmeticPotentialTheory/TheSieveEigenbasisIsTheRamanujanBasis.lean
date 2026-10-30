import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveOperatorHasTheAdjunctionEigenbasis
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes

/-!
# The sieve eigenbasis is the density-weighted Ramanujan basis

The local geometric ground and Blaschke excitation coefficients are precisely
normalized prime-power Ramanujan values. Coprime multiplicativity identifies
the complete sieve eigenbasis on its actual supported-integer carrier.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry BezoutValuationIncidence

private theorem normRamanujan_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  rw [normalizedRamanujanMode_eq_coefficient (by norm_num),
    TransThresholdPairCorrelation.ramanujanLagCoefficient_one]
  norm_num

private theorem normRamanujan_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (n : ℕ) :
    normalizedRamanujanMode (a * b) n =
      normalizedRamanujanMode a n * normalizedRamanujanMode b n := by
  rw [normalizedRamanujanMode_eq_coefficient (Nat.mul_pos ha hb),
    normalizedRamanujanMode_eq_coefficient ha, normalizedRamanujanMode_eq_coefficient hb,
    BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab,
    Nat.totient_mul hab, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), div_mul_div_comm]

private theorem normRamanujan_prime_succ (p : Nat.Primes) (k n : ℕ) (hn : n ≠ 0) :
    normalizedRamanujanMode ((p : ℕ) ^ (k + 1)) n =
      Real.sqrt (((p : ℕ) ^ (k + 1)).totient : ℝ) *
        valuationStep p (k + 1) (n.factorization p) := by
  have ht : 0 < (((p : ℕ) ^ (k + 1)).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos p.property.pos _)
  rw [normalizedRamanujanMode_eq_coefficient (pow_pos p.property.pos _),
    ramanujanCoefficient_prime_pow_eq_valuationStep p.property (by omega) hn]
  apply (div_eq_iff (Real.sqrt_pos.mpr ht).ne').mpr
  rw [mul_right_comm, Real.mul_self_sqrt ht.le]

private theorem primeBlaschkeParameter_pos (p : Nat.Primes) :
    0 < primeBlaschkeParameter p := by
  unfold primeBlaschkeParameter
  exact div_pos zero_lt_one (Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos))

private theorem primeBlaschkeGround_pos (p : Nat.Primes) :
    0 < 1 - primeBlaschkeParameter p ^ 2 := by
  rw [primeBlaschkeParameter_sq]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp)).mpr hp)

private theorem sqrt_totient_mul_primeBlaschke_pow (p : Nat.Primes) (k : ℕ) :
    Real.sqrt (((p : ℕ) ^ (k + 1)).totient : ℝ) *
        primeBlaschkeParameter p ^ (k + 1) =
      Real.sqrt (1 - primeBlaschkeParameter p ^ 2) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hsq : (Real.sqrt (((p : ℕ) ^ (k + 1)).totient : ℝ) *
      primeBlaschkeParameter p ^ (k + 1)) ^ 2 = 1 - primeBlaschkeParameter p ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm (k + 1) 2,
      pow_mul, primeBlaschkeParameter_sq, Nat.totient_prime_pow_succ p.property,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_sub p.property.one_lt.le, Nat.cast_one,
      div_pow, one_pow, pow_succ]
    field_simp
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg
    (primeBlaschkeParameter_pos p).le _)) (Real.sqrt_nonneg _)).mp
  rw [hsq, Real.sq_sqrt (primeBlaschkeGround_pos p).le]

private theorem hardyBlaschkeCoefficient_prime_eq (p : Nat.Primes) (k n : ℕ)
    (hn : n ≠ 0) :
    hardyBlaschkeCoefficient (primeBlaschkeParameter p) k (n.factorization p) =
      ((Real.sqrt (1 - primeBlaschkeParameter p ^ 2) *
        primeBlaschkeParameter p ^ n.factorization p *
          normalizedRamanujanMode ((p : ℕ) ^ k) n : ℝ) : ℂ) := by
  cases k with
  | zero => simp only [pow_zero, normRamanujan_one, mul_one, hardyBlaschkeCoefficient,
      Complex.ofReal_mul, Complex.ofReal_pow]
  | succ k =>
    rw [normRamanujan_prime_succ p k n hn]
    set q := primeBlaschkeParameter p
    set v := n.factorization (p : ℕ)
    set t := Real.sqrt (((p : ℕ) ^ (k + 1)).totient : ℝ)
    have hq : q ≠ 0 := (primeBlaschkeParameter_pos p).ne'
    have hs : 0 ≤ 1 - q ^ 2 := (primeBlaschkeGround_pos p).le
    have hscale : t * q ^ (k + 1) = Real.sqrt (1 - q ^ 2) :=
      sqrt_totient_mul_primeBlaschke_pow p k
    change hardyBlaschkeCoefficient q (k + 1) v =
      ((Real.sqrt (1 - q ^ 2) * q ^ v * (t * valuationStep p (k + 1) v) : ℝ) : ℂ)
    by_cases hv : k < v
    · have hkv : k + 1 ≤ v := by omega
      rw [hardyBlaschkeCoefficient, if_pos hv, valuationStep, if_pos hkv, mul_one]
      have heq : Real.sqrt (1 - q ^ 2) * q ^ v * t =
          (1 - q ^ 2) * q ^ (v - (k + 1)) := by
        have hvpow : q ^ v = q ^ (v - (k + 1)) * q ^ (k + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hkv]
        rw [hvpow]
        calc
          _ = (Real.sqrt (1 - q ^ 2) * (t * q ^ (k + 1))) *
              q ^ (v - (k + 1)) := by ring
          _ = _ := by rw [hscale, Real.mul_self_sqrt hs]
      rw [heq]
      push_cast
      rfl
    · rw [hardyBlaschkeCoefficient, if_neg hv, valuationStep, if_neg (by omega : ¬ k + 1 ≤ v)]
      by_cases heq : v = k
      · rw [heq, if_pos rfl, if_pos rfl]
        have hprod : (Real.sqrt (1 - q ^ 2) * q ^ k * t) * q = 1 - q ^ 2 := by
          calc
            _ = Real.sqrt (1 - q ^ 2) * (t * q ^ (k + 1)) := by rw [pow_succ]; ring
            _ = _ := by rw [hscale, Real.mul_self_sqrt hs]
        have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
        have hqrel : q ^ 2 * ((p : ℕ) : ℝ) = 1 := by
          rw [primeBlaschkeParameter_sq]
          exact div_mul_cancel₀ _ (zero_lt_one.trans hp).ne'
        have hA : Real.sqrt (1 - q ^ 2) * q ^ k * t = q * (((p : ℕ) : ℝ) - 1) := by
          apply mul_right_cancel₀ hq
          nlinarith only [hprod, hqrel]
        have hreal : Real.sqrt (1 - q ^ 2) * q ^ k *
            (t * (-(1 / (((p : ℕ) : ℝ) - 1)))) = -q := by
          calc
            _ = (Real.sqrt (1 - q ^ 2) * q ^ k * t) *
                (-(1 / (((p : ℕ) : ℝ) - 1))) := by ring
            _ = (q * (((p : ℕ) : ℝ) - 1)) * (-(1 / (((p : ℕ) : ℝ) - 1))) := by rw [hA]
            _ = -q := by field_simp [(sub_pos.mpr hp).ne']
        rw [hreal]
        push_cast
        rfl
      · rw [if_neg heq, if_neg (by omega : ¬ v + 1 = k + 1), mul_zero, mul_zero,
          Complex.ofReal_zero]


private theorem normRamanujan_prime_product (Q : Finset Nat.Primes)
    (e : Nat.Primes → ℕ) (n : ℕ) :
    normalizedRamanujanMode (∏ p ∈ Q, (p : ℕ) ^ e p) n =
      ∏ p ∈ Q, normalizedRamanujanMode ((p : ℕ) ^ e p) n := by
  induction Q using Finset.induction_on with
  | empty => simp only [prod_empty, normRamanujan_one]
  | @insert p Q hpQ ih =>
    have hcop : Nat.Coprime ((p : ℕ) ^ e p) (∏ q ∈ Q, (q : ℕ) ^ e q) :=
      Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _
        ((Nat.coprime_primes p.property q.property).mpr (fun hpq =>
          hpQ ((Subtype.ext hpq).symm ▸ hq)))
    have hpos : 0 < ∏ q ∈ Q, (q : ℕ) ^ e q :=
      Finset.prod_pos fun q _ => pow_pos q.property.pos _
    rw [prod_insert hpQ, prod_insert hpQ,
      normRamanujan_mul (pow_pos p.property.pos _) hpos hcop, ih]

/-- Reconstruct a supported integer using every prime of its sieve, including zero valuations. -/
theorem prod_prime_pow_factorization_sieve {Q : Finset Nat.Primes} {n : ℕ}
    (hn : SieveSupported Q n) :
    (∏ p ∈ Q, (p : ℕ) ^ n.factorization p) = n := by
  calc
    _ = primeProduct (sieveExponentVector Q (fun p => n.factorization (p : Nat.Primes))) := by
      rw [primeProduct, Finsupp.prod_of_support_subset _
        (sieveExponentVector_support_subset Q _) _ (fun _ _ => pow_zero _)]
      apply Finset.prod_congr rfl
      intro p hp
      rw [sieveExponentVector_apply, dif_pos hp]
    _ = primeProduct (primeExponentVector n) := by rw [sieveExponentVector_factorization hn]
    _ = n := primeProduct_primeExponentVector hn.pos.ne'

/-- The product geometric ground weight is exactly the square root of the arithmetic class density. -/
theorem prod_primeBlaschkeGround_eq_sqrt_density (Q : Finset Nat.Primes) (n : SieveClass Q) :
    (∏ p : Q, Real.sqrt (1 - primeBlaschkeParameter p ^ 2) *
      primeBlaschkeParameter p ^ (n : ℕ).factorization (p : Nat.Primes)) =
        Real.sqrt (sieveClassDensity Q n) := by
  have hden : (∏ p : Q, (((p : Nat.Primes) : ℕ) : ℝ) ^
      (n : ℕ).factorization (p : Nat.Primes)) = ((n : ℕ) : ℝ) := by
    calc
      _ = ((∏ p : Q, ((p : Nat.Primes) : ℕ) ^
          (n : ℕ).factorization (p : Nat.Primes) : ℕ) : ℝ) := by
            simp only [Nat.cast_prod, Nat.cast_pow]
      _ = ((n : ℕ) : ℝ) := by
        rw [Finset.prod_coe_sort Q (fun p : Nat.Primes =>
          (p : ℕ) ^ (n : ℕ).factorization p), prod_prime_pow_factorization_sieve n.property]
  have hnum : (∏ p : Q, (1 - 1 / (((p : Nat.Primes) : ℕ) : ℝ))) = sieveDensity Q := by
    rw [Finset.prod_coe_sort Q (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ))]
    simp only [sieveDensity, one_div]
  have hsq : (∏ p : Q, Real.sqrt (1 - primeBlaschkeParameter p ^ 2) *
      primeBlaschkeParameter p ^ (n : ℕ).factorization (p : Nat.Primes)) ^ 2 =
        sieveClassDensity Q n := by
    calc
      _ = ∏ p : Q, (1 - 1 / (((p : Nat.Primes) : ℕ) : ℝ)) /
          (((p : Nat.Primes) : ℕ) : ℝ) ^ (n : ℕ).factorization (p : Nat.Primes) := by
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro p _
        rw [mul_pow, Real.sq_sqrt (primeBlaschkeGround_pos p).le,
          ← pow_mul, mul_comm ((n : ℕ).factorization (p : Nat.Primes)) 2, pow_mul,
          primeBlaschkeParameter_sq, div_pow, one_pow]
        ring
      _ = (∏ p : Q, (1 - 1 / (((p : Nat.Primes) : ℕ) : ℝ))) /
          (∏ p : Q, (((p : Nat.Primes) : ℕ) : ℝ) ^
            (n : ℕ).factorization (p : Nat.Primes)) := Finset.prod_div_distrib _ _
      _ = sieveClassDensity Q n := by rw [hnum, hden]; rfl
  have hnonneg : 0 ≤ ∏ p : Q, Real.sqrt (1 - primeBlaschkeParameter p ^ 2) *
      primeBlaschkeParameter p ^ (n : ℕ).factorization (p : Nat.Primes) :=
    Finset.prod_nonneg fun p _ => mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg (primeBlaschkeParameter_pos p).le _)
  rw [← hsq, Real.sqrt_sq hnonneg]

/-- The actual complete sieve eigenbasis is the density-weighted normalized Ramanujan basis. -/
theorem sieveAdjunctionBasis_eq_normalizedRamanujan (Q : Finset Nat.Primes)
    (m n : SieveClass Q) :
    sieveAdjunctionBasis Q m n =
      ((Real.sqrt (sieveClassDensity Q n) * normalizedRamanujanMode m n : ℝ) : ℂ) := by
  have hmode : (∏ p : Q, normalizedRamanujanMode
      (((p : Nat.Primes) : ℕ) ^ (m : ℕ).factorization (p : Nat.Primes)) n) =
        normalizedRamanujanMode m n := by
    rw [Finset.prod_coe_sort Q (fun p : Nat.Primes =>
      normalizedRamanujanMode ((p : ℕ) ^ (m : ℕ).factorization p) n),
      ← normRamanujan_prime_product,
      prod_prime_pow_factorization_sieve m.property]
  rw [sieveAdjunctionBasis_coefficients]
  simp_rw [hardyBlaschkeCoefficient_prime_eq _ _ _ n.property.pos.ne']
  rw [← Complex.ofReal_prod, Finset.prod_mul_distrib,
    prod_primeBlaschkeGround_eq_sqrt_density, hmode]

/-- Arithmetic class densities form a probability distribution on the supported integers. -/
theorem hasSum_sieveClassDensity (Q : Finset Nat.Primes) :
    HasSum (fun n : SieveClass Q => sieveClassDensity Q n) 1 := by
  let ground : SieveClass Q := ⟨1, ⟨0, by simp⟩⟩
  have hcoeff (n : SieveClass Q) :
      ‖sieveAdjunctionBasis Q ground n‖ ^ 2 = sieveClassDensity Q n := by
    rw [sieveAdjunctionBasis_eq_normalizedRamanujan]
    change ‖((Real.sqrt (sieveClassDensity Q n) * normalizedRamanujanMode 1 n : ℝ) : ℂ)‖ ^ 2 = _
    rw [normRamanujan_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (sieveClassDensity_pos n.property).le]
  have hs : HasSum (fun n : SieveClass Q => ‖sieveAdjunctionBasis Q ground n‖ ^ 2)
      (‖sieveAdjunctionBasis Q ground‖ ^ 2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (sieveAdjunctionBasis Q ground)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  simpa only [hcoeff, (sieveAdjunctionBasis Q).orthonormal.norm_eq_one ground, one_pow] using hs

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sieveAdjunctionBasis_eq_normalizedRamanujan
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.hasSum_sieveClassDensity

