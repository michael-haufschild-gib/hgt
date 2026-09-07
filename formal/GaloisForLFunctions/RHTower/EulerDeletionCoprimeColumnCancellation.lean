import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeThreeQuarterSigmaBound
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeLogExpansion
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Complete coprime Möbius columns and their quantitative cancellation

A complete floor column is exactly a finite-prime-support count. Its Rankin
bound gives an unconditional near-linear estimate for the signed correlation,
uniformly over the outer divisor selection. Removing the unit divisor from
both columns exposes the exact quadratic tail polynomial. These estimates do
not bound the full compensated EDQ energy at growing cutoffs.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators
attribute [local instance] Classical.propDecidable
namespace RHTower.DeletionCoprimeColumn
open Sieve

private theorem supported_norm_lt {r p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0<a) :
    ‖primeSupportedRpowHom r a p‖<1 := by
  by_cases hs : primeSupportedOn r p
  · simp only [primeSupportedRpowHom,hs,if_true,MonoidHom.coe_mk,OneHom.coe_mk,
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  · simp [primeSupportedRpowHom,hs]

/-- The complete positive mass on a finite prime support, for any positive exponent. -/
theorem hasSum_supportedRpow {r : ℕ} (hr : 0<r) {a : ℝ} (ha : 0<a) :
    HasSum (fun n : ℕ => primeSupportedRpowHom r a n)
      (∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹) := by
  have he := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := primeSupportedRpowHom r a) (fun {_} hp => supported_norm_lt hp ha) (r+1)
  have hsub := hasSum_subtype_iff_indicator.mp he.2
  have hind : ((r+1).smoothNumbers : Set ℕ).indicator (fun n => primeSupportedRpowHom r a n) =
      fun n => primeSupportedRpowHom r a n := by
    funext n
    by_cases hs : primeSupportedOn r n
    · simp [Set.indicator,primeSupportedOn_mem_smoothNumbers hr hs]
    · simp [Set.indicator,primeSupportedRpowHom,hs]
  rw [hind] at hsub
  have hsubset : r.primeFactors ⊆ (r+1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨by
      have := Nat.le_of_dvd hr (Nat.mem_primeFactors.mp hp).2.1
      omega, Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ (r+1).primesBelow, (1-primeSupportedRpowHom r a p)⁻¹) =
      ∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹ := by
    rw [← Finset.prod_subset hsubset (by
      intro p hp hnot
      have hpr := (Nat.mem_primesBelow.mp hp).2
      have hs : ¬primeSupportedOn r p := by
        intro hs
        exact hnot (Nat.mem_primeFactors.mpr ⟨hpr,hs p hpr dvd_rfl,by omega⟩)
      simp [primeSupportedRpowHom,hs])]
    apply Finset.prod_congr rfl
    intro p hp
    have hs : primeSupportedOn r p := by
      intro q hq hqp
      have heq := (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hp)).mp hqp
      rcases heq with heq | heq
      · exact (hq.ne_one heq).elim
      · simpa [heq] using (Nat.mem_primeFactors.mp hp).2.1
    simp [primeSupportedRpowHom,hs]
  rwa [hprod] at hsub

private theorem geo_one_le {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0<a) :
    1 ≤ (1-(p : ℝ)^(-a))⁻¹ := by
  have hpow := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt : (1 : ℝ)<p) (by linarith : -a<0)
  have hnn := Real.rpow_nonneg (Nat.cast_nonneg p) (-a)
  rw [one_le_inv₀ (by linarith : 0<1-(p : ℝ)^(-a))]
  linarith

/-- Finite-support Euler mass has an arbitrarily small power bound in its modulus. -/
theorem exists_supportedEulerMass_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℕ, 0<r →
      (∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹) ≤ C*(r : ℝ)^b := by
  obtain ⟨P,hP⟩ := exists_nat_gt (max ((2 : ℝ)^(1/a)) ((2 : ℝ)^(1/b)))
  let f : ℕ → ℝ := fun p => (1-(p : ℝ)^(-a))⁻¹
  let C : ℝ := ∏ p ∈ P.primesBelow, f p
  have hf1 {p : ℕ} (hp : p.Prime) : 1≤f p := geo_one_le hp ha
  have hC1 : 1≤C := Finset.one_le_prod (fun p hp => hf1 (Nat.mem_primesBelow.mp hp).2)
  refine ⟨C,by linarith,?_⟩
  intro r hr
  have hlarge {p : ℕ} (hp : p.Prime) (hPp : P≤p) : f p ≤ (p : ℝ)^b := by
    have hnat : (P : ℝ)≤p := by exact_mod_cast hPp
    have hpa : (2 : ℝ)^(1/a) ≤ p := (le_max_left _ _).trans (hP.le.trans hnat)
    have hpb : (2 : ℝ)^(1/b) ≤ p := (le_max_right _ _).trans (hP.le.trans hnat)
    have hpowa : (2 : ℝ)≤(p : ℝ)^a := by
      have h := Real.rpow_le_rpow (by positivity) hpa ha.le
      rw [← Real.rpow_mul (by norm_num)] at h
      simpa [ha.ne'] using h
    have hpowb : (2 : ℝ)≤(p : ℝ)^b := by
      have h := Real.rpow_le_rpow (by positivity) hpb hb.le
      rw [← Real.rpow_mul (by norm_num)] at h
      simpa [hb.ne'] using h
    have hhalf : (p : ℝ)^(-a) ≤ 1/2 := by
      rw [Real.rpow_neg (Nat.cast_nonneg p)]
      simpa only [one_div] using (inv_le_inv₀ (by positivity) (by norm_num)).mpr hpowa
    have hf : f p ≤ 2 := by
      dsimp [f]
      calc (1-(p : ℝ)^(-a))⁻¹ ≤ (1/2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (by linarith) (by norm_num)).mpr (by linarith)
        _ = 2 := by norm_num
    exact hf.trans hpowb
  have hterm : ∀ p ∈ r.primeFactors,
      f p ≤ (if p<P then f p else 1)*(p : ℝ)^b := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_cases hsmall : p<P
    · rw [if_pos hsmall]
      exact le_mul_of_one_le_right (by linarith [hf1 hprime])
        (Real.one_le_rpow (by exact_mod_cast hprime.one_lt.le) hb.le)
    · rw [if_neg hsmall,one_mul]
      exact hlarge hprime (by omega)
  have hsmall : (∏ p ∈ r.primeFactors, if p<P then f p else 1) ≤ C := by
    rw [← Finset.prod_filter]
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨hlt,Nat.prime_of_mem_primeFactors hp⟩
    · intro p hp
      exact (hf1 (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).trans' zero_le_one
    · intro p hp _
      exact hf1 (Nat.mem_primesBelow.mp hp).2
  have hrad : (∏ p ∈ r.primeFactors, (p : ℝ)^b) ≤ (r : ℝ)^b := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    apply Real.rpow_le_rpow (by positivity) _ hb.le
    simpa only [Nat.cast_prod] using (show ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) ≤ r by
      exact_mod_cast Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r))
  calc
    _ ≤ ∏ p ∈ r.primeFactors, (if p<P then f p else 1)*(p : ℝ)^b :=
      Finset.prod_le_prod (fun p hp => (hf1 (Nat.prime_of_mem_primeFactors hp)).trans' zero_le_one) hterm
    _ = (∏ p ∈ r.primeFactors, if p<P then f p else 1)*(∏ p ∈ r.primeFactors,(p : ℝ)^b) := Finset.prod_mul_distrib
    _ ≤ C*(r : ℝ)^b := mul_le_mul hsmall hrad (by positivity) (by linarith)

/-- Rankin's bound retains precisely the primes of the source modulus. -/
theorem supportedCount_le_mass {r R : ℕ} (hr : 0<r) (_hR : 0<R) {a : ℝ} (ha : 0<a) :
    ((primeSupportedIcc r R).card : ℝ) ≤
      (R : ℝ)^a*(∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹) := by
  classical
  have hsum := hasSum_supportedRpow hr ha
  have hnn (n : ℕ) : 0≤primeSupportedRpowHom r a n := by
    dsimp [primeSupportedRpowHom]
    split_ifs <;> positivity
  have hfin : (∑ n ∈ primeSupportedIcc r R, primeSupportedRpowHom r a n) ≤
      ∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹ :=
    hsum.tsum_eq ▸ Summable.sum_le_tsum _ (fun n _ => hnn n) hsum.summable
  calc
    ((primeSupportedIcc r R).card : ℝ) = ∑ _n ∈ primeSupportedIcc r R, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ primeSupportedIcc r R, (R : ℝ)^a*primeSupportedRpowHom r a n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1,hnR⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast hn1
      have hpow : (n : ℝ)^a ≤ (R : ℝ)^a :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hnR) ha.le
      simp only [primeSupportedRpowHom,hs,if_true,MonoidHom.coe_mk,OneHom.coe_mk]
      rw [Real.rpow_neg hn0.le]
      exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hn0 a)).mpr (by simpa using hpow)
    _ = (R : ℝ)^a*(∑ n ∈ primeSupportedIcc r R, primeSupportedRpowHom r a n) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg (Nat.cast_nonneg R) a)

/-- The complete-column support count has independent arbitrarily small exponents. -/
theorem exists_supportedCount_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ r R : ℕ, 0<r → 0<R →
      ((primeSupportedIcc r R).card : ℝ) ≤ C*(R : ℝ)^a*(r : ℝ)^b := by
  obtain ⟨C,hC,hbound⟩ := exists_supportedEulerMass_le ha hb
  refine ⟨C,hC,?_⟩
  intro r R hr hR
  calc
    _ ≤ (R : ℝ)^a*(∏ p ∈ r.primeFactors, (1-(p : ℝ)^(-a))⁻¹) := supportedCount_le_mass hr hR ha
    _ ≤ (R : ℝ)^a*(C*(r : ℝ)^b) := mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)
    _ = _ := by ring

private def coprimeMobius (r : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if r.Coprime n then μ n else 0, by simp⟩

private def supportIndicator (r : ℕ) : ArithmeticFunction ℤ := by
  classical
  exact ⟨fun n => if n ≠ 0 ∧ primeSupportedOn r n then 1 else 0, by simp⟩

private theorem coprimeMobius_mult (r : ℕ) : (coprimeMobius r).IsMultiplicative := by
  constructor
  · simp [coprimeMobius]
  · intro m n hmn
    have hm := isMultiplicative_moebius.map_mul_of_coprime hmn
    change (if r.Coprime (m*n) then μ (m*n) else 0) =
      (if r.Coprime m then μ m else 0)*(if r.Coprime n then μ n else 0)
    split_ifs with h h1 h2 h2 h1 h2 h2
    · exact hm
    all_goals simp_all only [Nat.coprime_mul_iff_right, and_self, and_false,
      false_and, zero_mul, mul_zero]
    all_goals tauto


private theorem supportIndicator_mult (r : ℕ) : (supportIndicator r).IsMultiplicative := by
  classical
  constructor
  · simp [supportIndicator]
  · intro m n _
    by_cases hm0 : m = 0
    · simp [supportIndicator, hm0]
    by_cases hn0 : n = 0
    · simp [supportIndicator, hn0]
    by_cases hm : primeSupportedOn r m <;> by_cases hn : primeSupportedOn r n <;>
      simp [supportIndicator, Nat.mul_ne_zero hm0 hn0, primeSupportedOn_mul_iff,
        hm0, hn0, hm, hn]

private theorem coprimeMobius_zeta (r : ℕ) :
    coprimeMobius r * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) =
      supportIndicator r := by
  classical
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((coprimeMobius_mult r).mul isMultiplicative_zeta.natCast) _
    (supportIndicator_mult r)).mpr
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  cases i with
  | zero => simp [coprimeMobius, supportIndicator]
  | succ i =>
    have hsum : ∀ k : ℕ, (∑ j ∈ range (k+2), coprimeMobius r (p^j)) =
        if p ∣ r then 1 else 0 := by
      intro k
      induction k with
      | zero =>
        have hcop : r.Coprime p ↔ ¬p ∣ r := by
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        by_cases hpr : p ∣ r <;>
          simp [Finset.sum_range_succ, coprimeMobius, hcop, moebius_apply_prime hp, hpr]
      | succ k ih =>
        rw [show k+1+2 = (k+2)+1 by omega, Finset.sum_range_succ, ih]
        have hz : coprimeMobius r (p^(k+2)) = 0 := by
          simp [coprimeMobius, moebius_apply_prime_pow hp (by omega : k+2 ≠ 0),
            show k+2 ≠ 1 by omega]
        rw [hz, add_zero]
    rw [hsum]
    simp [supportIndicator, hp.ne_zero,
      primeSupportedOn_prime_pow_iff hp (by omega : 1 ≤ i+1)]

/-- Complete coprime Möbius inversion leaves exactly the prime-support indicator. -/
theorem sum_coprime_moebius_divisors (r : ℕ) {n : ℕ} (hn : 0<n) :
    (∑ e ∈ n.divisors, if r.Coprime e then (μ e : ℤ) else 0) =
      if primeSupportedOn r n then 1 else 0 := by
  classical
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (coprimeMobius_zeta r)
  rw [coe_mul_zeta_apply] at h
  change (∑ e ∈ n.divisors, if r.Coprime e then μ e else 0) =
    (if n ≠ 0 ∧ primeSupportedOn r n then 1 else 0) at h
  by_cases hs : primeSupportedOn r n
  · rw [if_pos ⟨hn.ne', hs⟩] at h
    rw [if_pos hs]
    exact h
  · rw [if_neg (fun h => hs h.2)] at h
    rw [if_neg hs]
    exact h

/-- Summing a complete floor column counts integers on the prescribed prime support. -/
theorem complete_floor_column (r R : ℕ) :
    (∑ e ∈ Icc 1 R, (if r.Coprime e then ((μ e : ℤ) : ℝ) else 0) * (R/e : ℕ)) =
      ((primeSupportedIcc r R).card : ℝ) := by
  classical
  have hswap := sum_divisors_swap R
    (fun e _ => if r.Coprime e then ((μ e : ℤ) : ℝ) else 0)
  have hdiv : ∀ n ∈ Icc 1 R,
      (∑ e ∈ n.divisors, if r.Coprime e then ((μ e : ℤ) : ℝ) else 0) =
        if primeSupportedOn r n then (1 : ℝ) else 0 := by
    intro n hn
    exact_mod_cast sum_coprime_moebius_divisors r (mem_Icc.mp hn).1
  have hcard : (∑ n ∈ Icc 1 R, if primeSupportedOn r n then (1 : ℝ) else 0) =
      ((primeSupportedIcc r R).card : ℝ) := by
    simp [primeSupportedIcc]
  rw [sum_congr rfl hdiv, hcard] at hswap
  simpa [mul_comm] using hswap.symm

/-- A complete inner floor column, with an arbitrary outer divisor selection. -/
def floorCorrelation (A : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ d ∈ A ∩ Icc 1 R, ((μ d : ℤ) : ℝ) * (R/d : ℕ) *
    ∑ e ∈ Icc 1 R, (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0) * (R/e : ℕ)

/-- Actual signed floor correlation has a near-linear bound, uniformly in the outer selection. -/
theorem exists_floorCorrelation_le {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Finset ℕ) (R : ℕ),
      |floorCorrelation A R| ≤ C*(R : ℝ)^(1+ε) := by
  let δ : ℝ := ε/3
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hcount⟩ := exists_supportedCount_le hδ hδ
  refine ⟨C*(1+1/δ), by positivity, ?_⟩
  intro A R
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp [floorCorrelation, Real.zero_rpow (by linarith : 1+ε ≠ 0)]
  have hR1 : (1 : ℝ)≤R := by exact_mod_cast hR
  have hR0 : (0 : ℝ)<R := by exact_mod_cast hR
  have hpoint : ∀ d ∈ Icc 1 R,
      |((μ d : ℤ) : ℝ)*(R/d : ℕ)*((primeSupportedIcc d R).card : ℝ)| ≤
        (C*(R : ℝ)^(1+2*δ))*(1/(d : ℝ)) := by
    intro d hd
    have hdpos : 0<d := (mem_Icc.mp hd).1
    have hdpow : (d : ℝ)^δ ≤ (R : ℝ)^δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast (mem_Icc.mp hd).2) hδ.le
    have hs : ((primeSupportedIcc d R).card : ℝ) ≤ C*(R : ℝ)^(2*δ) := by
      calc
        _ ≤ C*(R : ℝ)^δ*(d : ℝ)^δ := hcount d R hdpos hR
        _ ≤ C*(R : ℝ)^δ*(R : ℝ)^δ := mul_le_mul_of_nonneg_left hdpow (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hR0]; congr 2; ring
    have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    calc
      _ = |((μ d : ℤ) : ℝ)| *(R/d : ℕ)*((primeSupportedIcc d R).card : ℝ) := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (R/d : ℕ) by positivity),
          abs_of_nonneg (show (0 : ℝ) ≤ ((primeSupportedIcc d R).card : ℝ) by positivity)]
      _ ≤ 1*((R : ℝ)/d)*(C*(R : ℝ)^(2*δ)) := by
        apply mul_le_mul (mul_le_mul hmu Nat.cast_div_le (Nat.cast_nonneg _) (by norm_num)) hs
          (Nat.cast_nonneg _) (by positivity)
      _ = (C*(R : ℝ)^(1+2*δ))*(1/(d : ℝ)) := by
        rw [Real.rpow_add hR0, Real.rpow_one]; ring
  have habs : |floorCorrelation A R| ≤
      C*(R : ℝ)^(1+2*δ)*(1+Real.log R) := by
    calc
      _ ≤ ∑ d ∈ A ∩ Icc 1 R,
          |((μ d : ℤ) : ℝ)*(R/d : ℕ)*((primeSupportedIcc d R).card : ℝ)| := by
        simp only [floorCorrelation, complete_floor_column]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 R,
          |((μ d : ℤ) : ℝ)*(R/d : ℕ)*((primeSupportedIcc d R).card : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ d ∈ Icc 1 R, (C*(R : ℝ)^(1+2*δ))*(1/(d : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (C*(R : ℝ)^(1+2*δ))*(∑ d ∈ Icc 1 R, 1/(d : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log R) (by positivity)
  have hlog : 1+Real.log R ≤ (1+1/δ)*(R : ℝ)^δ := by
    have hlog := Real.log_le_rpow_div (Nat.cast_nonneg R) hδ
    have hpow := Real.one_le_rpow hR1 hδ.le
    calc
      _ ≤ (R : ℝ)^δ + (R : ℝ)^δ/δ := add_le_add hpow hlog
      _ = _ := by ring
  calc
    _ ≤ C*(R : ℝ)^(1+2*δ)*(1+Real.log R) := habs
    _ ≤ C*(R : ℝ)^(1+2*δ)*((1+1/δ)*(R : ℝ)^δ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (C*(1+1/δ))*(R : ℝ)^(1+ε) := by
      calc
        _ = (C*(1+1/δ))*((R : ℝ)^(1+2*δ)*(R : ℝ)^δ) := by ring
        _ = _ := by rw [← Real.rpow_add hR0, show 1+2*δ+δ=1+ε by dsimp [δ]; ring]

private theorem supported_one_card {R : ℕ} (hR : 0<R) :
    (primeSupportedIcc 1 R).card = 1 := by
  have hs : primeSupportedIcc 1 R = {1} := by
    ext n
    simp only [primeSupportedIcc, mem_filter, mem_Icc, mem_singleton]
    constructor
    · rintro ⟨_,hs⟩
      by_contra hn
      obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hn
      exact hp.not_dvd_one (hs p hp hpn)
    · rintro rfl
      exact ⟨⟨by omega, hR⟩, primeSupportedOn_one 1⟩
  simp [hs]

/-- Both divisor columns after removing the unit divisor. -/
def unitCutoffDoubleTail (R : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 R).erase 1, ((μ d : ℤ) : ℝ) * (R/d : ℕ) *
    ∑ e ∈ (Icc 1 R).erase 1,
      (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0) * (R/e : ℕ)

/-- The uncompensated double tail contains a quadratic term even at cutoff one. -/
theorem unitCutoffDoubleTail_exact {R : ℕ} (hR : 0<R) :
    unitCutoffDoubleTail R = (R : ℝ)^2-2*R+floorCorrelation (Icc 1 R) R := by
  let S := Icc 1 R
  let f : ℕ → ℝ := fun d => ((μ d : ℤ) : ℝ)*(R/d : ℕ)
  let row : ℕ → ℝ := fun d =>
    ∑ e ∈ S, (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0)*(R/e : ℕ)
  have h1 : 1∈S := mem_Icc.mpr ⟨le_refl 1,hR⟩
  have hf1 : f 1 = R := by simp [f]
  have hrow1 : row 1 = 1 := by
    simpa only [row, S, supported_one_card hR, Nat.cast_one] using complete_floor_column 1 R
  have hsumf : (∑ d ∈ S, f d) = 1 := by
    simpa [row, f] using hrow1
  have hrowerase (d : ℕ) :
      (∑ e ∈ S.erase 1, (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0)*(R/e : ℕ)) =
        row d - R := by
    have h := Finset.sum_erase_add S
      (fun e => (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0)*(R/e : ℕ)) h1
    change _ = row d at h
    rw [if_pos (Nat.coprime_one_right d), moebius_apply_one, Int.cast_one,
      Nat.div_one, one_mul] at h
    linarith
  have hfirst : (∑ d ∈ S.erase 1, f d*row d) =
      floorCorrelation S R-R := by
    have h := Finset.sum_erase_add S (fun d => f d*row d) h1
    have hfull : (∑ d ∈ S, f d*row d) = floorCorrelation S R := by
      simp only [floorCorrelation, S, inter_self, f, row]
    rw [hfull, hf1, hrow1, mul_one] at h
    linarith
  have hsecond : (∑ d ∈ S.erase 1, f d) = 1-R := by
    have h := Finset.sum_erase_add S f h1
    rw [hsumf, hf1] at h
    linarith
  calc
    _ = ∑ d ∈ S.erase 1, f d*(row d-R) := by
      unfold unitCutoffDoubleTail
      exact Finset.sum_congr rfl fun d _ => congrArg (fun x => f d*x) (hrowerase d)
    _ = (∑ d ∈ S.erase 1, f d*row d)-(∑ d ∈ S.erase 1, f d)*R := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by rw [hfirst, hsecond]; dsimp [S]; ring

/-- Removing the exact quadratic term leaves an unconditionally near-linear remainder. -/
theorem exists_unitCutoffDoubleTail_remainder_le {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℕ, 0<R →
      |unitCutoffDoubleTail R-(R : ℝ)^2+2*R| ≤ C*(R : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_floorCorrelation_le hε
  refine ⟨C,hC,?_⟩
  intro R hR
  rw [unitCutoffDoubleTail_exact hR]
  convert hbound (Icc 1 R) R using 1
  congr 1
  ring

end RHTower.DeletionCoprimeColumn
