import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.FiniteSieveProfilesHaveEffectiveRamanujanApproximations
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSmoothRoughMeanApproximatesBoundedDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanAdjunctionEnergiesAreDistinct

/-!
# Exponential conductor confinement from bounded prime defect

Conditioning on small-prime parts and discarding their logarithmic tail gives
a finite sieve profile. Its actual harmonic weights admit spectral truncation
without a primorial loss. Exact finite Ramanujan spans cover smaller horizons.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory BezoutValuationIncidence

/-- The finite sieve consisting of all primes below an integer threshold. -/
def primePrefixSieve (P : ℕ) : Finset Nat.Primes :=
  ((range P).filter Nat.Prime).subtype Nat.Prime

theorem mem_primePrefixSieve (P : ℕ) (p : Nat.Primes) :
    p ∈ primePrefixSieve P ↔ (p : ℕ) < P := by
  change (⟨(p : ℕ), p.property⟩ : {n : ℕ // Nat.Prime n}) ∈
    ((range P).filter Nat.Prime).subtype Nat.Prime ↔ (p : ℕ) < P
  rw [Finset.mem_subtype]
  simp only [mem_filter, mem_range, p.property, and_true]

private theorem divisors_eq_horizon_filter {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    d.divisors = (Icc 1 N).filter (fun q => q ∣ d) := by
  ext q
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hqd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hqd hd, (Nat.le_of_dvd hd hqd).trans hdN⟩, hqd⟩
  · rintro ⟨_, hqd⟩
    exact ⟨hqd, hd.ne'⟩

/-- The first `N` conductors span all real data on the first `N` positive integers. -/
theorem exists_horizon_normalizedRamanujan_expansion (N : ℕ) (F : ℕ → ℝ) :
    ∃ b : ℕ → ℝ, ∀ n ∈ Icc 1 N,
      F n = ∑ m ∈ Icc 1 N, b m * normalizedRamanujanMode m n := by
  let a : ℕ → ℝ := fun m => ∑ d ∈ Icc 1 N,
    if m ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0
  refine ⟨fun m => a m * Real.sqrt (m.totient : ℝ), fun n hn => ?_⟩
  have hn0 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hinversion : F n = ∑ d ∈ Icc 1 N,
      if d ∣ n then gcdProfileMobiusCoefficient F d else 0 := by
    rw [← sum_gcdProfileMobiusCoefficient F hn0, divisors_eq_horizon_filter hn0 hnN, sum_filter]
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      (if d ∣ n then gcdProfileMobiusCoefficient F d else 0) =
        ∑ m ∈ Icc 1 N,
          (if m ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0) *
            ramanujanLagCoefficient m n := by
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hs := sum_divisors_ramanujanLagCoefficient hn0 hd0
    calc
      _ = gcdProfileMobiusCoefficient F d / (d : ℝ) *
          (∑ m ∈ d.divisors, ramanujanLagCoefficient m n) := by
        rw [hs]
        by_cases hdn : d ∣ n
        · rw [if_pos hdn, if_pos hdn, div_mul_cancel₀ _ hdR]
        · rw [if_neg hdn, if_neg hdn, mul_zero]
      _ = _ := by
        rw [divisors_eq_horizon_filter hd0 (mem_Icc.mp hd).2, sum_filter, mul_sum]
        exact sum_congr rfl fun m _ => by
          by_cases hmd : m ∣ d
          · rw [if_pos hmd, if_pos hmd]
          · rw [if_neg hmd, if_neg hmd, mul_zero, zero_mul]
  have hexp : F n = ∑ m ∈ Icc 1 N, a m * ramanujanLagCoefficient m n := by
    rw [hinversion, sum_congr rfl hterm, sum_comm]
    exact sum_congr rfl fun m _ => (sum_mul _ _ _).symm
  rw [hexp]
  refine sum_congr rfl fun m hm => ?_
  have hm0 := (mem_Icc.mp hm).1
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hs : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot).ne'
  rw [normalizedRamanujanMode_eq_coefficient hm0]
  field_simp

/-- Every finite physical vector has an exact Ramanujan pole expansion within its own horizon. -/
theorem exists_horizon_ramanujanPole_expansion (N : ℕ) (x : ℕ → ℝ) :
    ∃ b : ℕ → ℝ, ∀ n ∈ Icc 1 N,
      x n = ∑ m ∈ Icc 1 N, b m * ramanujanPoleProfile m n := by
  obtain ⟨b, hb⟩ := exists_horizon_normalizedRamanujan_expansion N (fun n => Real.sqrt n * x n)
  refine ⟨b, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have h := hb n hn
  calc
    x n = (Real.sqrt n * x n) / Real.sqrt n := by field_simp
    _ = (∑ m ∈ Icc 1 N, b m * normalizedRamanujanMode m n) / Real.sqrt n := by rw [h]
    _ = _ := by
      rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile]; ring


private theorem exists_nat_log_cutoff {x : ℝ} (hx : 0 ≤ x) :
    ∃ T : ℕ, 1 < T ∧ x ≤ Real.log T ∧ Real.log T ≤ x + 3 := by
  let z : ℝ := x + 2
  let T : ℕ := ⌈Real.exp z⌉₊
  have hz : 0 < z := by dsimp only [z]; linarith only [hx]
  have hexp : 1 < Real.exp z := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
  have hceil : Real.exp z ≤ (T : ℝ) := Nat.le_ceil _
  have hTR : (1 : ℝ) < T := hexp.trans_le hceil
  have hT : 1 < T := by exact_mod_cast hTR
  have hlower : z ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hceil
  have hceilUpper : (T : ℝ) < Real.exp z + 1 := Nat.ceil_lt_add_one (Real.exp_pos z).le
  have hdouble : (T : ℝ) ≤ 2 * Real.exp z := by linarith only [hceilUpper, hexp]
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hupper : Real.log T ≤ z + 1 := by
    have h := Real.log_le_log (zero_lt_one.trans hTR) hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero z), Real.log_exp] at h
    linarith only [h, hlogTwo]
  refine ⟨T, hT, ?_, ?_⟩
  · dsimp only [z] at hlower
    linarith only [hlower]
  · dsimp only [z] at hupper
    linarith only [hupper]

theorem sieveSupported_primePrefix_iff (P n : ℕ) :
    SieveSupported (primePrefixSieve P) n ↔ n ∈ Nat.smoothNumbers P := by
  constructor
  · intro hn
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpn
    exact (mem_primePrefixSieve P ⟨p, hp⟩).mp (hn.prime_dvd_mem hpn)
  · intro hn
    apply sieveSupported_of_primeExponentVector_support_subset
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn))
    intro p hp
    have hv : n.factorization (p : ℕ) ≠ 0 := by
      simpa only [primeExponentVector_apply] using Finsupp.mem_support_iff.mp hp
    have hpn : (p : ℕ) ∣ n := by
      by_contra h
      exact hv ((Nat.factorization_eq_zero_iff _ _).mpr (Or.inr (Or.inl h)))
    exact (mem_primePrefixSieve P p).mpr ((Nat.mem_smoothNumbers'.mp hn) p p.property hpn)

theorem smoothSet_eq_smoothNumbersUpTo (P N : ℕ) :
    smoothSet P N = Nat.smoothNumbersUpTo N P := by
  ext a
  rw [mem_smoothSet, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨ha, haN, hp⟩
    exact ⟨haN, (show 0 < a from ha).ne', fun p hpa => Nat.mem_primesBelow.mpr
      ⟨hp p hpa, Nat.prime_of_mem_primeFactors hpa⟩⟩
  · rintro ⟨haN, ha, hp⟩
    exact ⟨Nat.pos_of_ne_zero ha, haN, fun p hpa => (Nat.mem_primesBelow.mp (hp hpa)).1⟩

theorem sieveClassPrefix_primePrefix_eq (P N : ℕ) :
    sieveClassPrefix (primePrefixSieve P) N =
      (Nat.smoothNumbersUpTo N P).subtype (SieveSupported (primePrefixSieve P)) := by
  ext a
  rw [mem_sieveClassPrefix, Finset.mem_subtype, Nat.mem_smoothNumbersUpTo]
  exact (and_iff_left ((sieveSupported_primePrefix_iff P a).mp a.property)).symm

theorem sum_sieveClassPrefix_primePrefix (P N : ℕ) (F : ℕ → ℝ) :
    (∑ a ∈ sieveClassPrefix (primePrefixSieve P) N, F (a : ℕ)) =
      ∑ a ∈ Nat.smoothNumbersUpTo N P, F a := by
  rw [sieveClassPrefix_primePrefix_eq]
  exact Finset.sum_subtype_of_mem F fun a ha =>
    (sieveSupported_primePrefix_iff P a).mpr (Nat.mem_smoothNumbersUpTo.mp ha).2

theorem sieveEuler_primePrefix_sub_euler (P : ℕ) :
    sieveEuler (primePrefixSieve P) - Real.eulerMascheroniConstant = ladderConstant P := by
  rw [sieveEuler, add_sub_cancel_left]
  unfold primePrefixSieve ladderConstant
  exact Finset.sum_subtype_of_mem (fun p : ℕ => Real.log p / ((p : ℝ) - 1))
    fun p hp => (mem_filter.mp hp).2

theorem ladderConstant_le_log {P : ℕ} (hP : 1 ≤ P) :
    ladderConstant P ≤ 2 * (Real.log P + (Real.log 4 + 4)) := by
  have hterm (p : ℕ) (hp : p ∈ (range P).filter Nat.Prime) :
      Real.log p / ((p : ℝ) - 1) ≤ 2 * (ArithmeticFunction.vonMangoldt p / (p : ℝ)) := by
    have hprime := (mem_filter.mp hp).2
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hpR]
    have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hpR]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime, ← mul_div_assoc,
      div_le_div_iff₀ hp1 hp0]
    nlinarith only [mul_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hpR)]
  have hsubset : (range P).filter Nat.Prime ⊆ Icc 1 P := by
    intro p hp
    exact mem_Icc.mpr ⟨(mem_filter.mp hp).2.pos, (mem_range.mp (mem_filter.mp hp).1).le⟩
  have hmert : mertensSum P ≤ Real.log P + (Real.log 4 + 4) := by
    simpa only [Nat.div_one, Nat.cast_one, Real.log_one, add_zero] using
      row_le (m := 1) (N := P) (by norm_num) hP
  calc
    _ ≤ ∑ p ∈ (range P).filter Nat.Prime,
        2 * (ArithmeticFunction.vonMangoldt p / (p : ℝ)) := sum_le_sum hterm
    _ = 2 * ∑ p ∈ (range P).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt p / (p : ℝ) := (mul_sum _ _ _).symm
    _ ≤ 2 * mertensSum P := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsubset fun p _ _ =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg p)) zero_le_two
    _ ≤ _ := mul_le_mul_of_nonneg_left hmert zero_le_two

/-- The logarithmic smooth-part moment is controlled collectively by prime defect. -/
theorem sum_log_smoothPart_mul_sq_le (P N : ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, Real.log (RHTower.Sieve.smoothPart (P - 1) n) * x n ^ 2) ≤
      2 * poleDefect N x + 2 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have h := sum_log_mul_fibre_le P N (poleGauge x) 0
  rw [smoothSet_eq_smoothNumbersUpTo] at h
  have hmass : (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge x n - 0) ^ 2) =
      ∑ n ∈ Icc 1 N, x n ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1).ne'
    rw [sub_zero, poleGauge, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  have hleft : (∑ a ∈ Nat.smoothNumbersUpTo N P, 1 / (a : ℝ) * Real.log a *
      ∑ b ∈ roughInterval P (N / a), 1 / (b : ℝ) * (poleGauge x (a * b) - 0) ^ 2) =
        ∑ n ∈ Icc 1 N, Real.log (RHTower.Sieve.smoothPart (P - 1) n) * x n ^ 2 := by
    rw [sum_Icc_eq_smoothRough_fibres P N]
    refine sum_congr rfl fun a ha => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b hb => ?_
    have ha0 : (a : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp ha).2
    have hb0 : (b : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < b from (mem_roughInterval.mp hb).1).ne'
    rw [smoothPart_mul_of_mem_rough_fibre ha hb, sub_zero, poleGauge,
      mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
    field_simp
  rw [hmass, hleft] at h
  have hsmall : walkEnergy N (fun t => t.minFac < P) (poleGauge x) ≤ poleDefect N x := by
    have heq := walkEnergy_small_add_large P N x
    have hn := walkEnergy_nonneg N (fun t => P ≤ t.minFac) (poleGauge x)
    linarith only [heq, hn]
  linarith only [h, hsmall]

theorem sum_outside_smoothPart_le (P N : ℕ) {A : ℕ} (hA : 1 < A) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) ≤
      (2 * poleDefect N x + 2 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2) / Real.log A := by
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  apply (le_div_iff₀ (Real.log_pos hAR)).mpr
  rw [sum_mul]
  refine (sum_le_sum fun n _ => ?_).trans (sum_log_smoothPart_mul_sq_le P N x)
  by_cases hn : A < RHTower.Sieve.smoothPart (P - 1) n
  · rw [if_pos hn, mul_comm (x n ^ 2)]
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (zero_lt_one.trans hAR) (by exact_mod_cast hn.le)) (sq_nonneg _)
  · rw [if_neg hn, zero_mul]
    exact mul_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)


theorem coprime_primePrefix_iff (P k : ℕ) :
    k.Coprime (sievePrimorial (primePrefixSieve P)) ↔
      ∀ p ∈ Nat.primesBelow P, ¬p ∣ k := by
  rw [sievePrimorial, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    have hpp := Nat.mem_primesBelow.mp hp
    exact (hpp.2.coprime_iff_not_dvd.mp
      (h ⟨p, hpp.2⟩ ((mem_primePrefixSieve P _).mpr hpp.1)).symm)
  · intro h p hp
    exact (p.property.coprime_iff_not_dvd.mpr
      (h p (Nat.mem_primesBelow.mpr ⟨(mem_primePrefixSieve P p).mp hp, p.property⟩))).symm

theorem sieveUnits_primePrefix_eq (P N : ℕ) :
    sieveUnits (primePrefixSieve P) N = roughInterval P N := by
  rw [roughInterval_eq_prefix_filter]
  ext k
  simp only [sieveUnits, mem_filter, coprime_primePrefix_iff]

theorem sievedHarmonic_primePrefix_eq (P N : ℕ) :
    sievedHarmonic (primePrefixSieve P) N = roughHarmonic P N := by
  change (∑ k ∈ sieveUnits (primePrefixSieve P) N, (1 : ℝ) / k) =
    ∑ k ∈ roughInterval P N, (1 : ℝ) / k
  rw [sieveUnits_primePrefix_eq]

private theorem normalizedRamanujan_coprime_dilate {m b : ℕ} (hm : 0 < m)
    (hbm : b.Coprime m) (a : ℕ) :
    normalizedRamanujanMode m (b * a) = normalizedRamanujanMode m a := by
  rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm]
  congr 1
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hdb : d.Coprime b := (hbm.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)).symm
  simp only [hdb.dvd_mul_left]

/-- Harmonic conditioning contracts the actual squared mass. -/
theorem sum_smoothRoughMean_classMass_le (P N : ℕ) (x : ℕ → ℝ) :
    (∑ a ∈ sieveClassPrefix (primePrefixSieve P) N,
      sieveClassMass (primePrefixSieve P) a N * smoothRoughMean P N x a ^ 2) ≤
        ∑ n ∈ Icc 1 N, x n ^ 2 := by
  rw [sum_sieveClassPrefix_primePrefix P N
    (fun a => sieveClassMass (primePrefixSieve P) a N * smoothRoughMean P N x a ^ 2),
    sum_Icc_eq_smoothRough_fibres P N]
  refine sum_le_sum fun a ha => ?_
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp ha).2
  have hj := sum_mul_sq_wMean_sub_le
    (s := roughInterval P (N / a)) (w := fun k => 1 / (k : ℝ))
    (v := fun k => poleGauge x (a * k)) (fun k _ => by positivity) (0 : ℝ)
  simp only [sub_zero] at hj
  have hj' := mul_le_mul_of_nonneg_left hj (show 0 ≤ 1 / (a : ℝ) by positivity)
  have hleft : 1 / (a : ℝ) *
      ((∑ k ∈ roughInterval P (N / a), (1 : ℝ) / k) *
        wMean (roughInterval P (N / a)) (fun k => 1 / (k : ℝ))
          (fun k => poleGauge x (a * k)) ^ 2) =
        sieveClassMass (primePrefixSieve P) a N * smoothRoughMean P N x a ^ 2 := by
    rw [sieveClassMass, sievedHarmonic_primePrefix_eq]
    unfold roughHarmonic smoothRoughMean
    ring
  rw [hleft, mul_sum] at hj'
  refine hj'.trans_eq ?_
  exact sum_congr rfl fun b hb => by
    have hb0 : (b : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < b from (mem_roughInterval.mp hb).1).ne'
    rw [poleGauge, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
    field_simp

theorem sum_smoothRoughMean_prefix_classMass_le (P N : ℕ) {A : ℕ} (hA : A ≤ N)
    (x : ℕ → ℝ) :
    (∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
      sieveClassMass (primePrefixSieve P) a N * smoothRoughMean P N x a ^ 2) ≤
        ∑ n ∈ Icc 1 N, x n ^ 2 := by
  refine (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (sum_smoothRoughMean_classMass_le P N x)
  · intro a ha
    exact (mem_sieveClassPrefix _ N a).mpr (((mem_sieveClassPrefix _ A a).mp ha).trans hA)
  · intro a _ _
    exact mul_nonneg
      (div_nonneg (sievedHarmonic_nonneg _ _) (Nat.cast_nonneg (a : ℕ))) (sq_nonneg _)

/-- Supported conductors are constant along each coprime fibre, so the physical error is exactly the class-weight error. -/
theorem smoothProfile_ramanujan_error_eq_classMass (P A R N : ℕ) (f : ℕ → ℝ)
    (b : SieveClass (primePrefixSieve P) → ℝ) :
    (∑ n ∈ Icc 1 N,
      (((if RHTower.Sieve.smoothPart (P - 1) n ≤ A then
          f (RHTower.Sieve.smoothPart (P - 1) n) else 0) / Real.sqrt n) -
        ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) =
      ∑ a ∈ sieveClassPrefix (primePrefixSieve P) N, sieveClassMass (primePrefixSieve P) a N *
        ((if (a : ℕ) ≤ A then f a else 0) -
          ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * normalizedRamanujanMode m a) ^ 2 := by
  rw [sum_Icc_eq_smoothRough_fibres P N,
    sum_sieveClassPrefix_primePrefix P N (fun a => sieveClassMass (primePrefixSieve P) a N *
      ((if a ≤ A then f a else 0) -
        ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * normalizedRamanujanMode m a) ^ 2)]
  refine sum_congr rfl fun a ha => ?_
  rw [sieveClassMass, sievedHarmonic_primePrefix_eq]
  unfold roughHarmonic
  rw [div_mul_eq_mul_div, sum_mul, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkcop : k.Coprime (sievePrimorial (primePrefixSieve P)) := by
    have hunit : k ∈ sieveUnits (primePrefixSieve P) (N / a) :=
      (sieveUnits_primePrefix_eq P (N / a)).symm ▸ hk
    exact (mem_filter.mp hunit).2
  have hmodes (m : SieveClass (primePrefixSieve P)) :
      normalizedRamanujanMode m (a * k) = normalizedRamanujanMode m a := by
    rw [Nat.mul_comm a k]
    exact normalizedRamanujan_coprime_dilate m.property.pos (m.property.coprime hkcop).symm a
  have hpacket :
      (∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m (a * k)) =
        (∑ m ∈ sieveClassPrefix (primePrefixSieve P) R,
          b m * normalizedRamanujanMode m a) / Real.sqrt (a * k : ℕ) := by
    rw [sum_div]
    exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile, hmodes]; ring
  rw [smoothPart_mul_of_mem_rough_fibre ha hk, hpacket, ← sub_div, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


private theorem exists_logarithmic_confinement_cutoffs {C₀ η : ℝ}
    (hC₀ : 0 < C₀) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 ≤ K →
      ∃ P A R : ℕ, 1 < P ∧ 1 < A ∧ 1 < R ∧ A ^ 2 ≤ R ∧
        2 * ladderConstant P + 4 ≤ Real.log R ∧
        C₀ / Real.log P * K ≤ η ∧
        (2 * K + 2 * ladderConstant P) / Real.log A ≤ η ∧
        16 * (Real.log A + ladderConstant P) / Real.log R ≤ η ∧
        (R : ℝ) ≤ Real.exp (C * (K + 1)) := by
  let J : ℝ := Real.log 4 + 4
  let C₁ : ℝ := C₀ / η + 3
  let C₂ : ℝ := 2 * C₁ + 2 * J
  let C₃ : ℝ := 2 * (1 + C₂) / η + 3
  let C : ℝ := 2 * C₃ + 2 * C₂ + 7 + 16 * (C₃ + C₂) / η
  have hJ : 0 < J := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [J]
    linarith only [h]
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp only [C₂]; positivity
  have hC₃ : 0 < C₃ := by dsimp only [C₃]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun K hK => ?_⟩
  have hK1 : 0 < K + 1 := by linarith only [hK]
  obtain ⟨P, hP, hPlow, hPup⟩ := exists_nat_log_cutoff
    (div_nonneg (mul_nonneg hC₀.le hK1.le) hη.le)
  have hPR : (1 : ℝ) < P := by exact_mod_cast hP
  have hlogP : 0 < Real.log P := Real.log_pos hPR
  have hPbound : Real.log P ≤ C₁ * (K + 1) := by
    calc
      _ ≤ C₀ * (K + 1) / η + 3 := hPup
      _ = (C₀ / η) * (K + 1) + 3 := by ring
      _ ≤ _ := by dsimp only [C₁]; nlinarith only [hK]
  have hL0 := ladderConstant_nonneg P
  have hLbound : ladderConstant P ≤ C₂ * (K + 1) := by
    have hL := ladderConstant_le_log (show 1 ≤ P by omega)
    change ladderConstant P ≤ 2 * (Real.log P + J) at hL
    dsimp only [C₂]
    nlinarith only [hL, hPbound, mul_nonneg hJ.le hK]
  obtain ⟨A, hA, hAlow, hAup⟩ := exists_nat_log_cutoff
    (div_nonneg (mul_nonneg zero_le_two (add_nonneg hK hL0)) hη.le)
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log A := Real.log_pos hAR
  have hAbound : Real.log A ≤ C₃ * (K + 1) := by
    have hKL : K + ladderConstant P ≤ (1 + C₂) * (K + 1) := by
      nlinarith only [hLbound]
    calc
      _ ≤ 2 * (K + ladderConstant P) / η + 3 := hAup
      _ ≤ 2 * ((1 + C₂) * (K + 1)) / η + 3 :=
        add_le_add (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKL zero_le_two) hη.le) le_rfl
      _ = (2 * (1 + C₂) / η) * (K + 1) + 3 := by ring
      _ ≤ _ := by dsimp only [C₃]; nlinarith only [hK]
  let z : ℝ := 2 * Real.log A + 2 * ladderConstant P + 4 +
    16 * (Real.log A + ladderConstant P) / η
  have hfrac : 0 ≤ 16 * (Real.log A + ladderConstant P) / η := by positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  obtain ⟨R, hR, hRlow, hRup⟩ := exists_nat_log_cutoff hz
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRR
  have hARsq : A ^ 2 ≤ R := by
    have hlogs : Real.log ((A : ℝ) ^ 2) ≤ Real.log R := by
      rw [pow_two, Real.log_mul (zero_lt_one.trans hAR).ne' (zero_lt_one.trans hAR).ne']
      dsimp only [z] at hRlow
      linarith only [hRlow, hL0, hfrac]
    have he := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_log (sq_pos_of_pos (zero_lt_one.trans hAR)),
      Real.exp_log (zero_lt_one.trans hRR)] at he
    exact_mod_cast he
  have hEuler : 2 * ladderConstant P + 4 ≤ Real.log R := by
    dsimp only [z] at hRlow
    linarith only [hRlow, hlogA, hfrac]
  have hmean : C₀ / Real.log P * K ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogP]
    have hp := (div_le_iff₀ hη).mp hPlow
    nlinarith only [hp, hC₀]
  have htail : (2 * K + 2 * ladderConstant P) / Real.log A ≤ η := by
    apply (div_le_iff₀ hlogA).mpr
    have ha := (div_le_iff₀ hη).mp hAlow
    nlinarith only [ha]
  have hmode : 16 * (Real.log A + ladderConstant P) / Real.log R ≤ η := by
    apply (div_le_iff₀ hlogR).mpr
    have hf : 16 * (Real.log A + ladderConstant P) / η ≤ Real.log R := by
      dsimp only [z] at hRlow
      linarith only [hRlow, hlogA, hL0]
    have h := (div_le_iff₀ hη).mp hf
    nlinarith only [h]
  have hRbound : Real.log R ≤ C * (K + 1) := by
    have hsum : Real.log A + ladderConstant P ≤ (C₃ + C₂) * (K + 1) := by
      nlinarith only [hAbound, hLbound]
    have hlinear : 2 * Real.log A + 2 * ladderConstant P + 7 ≤
        (2 * C₃ + 2 * C₂ + 7) * (K + 1) := by
      nlinarith only [hsum, hK]
    have hdiv : 16 * (Real.log A + ladderConstant P) / η ≤
        (16 * (C₃ + C₂) / η) * (K + 1) := by
      calc
        _ ≤ 16 * ((C₃ + C₂) * (K + 1)) / η :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hη.le
        _ = _ := by ring
    dsimp only [z] at hRup
    dsimp only [C]
    nlinarith only [hRup, hlinear, hdiv]
  have hRexp : (R : ℝ) ≤ Real.exp (C * (K + 1)) := by
    have h := Real.exp_le_exp.mpr hRbound
    rwa [Real.exp_log (zero_lt_one.trans hRR)] at h
  exact ⟨P, A, R, hP, hA, hR, hARsq, hEuler, hmean, htail, hmode, hRexp⟩


private def extendSieveCoefficient (Q : Finset Nat.Primes)
    (b : SieveClass Q → ℝ) (m : ℕ) : ℝ :=
  if hm : SieveSupported Q m then b ⟨m, hm⟩ else 0

private theorem extendSieveCoefficient_at (Q : Finset Nat.Primes)
    (b : SieveClass Q → ℝ) (m : SieveClass Q) :
    extendSieveCoefficient Q b (m : ℕ) = b m := by
  rw [extendSieveCoefficient, dif_pos m.property]

private theorem sum_extendSieveCoefficient_ramanujanPole (Q : Finset Nat.Primes)
    (R : ℕ) (b : SieveClass Q → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 R, extendSieveCoefficient Q b m * ramanujanPoleProfile m n) =
      ∑ m ∈ sieveClassPrefix Q R, b m * ramanujanPoleProfile m n := by
  let S := (sieveClassPrefix Q R).image (fun m : SieveClass Q => (m : ℕ))
  have hS : S ⊆ Icc 1 R := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨a.property.pos, (mem_sieveClassPrefix Q R a).mp ha⟩
  have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmS : m ∉ S) :
      extendSieveCoefficient Q b m * ramanujanPoleProfile m n = 0 := by
    have hnot : ¬SieveSupported Q m := by
      intro hsup
      exact hmS (mem_image.mpr ⟨⟨m, hsup⟩,
        (mem_sieveClassPrefix Q R ⟨m, hsup⟩).mpr (mem_Icc.mp hm).2, rfl⟩)
    rw [extendSieveCoefficient, dif_neg hnot, zero_mul]
  calc
    _ = ∑ m ∈ S, extendSieveCoefficient Q b m * ramanujanPoleProfile m n :=
      (sum_subset hS hzero).symm
    _ = ∑ m ∈ sieveClassPrefix Q R,
        extendSieveCoefficient Q b (m : ℕ) * ramanujanPoleProfile m n := by
      dsimp only [S]
      exact sum_image (fun a _ b _ h => Subtype.ext h)
    _ = _ := sum_congr rfl fun m _ => by rw [extendSieveCoefficient_at]

private theorem sum_horizon_truncated_coefficients {N R : ℕ} (hNR : N ≤ R)
    (b : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) =
      ∑ m ∈ Icc 1 N, b m * ramanujanPoleProfile m n := by
  have hsub : Icc 1 N ⊆ Icc 1 R := fun m hm =>
    mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hNR⟩
  calc
    _ = ∑ m ∈ Icc 1 N, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n := by
      symm
      apply sum_subset hsub
      intro m hm hmN
      have hn : ¬m ≤ N := fun h => hmN (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
      rw [if_neg hn, zero_mul]
    _ = _ := sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]

/-- Bounded prime defect admits an exponential conductor cutoff uniformly over every horizon. -/
theorem exists_exponential_conductor_cutoff_of_poleDefect_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 ≤ K →
      ∃ R : ℕ, (R : ℝ) ≤ Real.exp (C * (K + 1)) ∧
        ∀ N : ℕ, ∀ x : ℕ → ℝ,
          (∑ n ∈ Icc 1 N, x n ^ 2) ≤ 1 → poleDefect N x ≤ K →
          ∃ b : ℕ → ℝ,
            (∑ n ∈ Icc 1 N,
              (x n - ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨C₀, hC₀, hconditioning⟩ := exists_smoothRoughPoleProjection_error_le
  let δ : ℝ := η / 8
  have hδ : 0 < δ := div_pos hη (by norm_num)
  obtain ⟨C, hC, hcutoffs⟩ := exists_logarithmic_confinement_cutoffs hC₀ hδ
  refine ⟨C, hC, fun K hK => ?_⟩
  obtain ⟨P, A, R, hP, hA, hR, hAR, hEuler, hmeanBound, htailBound, hmodeBound, hRexp⟩ :=
    hcutoffs K hK
  refine ⟨R, hRexp, fun N x hmass hdef => ?_⟩
  by_cases hRN : R ≤ N
  · have hPR : (1 : ℝ) < P := by exact_mod_cast hP
    have hAR' : (1 : ℝ) < A := by exact_mod_cast hA
    have hRR : (1 : ℝ) < R := by exact_mod_cast hR
    have hlogP : 0 < Real.log P := Real.log_pos hPR
    have hlogA : 0 < Real.log A := Real.log_pos hAR'
    have hlogR : 0 < Real.log R := Real.log_pos hRR
    have hL0 := ladderConstant_nonneg P
    have hAN : A ≤ N := by
      have hself : A ≤ A ^ 2 := by
        calc
          A = A * 1 := (Nat.mul_one A).symm
          _ ≤ A * A := Nat.mul_le_mul_left A (show 1 ≤ A by omega)
          _ = A ^ 2 := (pow_two A).symm
      exact (hself.trans hAR).trans hRN
    have hlogN : Real.log R ≤ Real.log (N + 1 : ℕ) :=
      Real.log_le_log (zero_lt_one.trans hRR)
        (by exact_mod_cast hRN.trans (Nat.le_succ N))
    have hNsieve : 2 * (sieveEuler (primePrefixSieve P) - Real.eulerMascheroniConstant) + 4 ≤
        Real.log (N + 1 : ℕ) := by
      rw [sieveEuler_primePrefix_sub_euler]
      exact hEuler.trans hlogN
    let f : ℕ → ℝ := smoothRoughMean P N x
    let g : ℕ → ℝ := fun n =>
      (if RHTower.Sieve.smoothPart (P - 1) n ≤ A then
        f (RHTower.Sieve.smoothPart (P - 1) n) else 0) / Real.sqrt n
    obtain ⟨b, hb⟩ := exists_sieveProfile_ramanujan_approximation (primePrefixSieve P) hR
      ((hAR.trans hRN).trans (Nat.le_succ N)) hNsieve (fun a => f a)
    rw [sieveEuler_primePrefix_sub_euler] at hb
    have hprofileMass :
        (∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
          sieveClassMass (primePrefixSieve P) a N * f a ^ 2) ≤ 1 :=
      (sum_smoothRoughMean_prefix_classMass_le P N hAN x).trans hmass
    have hcoef : 0 ≤ 16 * (Real.log A + ladderConstant P) / Real.log R := by positivity
    have hpacketError : (∑ n ∈ Icc 1 N,
        (g n - ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R,
          b m * ramanujanPoleProfile m n) ^ 2) ≤ δ := by
      dsimp only [g]
      rw [smoothProfile_ramanujan_error_eq_classMass P A R N f b]
      calc
        _ ≤ (16 * (Real.log A + ladderConstant P) / Real.log R) *
            ∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
              sieveClassMass (primePrefixSieve P) a N * f a ^ 2 := hb
        _ ≤ (16 * (Real.log A + ladderConstant P) / Real.log R) * 1 :=
          mul_le_mul_of_nonneg_left hprofileMass hcoef
        _ = 16 * (Real.log A + ladderConstant P) / Real.log R := mul_one _
        _ ≤ δ := hmodeBound
    have hmeanError :
        (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) ≤ δ := by
      exact (hconditioning P (by omega) N x).trans
        ((mul_le_mul_of_nonneg_left hdef (div_nonneg hC₀.le hlogP.le)).trans hmeanBound)
    have hsmoothTail :
        (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) ≤ δ := by
      have hpaid := mul_le_mul_of_nonneg_left hmass (mul_nonneg zero_le_two hL0)
      have hnum : 2 * poleDefect N x + 2 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
          2 * K + 2 * ladderConstant P := by nlinarith only [hdef, hpaid]
      exact (sum_outside_smoothPart_le P N hA x).trans
        ((div_le_div_of_nonneg_right hnum hlogA.le).trans htailBound)
    have hpreError : (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) ≤ 2 * δ := by
      calc
        _ ≤ ∑ n ∈ Icc 1 N, ((x n - smoothRoughPoleProjection P N x n) ^ 2 +
            if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) := by
          refine sum_le_sum fun n _ => ?_
          by_cases hn : RHTower.Sieve.smoothPart (P - 1) n ≤ A
          · simp only [g, f, if_pos hn, if_neg (not_lt.mpr hn), add_zero,
              smoothRoughPoleProjection]
            exact le_rfl
          · simp only [g, if_neg hn, if_pos (not_le.mp hn), zero_div, sub_zero]
            exact le_add_of_nonneg_left (sq_nonneg _)
        _ = (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) +
            (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) :=
          sum_add_distrib
        _ ≤ δ + δ := add_le_add hmeanError hsmoothTail
        _ = 2 * δ := by ring
    refine ⟨extendSieveCoefficient (primePrefixSieve P) b, ?_⟩
    simp_rw [sum_extendSieveCoefficient_ramanujanPole (primePrefixSieve P) R b]
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          (2 * (x n - g n) ^ 2 + 2 * (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) :=
        sum_le_sum fun n _ => by
          nlinarith only [sq_nonneg ((x n - g n) - (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n))]
      _ = 2 * (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) +
          2 * (∑ n ∈ Icc 1 N, (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) := by
        simp only [sum_add_distrib, mul_sum]
      _ ≤ 2 * (2 * δ) + 2 * δ := add_le_add
        (mul_le_mul_of_nonneg_left hpreError zero_le_two)
        (mul_le_mul_of_nonneg_left hpacketError zero_le_two)
      _ ≤ η := by dsimp only [δ]; linarith only [hη]
  · obtain ⟨b, hb⟩ := exists_horizon_ramanujanPole_expansion N x
    refine ⟨fun m => if m ≤ N then b m else 0, ?_⟩
    have hNR : N ≤ R := (lt_of_not_ge hRN).le
    have hzero : (∑ n ∈ Icc 1 N,
        (x n - ∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) ^ 2) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [sum_horizon_truncated_coefficients hNR, ← hb n hn, sub_self, zero_pow (by decide)]
    rw [hzero]
    exact hη.le


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_horizon_ramanujanPole_expansion

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sum_log_smoothPart_mul_sq_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sum_smoothRoughMean_classMass_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.smoothProfile_ramanujan_error_eq_classMass

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_exponential_conductor_cutoff_of_poleDefect_le
