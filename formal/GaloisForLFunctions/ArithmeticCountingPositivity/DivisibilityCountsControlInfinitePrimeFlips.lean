import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMatchingCoefficientIsTheLogarithmicDensity

/-!
# Divisibility counts control infinite prime flips

A prime-pattern gauge agrees with its finite prime cutoff throughout each
integer horizon. Counting multiples bounds its harmonic defect and the
squared error of any fixed cutoff, uniformly in the horizon. Geometrically
sparse infinite prime sets consequently retain gaps arbitrarily close to
the maximal selective margin.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

open private harmonicMass_shell from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity

/-- The completely multiplicative sign flipping precisely the primes in P. -/
def primeSetFlip (P : Set ℕ) : ℕ → ℝ := by
  classical
  exact primeSignGauge (fun p => if p ∈ P then -1 else 1)

/-- The flipped primes visible at a finite integer horizon. -/
def primeSetCutoff (P : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE N).filter (fun p => p ∈ P)

/-- The reciprocal mass of the flipped primes visible at a horizon. -/
def primeSetReciprocalSum (P : Set ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ primeSetCutoff P N, 1 / (p : ℝ)

private theorem primeSetFlip_sign (P : Set ℕ) : IsSignGauge (primeSetFlip P) := by
  classical
  apply primeSignGauge_isSignGauge
  intro p
  split_ifs <;> norm_num

private theorem primeSetFlip_mul_self (P : Set ℕ) (n : ℕ) :
    primeSetFlip P n * primeSetFlip P n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [primeSetFlip, primeSignGauge, Nat.factorization_zero, Finsupp.prod_zero_index,
      one_mul]
  · exact (primeSetFlip_sign P).mul_self hn

private theorem primeSetCutoff_prime (P : Set ℕ) (N : ℕ) :
    ∀ p ∈ primeSetCutoff P N, p.Prime := by
  classical
  intro p hp
  exact Nat.prime_of_mem_primesLE (mem_filter.mp hp).1

/-- Every prime-pattern gauge agrees exactly with its finite cutoff on the
whole integer horizon, including the zero coordinate. -/
theorem primeSetFlip_eq_finiteFlip_of_le (P : Set ℕ) {n N : ℕ} (hn : n ≤ N) :
    primeSetFlip P n = finiteFlip (primeSetCutoff P N) n := by
  classical
  have hsub : n.primeFactors ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hprime, hpn, hn0⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans hn, hprime⟩
  simp only [primeSetFlip, primeSignGauge, Nat.prod_factorization_eq_prod_primeFactors,
    finiteFlip, primeSetCutoff, prod_filter]
  calc
    _ = ∏ p ∈ n.primeFactors, (if p ∈ P then (-1 : ℝ) ^ n.factorization p else 1) := by
      apply prod_congr rfl
      intro p _
      by_cases hp : p ∈ P <;> simp only [hp, if_true, if_false, one_pow]
    _ = _ := by
      apply prod_subset hsub
      intro p _ hp
      have hz : n.factorization p = 0 := by
        by_contra hne
        apply hp
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        exact hne
      rw [hz, pow_zero]
      split_ifs <;> rfl

private theorem finiteFlip_defect_le_divisor_count (F : Finset ℕ) (n : ℕ) :
    1 - finiteFlip F n ≤ 2 * ∑ p ∈ F, (if p ∣ n then (1 : ℝ) else 0) := by
  have hsign : 1 - finiteFlip F n ≤ 2 := by
    have h := (abs_le.mp (abs_finiteFlip_sub_one_le F n)).1
    linarith only [h]
  by_cases h : ∃ p ∈ F, p ∣ n
  · obtain ⟨p, hp, hpn⟩ := h
    have hcount : (1 : ℝ) ≤ ∑ q ∈ F, (if q ∣ n then (1 : ℝ) else 0) := by
      have h := single_le_sum (f := fun q => if q ∣ n then (1 : ℝ) else 0)
        (fun q _ => by split_ifs <;> norm_num) hp
      simpa only [if_pos hpn] using h
    linarith only [hsign, hcount]
  · have he : finiteFlip F n = 1 :=
      finiteFlip_eq_one_of_coprime (fun p hp hpn => h ⟨p, hp, hpn⟩)
    rw [he, sub_self]
    positivity

private theorem finiteFlip_harmonic_defect_le (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) (N : ℕ) :
    gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (finiteFlip F) N ≤
      2 * gaugeHarmonicSum (fun _ => 1) N * ∑ p ∈ F, 1 / (p : ℝ) := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (1 : ℝ) / n - finiteFlip F n / n ≤
        ∑ p ∈ F, (if p ∣ n then 2 / (n : ℝ) else 0) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h := div_le_div_of_nonneg_right (finiteFlip_defect_le_divisor_count F n) hn0
    rw [sub_div, mul_sum, sum_div] at h
    calc
      _ ≤ ∑ p ∈ F, (2 * (if p ∣ n then (1 : ℝ) else 0)) / n := h
      _ = _ := by
        apply sum_congr rfl
        intro p _
        by_cases hp : p ∣ n <;> simp only [hp, if_true, if_false, mul_one, mul_zero, zero_div]
  have hmass (p : ℕ) (hp : p ∈ F) :
      (∑ n ∈ Icc 1 N, (if p ∣ n then 2 / (n : ℝ) else 0)) ≤
        2 * gaugeHarmonicSum (fun _ => 1) N / p := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hF p hp).pos
    have he : (∑ n ∈ Icc 1 N, (if p ∣ n then 2 / (n : ℝ) else 0)) =
        2 * (∑ n ∈ (Icc 1 N).filter (p ∣ ·), (1 : ℝ) / n) := by
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro n _
      by_cases hn : p ∣ n <;> simp only [hn, if_true, if_false, mul_zero, mul_one_div]
    rw [he, harmonicMass_multiples (hF p hp).pos]
    have hh : gaugeHarmonicSum (fun _ => 1) (N / p) ≤ gaugeHarmonicSum (fun _ => 1) N := by
      have h := (harmonicMass_shell (hF p hp).pos N).1
      linarith only [h]
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh hp0.le)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc] using h
  calc
    _ = ∑ n ∈ Icc 1 N, ((1 : ℝ) / n - finiteFlip F n / n) := by
      rw [gaugeHarmonicSum, gaugeHarmonicSum, sum_sub_distrib]
    _ ≤ ∑ n ∈ Icc 1 N, ∑ p ∈ F, (if p ∣ n then 2 / (n : ℝ) else 0) :=
      sum_le_sum hterm
    _ = ∑ p ∈ F, ∑ n ∈ Icc 1 N, (if p ∣ n then 2 / (n : ℝ) else 0) := sum_comm
    _ ≤ ∑ p ∈ F, 2 * gaugeHarmonicSum (fun _ => 1) N / p := sum_le_sum hmass
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring

private theorem primeSetFlip_harmonic_defect_le (P : Set ℕ) (N : ℕ) :
    gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (primeSetFlip P) N ≤
      2 * gaugeHarmonicSum (fun _ => 1) N * primeSetReciprocalSum P N := by
  have he : gaugeHarmonicSum (primeSetFlip P) N =
      gaugeHarmonicSum (finiteFlip (primeSetCutoff P N)) N := by
    apply sum_congr rfl
    intro n hn
    rw [primeSetFlip_eq_finiteFlip_of_le P (mem_Icc.mp hn).2]
  rw [he]
  exact finiteFlip_harmonic_defect_le _ (primeSetCutoff_prime P N) N

/-- Reciprocal divisibility counts give a harmonic correlation floor for
every prime set, uniformly in the integer horizon. -/
theorem primeSetFlip_harmonicCorrelation_ge (P : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    1 - 2 * primeSetReciprocalSum P N ≤ harmonicCorrelation (primeSetFlip P) N := by
  have h := primeSetFlip_harmonic_defect_le P N
  rw [harmonicCorrelation, le_div_iff₀ (gaugeHarmonicSum_one_pos hN)]
  nlinarith only [h]

private theorem primeSetFlip_partition (P : Set ℕ) (Q n : ℕ) :
    primeSetFlip P n =
      primeSetFlip (P ∩ Set.Iic Q) n * primeSetFlip (P \ Set.Iic Q) n := by
  classical
  simp only [primeSetFlip, primeSignGauge, Finsupp.prod, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  by_cases hp : p ∈ P <;> by_cases hpQ : p ≤ Q <;>
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Iic, hp, hpQ,
      and_self, and_true, and_false, not_true_eq_false,
      not_false_eq_true, if_true, if_false, one_pow, one_mul, mul_one]

private theorem primeSetFlip_cutoff_eq (P : Set ℕ) (Q n : ℕ) :
    primeSetFlip (P ∩ Set.Iic Q) n = finiteFlip (primeSetCutoff P Q) n := by
  classical
  rw [primeSetFlip_eq_finiteFlip_of_le _ (le_max_left n Q)]
  have he : primeSetCutoff (P ∩ Set.Iic Q) (max n Q) = primeSetCutoff P Q := by
    apply Finset.ext
    intro p
    simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro ⟨⟨_, hprime⟩, hpP, hpQ⟩
      exact ⟨⟨hpQ, hprime⟩, hpP⟩
    · rintro ⟨⟨hpQ, hprime⟩, hpP⟩
      exact ⟨⟨hpQ.trans (le_max_right n Q), hprime⟩, hpP, hpQ⟩
  rw [he]

/-- A fixed finite cutoff has squared harmonic error bounded by four times
the reciprocal mass of omitted flipped primes, uniformly in the horizon. -/
theorem primeSetFlip_cutoff_distance_sq_le (P : Set ℕ) (Q : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 / n) /
        gaugeHarmonicSum (fun _ => 1) N ≤
      4 * primeSetReciprocalSum (P \ Set.Iic Q) N := by
  have he (n : ℕ) :
      (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 =
        2 * (1 - primeSetFlip (P \ Set.Iic Q) n) := by
    rw [← primeSetFlip_cutoff_eq P Q n, primeSetFlip_partition P Q n]
    have hu : primeSetFlip (P ∩ Set.Iic Q) n ^ 2 = 1 := by
      simpa only [pow_two] using primeSetFlip_mul_self (P ∩ Set.Iic Q) n
    have hv : primeSetFlip (P \ Set.Iic Q) n ^ 2 = 1 := by
      simpa only [pow_two] using primeSetFlip_mul_self (P \ Set.Iic Q) n
    calc
      _ = primeSetFlip (P ∩ Set.Iic Q) n ^ 2 *
          (primeSetFlip (P \ Set.Iic Q) n ^ 2 -
            2 * primeSetFlip (P \ Set.Iic Q) n + 1) := by ring
      _ = _ := by rw [hu, hv]; ring
  have hsum : (∑ n ∈ Icc 1 N,
      (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 / n) =
        2 * (gaugeHarmonicSum (fun _ => 1) N -
          gaugeHarmonicSum (primeSetFlip (P \ Set.Iic Q)) N) := by
    rw [gaugeHarmonicSum, gaugeHarmonicSum, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [he]
    ring
  rw [hsum, div_le_iff₀ (gaugeHarmonicSum_one_pos hN)]
  have h := mul_le_mul_of_nonneg_left (primeSetFlip_harmonic_defect_le (P \ Set.Iic Q) N)
    (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [h]

/-- There are infinite sets of primes with arbitrarily small reciprocal
mass at every finite cutoff. -/
theorem exists_infinite_primes_bounded_reciprocal_mass {η : ℝ} (hη : 0 < η) :
    ∃ P : Set ℕ, P.Infinite ∧ (∀ p ∈ P, p.Prime) ∧
      ∀ N : ℕ, primeSetReciprocalSum P N ≤ η := by
  classical
  obtain ⟨A, hA⟩ := exists_nat_gt (max (1 : ℝ) (2 / η))
  have hA1 : (1 : ℝ) < A := (le_max_left _ _).trans_lt hA
  have hA0 : (0 : ℝ) < A := zero_lt_one.trans hA1
  have hAη : 2 / (A : ℝ) < η := by
    have h := (le_max_right _ _).trans_lt hA
    rw [div_lt_iff₀ hη] at h
    rw [div_lt_iff₀ hA0]
    nlinarith only [h]
  -- Increasing primes with geometric lower bounds make their reciprocals summable.
  choose q hq hprime using (fun M : ℕ => Nat.exists_infinite_primes M)
  let f : ℕ → ℕ := Nat.rec (q A) (fun n previous => q (max (A * 2 ^ (n + 1)) (previous + 1)))
  have hfprime (n : ℕ) : (f n).Prime := by
    cases n with
    | zero => exact hprime A
    | succ n => exact hprime _
  have hfbound (n : ℕ) : A * 2 ^ n ≤ f n := by
    cases n with
    | zero =>
        change A * 2 ^ 0 ≤ q A
        simpa only [pow_zero, mul_one] using hq A
    | succ n => exact (le_max_left _ _).trans (hq _)
  have hfmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h : f n + 1 ≤ f (n + 1) := (le_max_right _ _).trans (hq _)
    omega
  have hgeo : HasSum (fun n : ℕ => (1 / (A : ℝ)) * (1 / 2 : ℝ) ^ n) (2 / (A : ℝ)) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / (A : ℝ))
    have hv : (1 / (A : ℝ)) * (1 - (1 / 2 : ℝ))⁻¹ = 2 / (A : ℝ) := by
      norm_num; ring
    rw [hv] at h
    exact h
  have hterm (n : ℕ) : 1 / (Nat.cast (f n) : ℝ) ≤ (1 / (A : ℝ)) * (1 / 2 : ℝ) ^ n := by
    have hb : (A : ℝ) * 2 ^ n ≤ (Nat.cast (f n) : ℝ) := by exact_mod_cast hfbound n
    calc
      _ ≤ 1 / ((A : ℝ) * 2 ^ n) := one_div_le_one_div_of_le
        (mul_pos hA0 (pow_pos (by norm_num) n)) hb
      _ = _ := by rw [div_pow, one_pow]; ring
  have hs : Summable (fun n : ℕ => 1 / (Nat.cast (f n) : ℝ)) :=
    hgeo.summable.of_nonneg_of_le (fun n => by positivity) hterm
  have htotal : (∑' n : ℕ, 1 / (Nat.cast (f n) : ℝ)) ≤ 2 / (A : ℝ) := by
    rw [← hgeo.tsum_eq]
    exact hs.tsum_mono hgeo.summable hterm
  -- Injectivity transfers the reciprocal series from its indices to all integers.
  let P : Set ℕ := Set.range f
  let w (p : ℕ) : ℝ :=
    @ite ℝ (p ∈ P) (Classical.propDecidable (p ∈ P)) (1 / (Nat.cast p : ℝ)) 0
  have hsum : HasSum w (∑' n : ℕ, 1 / (Nat.cast (f n) : ℝ)) := by
    apply (hfmono.injective.hasSum_iff (fun p hp => by
      dsimp only [w, P]
      rw [if_neg hp])).mp
    exact hs.hasSum.congr_fun fun n => by
      dsimp only [Function.comp_apply, w, P]
      rw [if_pos (Set.mem_range_self n)]
  refine ⟨P, Set.infinite_range_of_injective hfmono.injective, ?_, ?_⟩
  · rintro p ⟨n, rfl⟩
    exact hfprime n
  · intro N
    have hcut : primeSetReciprocalSum P N = ∑ p ∈ primeSetCutoff P N, w p := by
      apply sum_congr rfl
      intro p hp
      have hpP : p ∈ P := by
        simp only [primeSetCutoff, Finset.mem_filter] at hp
        exact hp.2
      dsimp only [w]
      rw [if_pos hpP]
    rw [hcut]
    have hle := hsum.summable.sum_le_tsum (primeSetCutoff P N)
      (fun p _ => by dsimp only [w]; split_ifs <;> positivity)
    rw [hsum.tsum_eq] at hle
    exact hle.trans (htotal.trans hAη.le)

private theorem primeSetFlip_hasGap_of_mass_bound (P : Set ℕ) {η : ℝ}
    (hη : η ≤ 1 / 2) (hmass : ∀ N, primeSetReciprocalSum P N ≤ η) :
    HasHyperplaneGap (primeSetFlip P) (2 * Real.log 2 * (1 - 2 * η) ^ 2) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_prime_gap_ge_squared_correlation hε
  refine ⟨max 1 N₀, fun N hN x hx => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hbound := hN₀ N ((le_max_right _ _).trans hN) (primeSetFlip P)
    (primeSetFlip_mul_self P) x hx
  have hfloor : 0 ≤ 1 - 2 * η := by linarith only [hη]
  have hc : 1 - 2 * η ≤ harmonicCorrelation (primeSetFlip P) N := by
    have h := primeSetFlip_harmonicCorrelation_ge P hN1
    linarith only [h, hmass N]
  have hs := pow_le_pow_left₀ hfloor hc 2
  have hg : 0 ≤ 2 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg one_le_two)
  have hM : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpaid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hg) hM
  linarith only [hbound, hpaid]

/-- Infinitely many flipped primes can retain any prescribed gap strictly
below the maximal margin. The construction pays a uniform arithmetic count,
so no interchange of prime-cutoff and integer-horizon limits is needed. -/
theorem exists_infinite_prime_flips_with_near_maximal_gap {a : ℝ}
    (ha : a < 2 * Real.log 2) :
    ∃ P : Set ℕ, P.Infinite ∧ (∀ p ∈ P, p.Prime) ∧
      IsSignGauge (primeSetFlip P) ∧
      (∀ p ∈ P, primeSetFlip P p = -1) ∧ HasHyperplaneGap (primeSetFlip P) a := by
  classical
  let g := 2 * Real.log 2
  have hg : 0 < g := mul_pos (by norm_num) (Real.log_pos one_lt_two)
  have hga : 0 < g - a := sub_pos.mpr ha
  let η : ℝ := min (1 / 4) ((g - a) / (8 * g))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hga (mul_pos (by norm_num) hg))
  have hηquarter : η ≤ 1 / 4 := min_le_left _ _
  have hηbound : 8 * g * η ≤ g - a := by
    have h := min_le_right (1 / 4 : ℝ) ((g - a) / (8 * g))
    have h' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hg)).mp h
    nlinarith only [h']
  have hgap : a < g * (1 - 2 * η) ^ 2 := by
    have hsq := mul_nonneg hg.le (sq_nonneg η)
    nlinarith only [hηbound, hga, hsq]
  obtain ⟨P, hPinf, hPprime, hmass⟩ := exists_infinite_primes_bounded_reciprocal_mass hη
  refine ⟨P, hPinf, hPprime, primeSetFlip_sign P, ?_, ?_⟩
  · intro p hp
    rw [primeSetFlip, primeSignGauge_prime (hPprime p hp), if_pos hp]
  · have h := primeSetFlip_hasGap_of_mass_bound P (by linarith only [hηquarter]) hmass
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨N₀, fun N hN x hx => (hN₀ N hN x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · linarith only [hgap]
    · exact sum_nonneg fun _ _ => sq_nonneg _

end GaloisForLFunctions.ArithmeticCountingPositivity
