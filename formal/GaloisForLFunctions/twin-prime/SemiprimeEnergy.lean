import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The semiprime contribution to an unmarked Type II energy

On a product of two distinct primes in the same block, the two
admissible factorizations have the same Möbius sign. Their coefficient
is the negative logarithm of the product. The prime number theorem
then forces an energy of order the product scale, uniformly in the cutoffs.
-/

namespace TwinPrime

open Finset ArithmeticFunction
open scoped Pointwise

noncomputable section

/-- Indicator of integers with no prime divisor at most `z`. -/
def roughIndicator (z n : ℕ) : ℝ :=
  if n = 1 ∨ z < n.minFac then 1 else 0

/-- The logarithmic divisor coefficient above a Vaughan cutoff. -/
def upperMangoldtDivisors (V n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if V < d then vonMangoldt d else 0

/-- The real, zero-frequency Type II coefficient on the block `(T,2T]`. -/
def emptyLabelCoefficient (T z V s : ℕ) : ℝ :=
  ∑ m ∈ s.divisors.filter (fun m => T < m ∧ m ≤ 2 * T ∧
      T < s / m ∧ s / m ≤ 2 * T),
    (moebius m : ℝ) * roughIndicator z m *
      upperMangoldtDivisors V (s / m) * roughIndicator z (s / m)

/-- The primes in one dyadic factor block. -/
def factorBlockPrimes (T : ℕ) : Finset ℕ :=
  (Ioc T (2 * T)).filter Nat.Prime

/-- Distinct prime factors, ordered to avoid counting a product twice. -/
def factorBlockPrimePairs (T : ℕ) : Finset (ℕ × ℕ) :=
  (factorBlockPrimes T ×ˢ factorBlockPrimes T).filter (fun pq => pq.1 < pq.2)

/-- The unsigned coefficient energy in the lower half of the product block. -/
def emptyLabelEnergy (T z V : ℕ) : ℝ :=
  ∑ s ∈ Ioc (T ^ 2) (2 * T ^ 2), emptyLabelCoefficient T z V s ^ 2

/-- Ordered prime pairs have distinct products. -/
theorem factorBlockPrimePairs_mul_injective (T : ℕ) :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) (factorBlockPrimePairs T : Set (ℕ × ℕ)) := by
  rintro ⟨p, q⟩ hpq ⟨r, s⟩ hrs heq
  change p * q = r * s at heq
  have hpq' := mem_filter.mp hpq
  have hrs' := mem_filter.mp hrs
  have hp := (mem_filter.mp (mem_product.mp hpq'.1).1).2
  have hr := (mem_filter.mp (mem_product.mp hrs'.1).1).2
  have hs := (mem_filter.mp (mem_product.mp hrs'.1).2).2
  have hdvd : p ∣ r * s := heq ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp hdvd with hpr | hps
  · have hpr' : p = r := (Nat.dvd_prime_two_le hr hp.two_le).mp hpr
    subst r
    exact Prod.ext rfl (mul_left_cancel₀ hp.ne_zero heq)
  · have hps' : p = s := (Nat.dvd_prime_two_le hs hp.two_le).mp hps
    subst s
    have hqr : q = r := mul_left_cancel₀ hp.ne_zero (heq.trans (mul_comm r p))
    have hlt₁ : p < q := hpq'.2
    have hlt₂ : r < p := hrs'.2
    omega

/-- A prime in the block survives every cutoff at most its lower endpoint. -/
theorem roughIndicator_blockPrime (T : ℕ) (z : Fin (T + 1))
    (p : ↥(factorBlockPrimes T)) : roughIndicator z p = 1 := by
  have hp := (mem_filter.mp p.property).2
  have hTp := (mem_Ioc.mp (mem_filter.mp p.property).1).1
  have hzp : (z : ℕ) < (p : ℕ) := lt_of_le_of_lt (Nat.le_of_lt_succ z.isLt) hTp
  simp only [roughIndicator, hp.minFac_eq, hzp, or_true, if_true]

/-- Above any cutoff at most `T`, a block prime contributes its logarithm. -/
theorem upperMangoldtDivisors_blockPrime (T : ℕ) (V : Fin (T + 1))
    (p : ↥(factorBlockPrimes T)) : upperMangoldtDivisors V p = Real.log p := by
  have hp := (mem_filter.mp p.property).2
  have hTp := (mem_Ioc.mp (mem_filter.mp p.property).1).1
  have hVp : (V : ℕ) < (p : ℕ) := lt_of_le_of_lt (Nat.le_of_lt_succ V.isLt) hTp
  simp only [upperMangoldtDivisors, hp.divisors, sum_insert, mem_singleton,
    hp.ne_one.symm, not_false_eq_true, sum_singleton, vonMangoldt_apply_one,
    ite_self, zero_add, hVp, if_true, vonMangoldt_apply_prime hp]

/-- The exact semiprime coefficient, uniformly in the smaller roughness and Vaughan cutoffs. -/
theorem emptyLabelCoefficient_prime_pair (T : ℕ) (z V : Fin (T + 1))
    (pq : ↥(factorBlockPrimePairs T)) :
    emptyLabelCoefficient T z V (pq.val.1 * pq.val.2) =
      -Real.log ((pq.val.1 * pq.val.2 : ℕ) : ℝ) := by
  rcases pq with ⟨⟨p, q⟩, hpq⟩
  have hmem := mem_filter.mp hpq
  have hpblock := (mem_product.mp hmem.1).1
  have hqblock := (mem_product.mp hmem.1).2
  have hp := (mem_filter.mp hpblock).2
  have hq := (mem_filter.mp hqblock).2
  have hpT := mem_Ioc.mp (mem_filter.mp hpblock).1
  have hqT := mem_Ioc.mp (mem_filter.mp hqblock).1
  have hpq' : p < q := hmem.2
  have hT : 1 ≤ T := by have := hp.two_le; omega
  have hprod : 2 * T < p * q := by
    have hmul := Nat.mul_le_mul (Nat.succ_le_of_lt hpT.1) (Nat.succ_le_of_lt hqT.1)
    nlinarith [Nat.zero_le (T * T)]
  have hdivp : p * q / p = q := Nat.mul_div_right q hp.pos
  have hdivq : p * q / q = p := Nat.mul_div_left p hq.pos
  have hdivisors : (p * q).divisors = {1, p, q, p * q} := by
    rw [Nat.divisors_mul, hp.divisors, hq.divisors]
    ext d
    simp [Finset.mem_mul, eq_comm, or_assoc, or_left_comm, or_comm]
  have hfilter : (p * q).divisors.filter (fun m => T < m ∧ m ≤ 2 * T ∧
      T < p * q / m ∧ p * q / m ≤ 2 * T) = {p, q} := by
    ext d
    rw [mem_filter, hdivisors]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨hd, hb⟩
      rcases hd with rfl | rfl | rfl | rfl
      · omega
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), hpT.1, hpT.2,
          hdivp.symm ▸ hqT.1, hdivp.symm ▸ hqT.2⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hqT.1, hqT.2,
          hdivq.symm ▸ hpT.1, hdivq.symm ▸ hpT.2⟩
  have hrp := roughIndicator_blockPrime T z ⟨p, hpblock⟩
  have hrq := roughIndicator_blockPrime T z ⟨q, hqblock⟩
  have hVp := upperMangoldtDivisors_blockPrime T V ⟨p, hpblock⟩
  have hVq := upperMangoldtDivisors_blockPrime T V ⟨q, hqblock⟩
  unfold emptyLabelCoefficient
  rw [hfilter, sum_pair hpq'.ne, hdivp, hdivq]
  rw [moebius_apply_prime hp, moebius_apply_prime hq, hrp, hrq, hVp, hVq]
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero)
    (Nat.cast_ne_zero.mpr hq.ne_zero)]
  push_cast
  ring

/-- The first prime subblock, ending at `6T/5`. -/
def lowerFactorPrimes (T : ℕ) : Finset ℕ :=
  (Ioc T ⌊(6 / 5 : ℝ) * T⌋₊).filter Nat.Prime

/-- The adjacent prime subblock, ending at `7T/5`. -/
def upperFactorPrimes (T : ℕ) : Finset ℕ :=
  (Ioc ⌊(6 / 5 : ℝ) * T⌋₊ ⌊(7 / 5 : ℝ) * T⌋₊).filter Nat.Prime

/-- Products across the two subblocks are distinct block-prime pairs in `(T²,2T²]`. -/
theorem factorSubblockPair_bounds (T : ℕ)
    (pq : ↥(lowerFactorPrimes T ×ˢ upperFactorPrimes T)) :
    pq.val ∈ factorBlockPrimePairs T ∧
      pq.val.1 * pq.val.2 ∈ Ioc (T ^ 2) (2 * T ^ 2) := by
  rcases pq with ⟨⟨p, q⟩, hpq⟩
  have hp := mem_filter.mp (mem_product.mp hpq).1
  have hq := mem_filter.mp (mem_product.mp hpq).2
  have hpI := mem_Ioc.mp hp.1
  have hqI := mem_Ioc.mp hq.1
  have hpq' : p < q := hpI.2.trans_lt hqI.1
  have hTq : T < q := hpI.1.trans hpq'
  have hfloor : ⌊(7 / 5 : ℝ) * T⌋₊ ≤ 2 * T := by
    have h := Nat.floor_mono (show (7 / 5 : ℝ) * T ≤ ((2 * T : ℕ) : ℝ) by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) T])
    simpa only [Nat.floor_natCast] using h
  have hqT : q ≤ 2 * T := hqI.2.trans hfloor
  have hpT : p ≤ 2 * T := hpq'.le.trans hqT
  have hblock : (p, q) ∈ factorBlockPrimePairs T := by
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpI.1, hpT⟩, hp.2⟩,
       mem_filter.mpr ⟨mem_Ioc.mpr ⟨hTq, hqT⟩, hq.2⟩⟩, hpq'⟩
  have hpR : (p : ℝ) ≤ (6 / 5 : ℝ) * T :=
    (Nat.cast_le.mpr hpI.2).trans (Nat.floor_le (by positivity))
  have hqR : (q : ℝ) ≤ (7 / 5 : ℝ) * T :=
    (Nat.cast_le.mpr hqI.2).trans (Nat.floor_le (by positivity))
  have hmul := mul_le_mul hpR hqR (Nat.cast_nonneg (α := ℝ) q)
    (show 0 ≤ (6 / 5 : ℝ) * T by positivity)
  have hupper : p * q ≤ 2 * T ^ 2 := by
    have hreal : ((p * q : ℕ) : ℝ) ≤ ((2 * T ^ 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith [sq_nonneg (T : ℝ)]
    exact_mod_cast hreal
  have hlower : T ^ 2 < p * q := by
    have h := Nat.mul_le_mul (Nat.succ_le_of_lt hpI.1) (Nat.succ_le_of_lt hTq)
    nlinarith
  exact ⟨hblock, mem_Ioc.mpr ⟨hlower, hupper⟩⟩

/-- The unsigned energy contains the product of the two prime logarithmic masses. -/
theorem emptyLabelEnergy_ge_prime_log_masses (T : ℕ) (z V : Fin (T + 1)) :
    4 * (∑ p ∈ lowerFactorPrimes T, Real.log p) *
        (∑ q ∈ upperFactorPrimes T, Real.log q) ≤ emptyLabelEnergy T z V := by
  classical
  let S := lowerFactorPrimes T ×ˢ upperFactorPrimes T
  let prod : ℕ × ℕ → ℕ := fun pq => pq.1 * pq.2
  have hinj : Set.InjOn prod (S : Set (ℕ × ℕ)) := by
    intro a ha b hb heq
    exact factorBlockPrimePairs_mul_injective T
      (factorSubblockPair_bounds T ⟨a, ha⟩).1
      (factorSubblockPair_bounds T ⟨b, hb⟩).1 heq
  have hsubset : S.image prod ⊆ Ioc (T ^ 2) (2 * T ^ 2) := by
    intro s hs
    obtain ⟨pq, hpq, rfl⟩ := mem_image.mp hs
    exact (factorSubblockPair_bounds T ⟨pq, hpq⟩).2
  have henergy : (∑ pq ∈ S, emptyLabelCoefficient T z V (prod pq) ^ 2) ≤
      emptyLabelEnergy T z V := by
    rw [← sum_image (f := fun s => emptyLabelCoefficient T z V s ^ 2)
      (fun a ha b hb heq => hinj ha hb heq)]
    exact sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => sq_nonneg _)
  have hexpand : (∑ p ∈ lowerFactorPrimes T, Real.log p) *
      (∑ q ∈ upperFactorPrimes T, Real.log q) =
      ∑ pq ∈ S, Real.log pq.1 * Real.log pq.2 := by
    simp only [S, sum_product, sum_mul_sum]
  rw [mul_assoc, hexpand, mul_sum]
  refine (sum_le_sum fun pq hpq => ?_).trans henergy
  have hpair := (factorSubblockPair_bounds T ⟨pq, hpq⟩).1
  have hp := (mem_filter.mp (mem_product.mp hpq).1).2
  have hq := (mem_filter.mp (mem_product.mp hpq).2).2
  change 4 * (Real.log pq.1 * Real.log pq.2) ≤
    emptyLabelCoefficient T z V (pq.1 * pq.2) ^ 2
  rw [emptyLabelCoefficient_prime_pair T z V ⟨pq, hpair⟩, neg_sq, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
  nlinarith [sq_nonneg (Real.log pq.1 - Real.log pq.2)]

open Filter Topology Asymptotics

private theorem prime_interval_log_mass (a : ℝ) (b : {b : ℝ // a ≤ b}) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b.val⌋₊).filter Nat.Prime, Real.log p) =
      Chebyshev.theta b - Chebyshev.theta a := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b.val⌋₊ := Nat.floor_mono b.property
  have hset : Ioc 0 ⌊b.val⌋₊ = Ioc 0 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b.val⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint (Ioc 0 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b.val⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have hn' := mem_Ioc.mp hn
    have hm' := mem_Ioc.mp hm
    omega
  simp only [Chebyshev.theta, sum_filter]
  rw [hset, sum_union hdisj]
  ring

private theorem theta_scaled_nat_div_tendsto (c : {c : ℝ // 0 < c}) :
    Tendsto (fun T : ℕ => Chebyshev.theta (c.val * T) / (T : ℝ))
      atTop (𝓝 c.val) := by
  have hratio : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one
      ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx => ne_of_gt hx)).mp chebyshev_asymptotic
  have hscale : Tendsto (fun T : ℕ => c.val * (T : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop c.property tendsto_natCast_atTop_atTop
  have hlim := (hratio.comp hscale).mul_const c.val
  rw [one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hc0 : c.val ≠ 0 := ne_of_gt c.property
  dsimp only [Function.comp_apply]
  field_simp

/-- The first subblock has logarithmic prime mass asymptotic to `T/5`. -/
theorem lowerFactorPrimes_log_mass_tendsto :
    Tendsto (fun T : ℕ => (∑ p ∈ lowerFactorPrimes T, Real.log p) / (T : ℝ))
      atTop (𝓝 (1 / 5 : ℝ)) := by
  have h₆ := theta_scaled_nat_div_tendsto ⟨6 / 5, by norm_num⟩
  have h₁ := theta_scaled_nat_div_tendsto ⟨1, by norm_num⟩
  have hlim := h₆.sub h₁
  norm_num only at hlim
  refine hlim.congr fun T => ?_
  have hmass := prime_interval_log_mass (T : ℝ)
    ⟨(6 / 5 : ℝ) * T, by nlinarith [Nat.cast_nonneg (α := ℝ) T]⟩
  simp only [Nat.floor_natCast] at hmass
  rw [show (∑ p ∈ lowerFactorPrimes T, Real.log p) =
      Chebyshev.theta ((6 / 5 : ℝ) * T) - Chebyshev.theta T from hmass]
  simp only [one_mul, sub_div]

/-- The adjacent subblock has the same logarithmic prime mass asymptotic. -/
theorem upperFactorPrimes_log_mass_tendsto :
    Tendsto (fun T : ℕ => (∑ p ∈ upperFactorPrimes T, Real.log p) / (T : ℝ))
      atTop (𝓝 (1 / 5 : ℝ)) := by
  have h₇ := theta_scaled_nat_div_tendsto ⟨7 / 5, by norm_num⟩
  have h₆ := theta_scaled_nat_div_tendsto ⟨6 / 5, by norm_num⟩
  have hlim := h₇.sub h₆
  norm_num only at hlim
  refine hlim.congr fun T => ?_
  have hmass := prime_interval_log_mass ((6 / 5 : ℝ) * T)
    ⟨(7 / 5 : ℝ) * T, by nlinarith [Nat.cast_nonneg (α := ℝ) T]⟩
  rw [show (∑ p ∈ upperFactorPrimes T, Real.log p) =
      Chebyshev.theta ((7 / 5 : ℝ) * T) - Chebyshev.theta ((6 / 5 : ℝ) * T) from hmass]
  simp only [sub_div]

/-- Semiprimes force a positive bulk energy, uniformly in every cutoff at most `T`. -/
theorem eventually_emptyLabelEnergy_ge :
    ∀ᶠ T : ℕ in atTop, ∀ z V : Fin (T + 1),
      (T : ℝ) ^ 2 / 25 ≤ emptyLabelEnergy T z V := by
  have hleft : ∀ᶠ T : ℕ in atTop,
      (1 / 10 : ℝ) < (∑ p ∈ lowerFactorPrimes T, Real.log p) / (T : ℝ) :=
    lowerFactorPrimes_log_mass_tendsto.eventually (Ioi_mem_nhds (by norm_num))
  have hright : ∀ᶠ T : ℕ in atTop,
      (1 / 10 : ℝ) < (∑ p ∈ upperFactorPrimes T, Real.log p) / (T : ℝ) :=
    upperFactorPrimes_log_mass_tendsto.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hleft, hright, eventually_ge_atTop (1 : ℕ)] with T hleft hright hT z V
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T from hT)
  have hL : (T : ℝ) / 10 ≤ ∑ p ∈ lowerFactorPrimes T, Real.log p := by
    have h := (lt_div_iff₀ hTpos).mp hleft
    linarith
  have hR : (T : ℝ) / 10 ≤ ∑ p ∈ upperFactorPrimes T, Real.log p := by
    have h := (lt_div_iff₀ hTpos).mp hright
    linarith
  have hmul := mul_le_mul hL hR (by positivity)
    (le_trans (show 0 ≤ (T : ℝ) / 10 by positivity) hL)
  have henergy := emptyLabelEnergy_ge_prime_log_masses T z V
  nlinarith

/-- No cutoff family below the factor scale gives an unsigned energy that is `o(T²)`. -/
theorem emptyLabelEnergy_not_isLittleO (z V : (T : ℕ) → Fin (T + 1)) :
    ¬ (fun T : ℕ => emptyLabelEnergy T (z T) (V T)) =o[atTop]
      (fun T : ℕ => (T : ℝ) ^ 2) := by
  intro h
  have hsmall : ∀ᶠ T : ℕ in atTop,
      emptyLabelEnergy T (z T) (V T) / (T : ℝ) ^ 2 < (1 / 50 : ℝ) :=
    h.tendsto_div_nhds_zero.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨T, hsmall, hlower, hT⟩ :=
    (hsmall.and (eventually_emptyLabelEnergy_ge.and (eventually_ge_atTop (1 : ℕ)))).exists
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T from hT)
  have hs := (div_lt_iff₀ (sq_pos_of_pos hTpos)).mp hsmall
  have hl := hlower (z T) (V T)
  nlinarith [sq_pos_of_pos hTpos]

end

end TwinPrime
