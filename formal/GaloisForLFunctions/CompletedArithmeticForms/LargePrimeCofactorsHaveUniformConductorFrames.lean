import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanModesAreValuationSteps

/-!
# Composite conductor frames with a large prime factor

Conductors `dp` split into disjoint large-prime spikes and a common packet
of small conductors. The rows below the first spike control that packet;
the small-conductor frame on each spike then controls every coefficient.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory CriticalScaleArithmeticRigidity

/-- A small-conductor packet before logarithmic horizon normalization. -/
def cofactorProfile (D : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 D, a d * ramanujanPoleProfile d n

/-- The background left after splitting off the large-prime divisibility spikes. -/
def cofactorBackground (S : Finset ℕ) (D : ℕ) (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  cofactorProfile D (fun d => ∑ p ∈ S, a p d / Real.sqrt (p.totient : ℝ)) n

/-- Large-prime spikes with their small-conductor profiles. -/
def cofactorSpikes (S : Finset ℕ) (D : ℕ) (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, if p ∣ n then
    ((p : ℝ) / Real.sqrt (p.totient : ℝ)) * cofactorProfile D (a p) n else 0

/-- The actual composite-conductor packet on the horizon. -/
def primeCofactorHorizonPacket (S : Finset ℕ) (D N : ℕ) (a : ℕ → ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d • normalizedRamanujanHorizonVector (d * p) N

private theorem profile_mul_prime {d p : ℕ} (hd : 0 < d) (hp : p.Prime)
    (hcp : d.Coprime p) (n : ℕ) :
    ramanujanPoleProfile (d * p) n = ramanujanPoleProfile d n *
      ((if p ∣ n then (p : ℝ) else 0) - 1) / Real.sqrt (p.totient : ℝ) := by
  rw [ramanujanPoleProfile, ramanujanPoleProfile,
    normalizedRamanujanMode_eq_coefficient (Nat.mul_pos hd hp.pos),
    normalizedRamanujanMode_eq_coefficient hd,
    BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hcp,
    Nat.totient_mul hcp, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    ramanujanCoefficient_prime hp]
  split_ifs <;> ring

private theorem cofactorProfile_mul_prime {D p : ℕ} (hp : p.Prime)
    (hcp : ∀ d ∈ Icc 1 D, d.Coprime p) (a : ℕ → ℝ) (n : ℕ) :
    cofactorProfile D a (p * n) = cofactorProfile D a n / Real.sqrt p := by
  unfold cofactorProfile
  rw [sum_div]
  refine sum_congr rfl fun d hd => ?_
  rw [ramanujanPoleProfile, ramanujanPoleProfile,
    normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hd).1,
    normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hd).1,
    Nat.mul_comm p n, ramanujanCoefficient_mul_lag_of_coprime (hcp d hd),
    Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

private theorem cofactor_profile_split (S : Finset ℕ) {D : ℕ} (a : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ S, p.Prime)
    (hcp : ∀ p ∈ S, ∀ d ∈ Icc 1 D, d.Coprime p) (n : ℕ) :
    (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d * ramanujanPoleProfile (d * p) n) =
      cofactorSpikes S D a n - cofactorBackground S D a n := by
  have hb : cofactorBackground S D a n =
      ∑ p ∈ S, cofactorProfile D (a p) n / Real.sqrt (p.totient : ℝ) := by
    unfold cofactorBackground cofactorProfile
    simp only [sum_mul, sum_div]
    rw [sum_comm]
    exact sum_congr rfl fun p _ => sum_congr rfl fun d _ => by ring
  rw [hb, cofactorSpikes, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    simp only [cofactorProfile, mul_sum, sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    rw [profile_mul_prime (mem_Icc.mp hd).1 (hP p hp) (hcp p hp d hd), if_pos hpn]
    ring
  · rw [if_neg hpn, zero_sub]
    simp only [cofactorProfile, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun d hd => ?_
    rw [profile_mul_prime (mem_Icc.mp hd).1 (hP p hp) (hcp p hp d hd), if_neg hpn]
    ring

private theorem cofactorSpikes_vanishes_before (S : Finset ℕ) (D : ℕ)
    (a : ℕ → ℕ → ℝ) {M n : ℕ} (hM : ∀ p ∈ S, M < p)
    (hn : 0 < n) (hnM : n ≤ M) : cofactorSpikes S D a n = 0 := by
  apply sum_eq_zero
  intro p hp
  exact if_neg fun hpn => (not_lt_of_ge ((Nat.le_of_dvd hn hpn).trans hnM)) (hM p hp)

private theorem cofactorSpikes_sq (S : Finset ℕ) (D : ℕ) (a : ℕ → ℕ → ℝ)
    {N n : ℕ} (hP : ∀ p ∈ S, p.Prime)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q) (hn : n ∈ Icc 1 N) :
    cofactorSpikes S D a n ^ 2 =
      ∑ p ∈ S, if p ∣ n then
        (((p : ℝ) / Real.sqrt (p.totient : ℝ)) * cofactorProfile D (a p) n) ^ 2 else 0 := by
  let z := fun p : ℕ => if p ∣ n then
    ((p : ℝ) / Real.sqrt (p.totient : ℝ)) * cofactorProfile D (a p) n else 0
  have hcross (p : ℕ) (hp : p ∈ S) (q : ℕ) (hq : q ∈ S) (hne : p ≠ q) :
      z p * z q = 0 := by
    by_cases hpn : p ∣ n
    · by_cases hqn : q ∣ n
      · have hcop := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hne
        have hpq := Nat.le_of_dvd (mem_Icc.mp hn).1
          (hcop.mul_dvd_of_dvd_of_dvd hpn hqn)
        exact ((not_lt_of_ge (hpq.trans (mem_Icc.mp hn).2)) (hdisj p hp q hq hne)).elim
      · simp only [z, if_neg hqn, mul_zero]
    · simp only [z, if_neg hpn, zero_mul]
  change (∑ p ∈ S, z p) ^ 2 = _
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, z p * z q := by
      rw [sq, sum_mul]
      exact sum_congr rfl fun _ _ => mul_sum _ _ _
    _ = ∑ p ∈ S, z p ^ 2 := by
      refine sum_congr rfl fun p hp => ?_
      rw [sum_eq_single_of_mem p hp (fun q hq hqp => hcross p hp q hq hqp.symm), sq]
    _ = _ := sum_congr rfl fun p _ => by
      dsimp only [z]
      split_ifs <;> simp only [zero_pow (by decide : 2 ≠ 0)]

private theorem sum_cofactorSpikes_sq (S : Finset ℕ) (D N : ℕ)
    (a : ℕ → ℕ → ℝ) (hP : ∀ p ∈ S, p.Prime)
    (hcp : ∀ p ∈ S, ∀ d ∈ Icc 1 D, d.Coprime p)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q) :
    (∑ n ∈ Icc 1 N, cofactorSpikes S D a n ^ 2) =
      ∑ p ∈ S, ((p : ℝ) / p.totient) *
        ∑ j ∈ Icc 1 (N / p), cofactorProfile D (a p) j ^ 2 := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ S, if p ∣ n then
        (((p : ℝ) / Real.sqrt (p.totient : ℝ)) * cofactorProfile D (a p) n) ^ 2 else 0 :=
      sum_congr rfl fun n hn => cofactorSpikes_sq S D a hP hdisj hn
    _ = ∑ p ∈ S, ∑ n ∈ Icc 1 N, if p ∣ n then
        (((p : ℝ) / Real.sqrt (p.totient : ℝ)) * cofactorProfile D (a p) n) ^ 2 else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun p hp => ?_
      rw [← sum_filter, mul_sum]
      refine (sum_bij' (fun j _ => p * j) (fun n _ => n / p) ?_ ?_ ?_ ?_ ?_).symm
      · intro j hj
        simp only [mem_Icc, mem_filter] at hj ⊢
        refine ⟨⟨Nat.mul_pos (hP p hp).pos hj.1, ?_⟩, ⟨j, rfl⟩⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (hP p hp).pos).mp hj.2
      · intro n hn
        obtain ⟨hnI, hpn⟩ := mem_filter.mp hn
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hnI).1 hpn)
          (hP p hp).pos, Nat.div_le_div_right (mem_Icc.mp hnI).2⟩
      · intro j _
        exact Nat.mul_div_cancel_left j (hP p hp).pos
      · intro n hn
        exact (Nat.mul_comm p (n / p)).trans (Nat.div_mul_cancel (mem_filter.mp hn).2)
      · intro j _
        rw [cofactorProfile_mul_prime (hP p hp) (hcp p hp), mul_pow, div_pow,
          div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
        have ht0 : (p.totient : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (hP p hp).pos).ne'
        field_simp [hp0, ht0]
        ring

private theorem cofactorProfile_upper {D N : ℕ} (hDN : D * D ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, cofactorProfile D a n ^ 2) ≤
      6 * Real.log N * ∑ d ∈ Icc 1 D, a d ^ 2 := by
  have hL0 : 0 < Real.log (N : ℝ) := (by positivity : 0 < 4 * Real.exp 7).trans_le hL
  have h := ramanujanConductor_upper_riesz hDN hL a
  rw [norm_sum_normalizedRamanujanHorizonVector_sq, div_le_iff₀ hL0] at h
  exact h.trans_eq (by ring)

private theorem spike_sub_background_bound {M N : ℕ} (hMN : M ≤ N)
    (s b : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hs : ∀ n ∈ Icc 1 M, s n = 0)
    (hb : δ * (∑ n ∈ Icc 1 N, b n ^ 2) ≤ 6 * ∑ n ∈ Icc 1 M, b n ^ 2) :
    δ * (∑ n ∈ Icc 1 N, s n ^ 2) ≤
      13 * ∑ n ∈ Icc 1 N, (s n - b n) ^ 2 := by
  have hhead : (∑ n ∈ Icc 1 M, b n ^ 2) ≤
      ∑ n ∈ Icc 1 N, (s n - b n) ^ 2 := by
    calc
      _ = ∑ n ∈ Icc 1 M, (s n - b n) ^ 2 :=
        sum_congr rfl fun n hn => by rw [hs n hn, zero_sub, neg_sq]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN)
        fun _ _ _ => sq_nonneg _
  have htriangle : (∑ n ∈ Icc 1 N, s n ^ 2) ≤
      2 * (∑ n ∈ Icc 1 N, (s n - b n) ^ 2) + 2 * ∑ n ∈ Icc 1 N, b n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n _ => by nlinarith only [sq_nonneg (s n - 2 * b n)]
  have ht := mul_le_mul_of_nonneg_left htriangle hδ.le
  have hx0 : 0 ≤ ∑ n ∈ Icc 1 N, (s n - b n) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hc := mul_le_mul_of_nonneg_right hδ1 hx0
  nlinarith only [ht, hb, hhead, hc]

end GaloisForLFunctions.CompletedArithmeticForms
