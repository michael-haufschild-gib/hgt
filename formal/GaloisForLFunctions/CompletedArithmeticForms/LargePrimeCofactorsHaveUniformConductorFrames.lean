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

private theorem cofactorProfile_mul_prime {D p : ℕ}
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
        rw [cofactorProfile_mul_prime (hcp p hp), mul_pow, div_pow,
          div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
        have ht0 : (p.totient : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (hP p hp).pos).ne'
        field_simp [hp0, ht0]

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

private theorem norm_primeCofactorHorizonPacket_sq (S : Finset ℕ) (D N : ℕ)
    (a : ℕ → ℕ → ℝ) :
    ‖primeCofactorHorizonPacket S D N a‖ ^ 2 =
      (∑ n ∈ Icc 1 N,
        (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d * ramanujanPoleProfile (d * p) n) ^ 2) /
          Real.log N := by
  have hcoord (n : PrimeHorizonIndex N) : primeCofactorHorizonPacket S D N a n =
      (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d * ramanujanPoleProfile (d * p) n) /
        Real.sqrt (Real.log N) := by
    simp only [primeCofactorHorizonPacket, normalizedRamanujanHorizonVector,
      ramanujanHorizonVector, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul]
    rw [sum_div]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_div]
    exact sum_congr rfl fun d _ => by ring
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hcoord, div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N) (fun n =>
    (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d * ramanujanPoleProfile (d * p) n) ^ 2)

/-- A growing small cofactor preserves the large-prime frame beyond the square-root
horizon. The constant is uniform in both conductor indices and all coefficients. -/
theorem primeCofactorBand_lower_frame {N D : ℕ} {θ ε : ℝ}
    (hL : 4 * Real.exp 7 ≤ Real.log (N : ℝ)) (hD : 2 ≤ D)
    (hθ : (1 / 2 : ℝ) < θ) (hε : 0 ≤ ε) (hrange : θ + 2 * ε < 1)
    (hDN : (D : ℝ) ≤ (N : ℝ) ^ ε)
    (S : Finset ℕ) (hP : ∀ p ∈ S, p.Prime)
    (hband : ∀ p ∈ S, Real.sqrt (N : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) ^ θ)
    (a : ℕ → ℕ → ℝ) :
    ((1 - 4 * ε) * (1 - θ - 2 * ε) / 26) *
        (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d ^ 2) ≤
      ‖primeCofactorHorizonPacket S D N a‖ ^ 2 := by
  have hL0 : 0 < Real.log (N : ℝ) := (by positivity : 0 < 4 * Real.exp 7).trans_le hL
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hh : N = 0 ∨ N = 1 := by omega
    rcases hh with rfl | rfl <;> norm_num at hL0
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hε4 : ε < 1 / 4 := by linarith only [hθ, hrange]
  have hDlog : Real.log D ≤ ε * Real.log N := by
    have hh := Real.log_le_log hD0 hDN
    rwa [Real.log_rpow hN0] at hh
  have hDroot : (D : ℝ) < Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact hDN.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith only [hε4]))
  have hDNsq : D * D ≤ N := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg D) hDroot.le 2
    rw [Real.sq_sqrt hN0.le] at hh
    rw [pow_two] at hh
    exact_mod_cast hh
  have hcp : ∀ p ∈ S, ∀ d ∈ Icc 1 D, d.Coprime p := by
    intro p hp d hd
    have hdp : d < p := by
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hd).2
      exact_mod_cast (hdD.trans_lt hDroot).trans (hband p hp).1
    exact ((hP p hp).coprime_iff_not_dvd.mpr
      (fun hpd => (not_le_of_gt hdp) (Nat.le_of_dvd (mem_Icc.mp hd).1 hpd))).symm
  have hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q := by
    intro p hp q hq _
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hh := mul_lt_mul (hband p hp).1 (hband q hq).1.le
      (Real.sqrt_pos.mpr hN0) hp0.le
    rw [← sq, Real.sq_sqrt hN0.le] at hh
    exact_mod_cast hh
  let M := ⌊Real.sqrt (N : ℝ)⌋₊
  let δ := (1 / 2 : ℝ) - 2 * ε
  let t := 1 - θ - 2 * ε
  let b := fun d => ∑ p ∈ S, a p d / Real.sqrt (p.totient : ℝ)
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hε4]
  have hδ1 : δ ≤ 1 / 2 := by dsimp only [δ]; linarith only [hε]
  have ht : 0 < t := by dsimp only [t]; linarith only [hrange]
  have hMroot : (M : ℝ) ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
  have hrootN : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith only [Real.sq_sqrt hN0.le, Real.sqrt_nonneg (N : ℝ), hN1]
  have hMN : M ≤ N := by exact_mod_cast hMroot.trans hrootN
  have hMp : ∀ p ∈ S, M < p := by
    intro p hp
    exact_mod_cast hMroot.trans_lt (hband p hp).1
  have hheadlog : Real.log N / 2 ≤ Real.log ((M : ℝ) + 1) := by
    have hh := Real.log_le_log (Real.sqrt_pos.mpr hN0)
      (Nat.lt_floor_add_one (Real.sqrt (N : ℝ))).le
    have he := congrArg Real.log (Real.sq_sqrt hN0.le)
    rw [Real.log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    linarith only [hh, he]
  have hb_low : δ * Real.log N * (∑ d ∈ Icc 1 D, b d ^ 2) ≤
      ∑ n ∈ Icc 1 M, cofactorBackground S D a n ^ 2 := by
    have hcoef : δ * Real.log N ≤ Real.log ((M : ℝ) + 1) - 2 * Real.log D := by
      dsimp only [δ]
      nlinarith only [hheadlog, hDlog]
    exact (mul_le_mul_of_nonneg_right hcoef (sum_nonneg fun _ _ => sq_nonneg _)).trans
      (ramanujanPoleProfile_family_squareRoot_lower hD b M)
  have hb_up : (∑ n ∈ Icc 1 N, cofactorBackground S D a n ^ 2) ≤
      6 * Real.log N * ∑ d ∈ Icc 1 D, b d ^ 2 := cofactorProfile_upper hDNsq hL b
  have hb : δ * (∑ n ∈ Icc 1 N, cofactorBackground S D a n ^ 2) ≤
      6 * ∑ n ∈ Icc 1 M, cofactorBackground S D a n ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hb_up hδ.le
    nlinarith only [hh, hb_low]
  have hs : t * Real.log N * (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d ^ 2) ≤
      ∑ n ∈ Icc 1 N, cofactorSpikes S D a n ^ 2 := by
    rw [sum_cofactorSpikes_sq S D N a hP hcp hdisj, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have htot : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr (hP p hp).pos
    have hratio : 1 ≤ (p : ℝ) / p.totient := (one_le_div htot).mpr
      (by exact_mod_cast Nat.totient_le p)
    have hfloor : (N : ℝ) / p < (N / p : ℕ) + 1 := by
      simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
        Nat.lt_floor_add_one ((N : ℝ) / p)
    have hlog := Real.log_le_log (div_pos hN0 hp0) hfloor.le
    rw [Real.log_div hN0.ne' hp0.ne'] at hlog
    have hlogp := Real.log_le_log hp0 (hband p hp).2
    rw [Real.log_rpow hN0] at hlogp
    have hcoef : t * Real.log N ≤ Real.log ((N / p : ℕ) + 1 : ℝ) - 2 * Real.log D := by
      dsimp only [t]
      nlinarith only [hlog, hlogp, hDlog]
    have hlower := (mul_le_mul_of_nonneg_right hcoef
      (sum_nonneg fun _ _ => sq_nonneg _)).trans
      (ramanujanPoleProfile_family_squareRoot_lower hD (a p) (N / p))
    exact hlower.trans (le_mul_of_one_le_left (sum_nonneg fun _ _ => sq_nonneg _) hratio)
  have hpaid := spike_sub_background_bound hMN (cofactorSpikes S D a)
    (cofactorBackground S D a) hδ hδ1
    (fun n hn => cofactorSpikes_vanishes_before S D a hMp (mem_Icc.mp hn).1 (mem_Icc.mp hn).2) hb
  have hnrm : (∑ n ∈ Icc 1 N,
      (cofactorSpikes S D a n - cofactorBackground S D a n) ^ 2) =
      Real.log N * ‖primeCofactorHorizonPacket S D N a‖ ^ 2 := by
    rw [norm_primeCofactorHorizonPacket_sq]
    have hrows := sum_congr rfl fun n (_ : n ∈ Icc 1 N) => congrArg (fun x : ℝ => x ^ 2)
      (cofactor_profile_split S a hP hcp n).symm
    rw [hrows]
    field_simp [hL0.ne']
  rw [hnrm] at hpaid
  have hmain := (mul_le_mul_of_nonneg_left hs hδ.le).trans hpaid
  have hc : Real.log N * (δ * t / 13 * (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d ^ 2)) ≤
      Real.log N * ‖primeCofactorHorizonPacket S D N a‖ ^ 2 := by
    nlinarith only [hmain]
  have hresult := (mul_le_mul_iff_right₀ hL0).mp hc
  have hcoef_eq : (1 - 4 * ε) * (1 - θ - 2 * ε) / 26 = δ * t / 13 := by
    dsimp only [δ, t]
    ring
  rw [hcoef_eq]
  exact hresult

/-- The composite family has a fixed positive lower frame constant throughout
every exponent range `1/2 < θ` and `θ + 2ε < 1`. -/
theorem exists_primeCofactorBand_uniform_lower_frame {θ ε : ℝ}
    (hθ : (1 / 2 : ℝ) < θ) (hε : 0 < ε) (hrange : θ + 2 * ε < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ D : ℕ, 2 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ ε →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        (∀ p ∈ S, Real.sqrt (N : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) ^ θ) →
      ∀ a : ℕ → ℕ → ℝ,
        κ * (∑ p ∈ S, ∑ d ∈ Icc 1 D, a p d ^ 2) ≤
          ‖primeCofactorHorizonPacket S D N a‖ ^ 2 := by
  have hfirst : 0 < 1 - 4 * ε := by linarith only [hθ, hrange]
  have hsecond : 0 < 1 - θ - 2 * ε := by linarith only [hrange]
  refine ⟨(1 - 4 * ε) * (1 - θ - 2 * ε) / 26, by positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (4 * Real.exp 7)] with N hL
  intro D hD hDN S hP hband a
  exact primeCofactorBand_lower_frame hL hD hθ hε.le hrange hDN S hP hband a

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.primeCofactorBand_lower_frame
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_primeCofactorBand_uniform_lower_frame
