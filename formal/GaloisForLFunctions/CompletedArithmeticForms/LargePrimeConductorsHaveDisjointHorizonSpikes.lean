import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus

/-!
# Large prime conductors have disjoint horizon spikes

Above the square-root horizon, distinct prime divisibility supports are disjoint.
Their common constant mode is paid by the harmonic mass below those supports.
This gives lower frame bounds beyond the square-root range for prime conductors.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory CriticalScaleArithmeticRigidity
  CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
  BezoutValuationIncidence SuccessorShellArithmetic

private theorem norm_sub_scalar_ge_missing_support {ι : Type*} (S : Finset ι)
    (P : ι → Prop) (f g : ι → ℝ) (s : ℝ)
    (hf : ∀ i ∈ S, P i → f i = 0) :
    (∑ i ∈ S, g i ^ 2) * (∑ i ∈ S, (f i - s * g i) ^ 2) ≥
      (∑ i ∈ S, if P i then g i ^ 2 else 0) * (∑ i ∈ S, f i ^ 2) := by
  let tail := fun i => if P i then 0 else g i
  let G := ∑ i ∈ S, g i ^ 2
  let H := ∑ i ∈ S, if P i then g i ^ 2 else 0
  let A := ∑ i ∈ S, f i ^ 2
  let F := ∑ i ∈ S, f i * g i
  have hcross : (∑ i ∈ S, f i * tail i) = F := by
    apply sum_congr rfl
    intro i hi
    by_cases hP : P i
    · simp only [tail, if_pos hP, hf i hi hP, zero_mul]
    · simp only [tail, if_neg hP]
  have htail : (∑ i ∈ S, tail i ^ 2) = G - H := by
    have hh : (∑ i ∈ S, tail i ^ 2) + H = G := by
      dsimp only [H, G]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      by_cases hP : P i <;> simp only [tail, hP, if_true, if_false, zero_pow (by decide : 2 ≠ 0),
        zero_add, add_zero]
    linarith only [hh]
  have hcs := sum_mul_sq_le_sq_mul_sq S f tail
  rw [hcross, htail] at hcs
  change F ^ 2 ≤ A * (G - H) at hcs
  have henergy : (∑ i ∈ S, (f i - s * g i) ^ 2) = A - 2 * s * F + s ^ 2 * G := by
    dsimp only [A, F, G]
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change G * (∑ i ∈ S, (f i - s * g i) ^ 2) ≥ H * A
  rw [henergy]
  nlinarith only [hcs, sq_nonneg (s * G - F)]

private def primeSpike (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, ((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) * (if p ∣ n then 1 else 0)

private def primeOffset (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, a p / Real.sqrt (p.totient : ℝ)

private theorem harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem div_sqrt_nat_sq (x : ℝ) (n : ℕ) :
    (x / Real.sqrt n) ^ 2 = x ^ 2 / n := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

private theorem prime_packet_profile_eq (S : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∑ p ∈ S, a p * ramanujanPoleProfile p n) =
      (primeSpike S a n - primeOffset S a) / Real.sqrt n := by
  have hterm (p : ℕ) (hp : p ∈ S) : a p * ramanujanPoleProfile p n =
      (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) * (if p ∣ n then 1 else 0) -
        a p / Real.sqrt (p.totient : ℝ)) / Real.sqrt n := by
    rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient (hP p hp).pos,
      ramanujanCoefficient_prime (hP p hp)]
    split_ifs <;> ring
  calc
    _ = ∑ p ∈ S, (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) *
        (if p ∣ n then 1 else 0) - a p / Real.sqrt (p.totient : ℝ)) / Real.sqrt n :=
      sum_congr rfl hterm
    _ = _ := by rw [← sum_div, sum_sub_distrib]; rfl

private theorem norm_prime_packet_eq (S : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ S, p.Prime) (N : ℕ) :
    ‖∑ p ∈ S, a p • normalizedRamanujanHorizonVector p N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n) / Real.log N := by
  rw [norm_sum_normalizedRamanujanHorizonVector_sq]
  congr 1
  exact sum_congr rfl fun n _ => by rw [prime_packet_profile_eq S a hP, div_sqrt_nat_sq]

private theorem sum_inv_multiples_real (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), 1 / (n : ℝ)) =
      (1 / (d : ℝ)) * (harmonic (N / d) : ℝ) := by
  rw [harmonic_real_eq_sum, mul_sum]
  refine (sum_bij' (fun k _ => d * k) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [mem_Icc, mem_filter] at hk ⊢
    refine ⟨⟨Nat.mul_pos hd (by omega), ?_⟩, ⟨k, rfl⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hk.2
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd, Nat.div_le_div_right hnN⟩
  · intro k _
    exact Nat.mul_div_cancel_left k hd
  · intro n hn
    have hdn := (mem_filter.mp hn).2
    exact (Nat.mul_comm d (n / d)).trans (Nat.div_mul_cancel hdn)
  · intro k _
    simp only [Nat.cast_mul, one_div, mul_inv_rev]
    ring

private theorem primeSpike_vanishes_before (S : Finset ℕ) (a : ℕ → ℝ) {M n : ℕ}
    (hM : ∀ p ∈ S, M < p) (hn : 0 < n) (hnM : n ≤ M) :
    primeSpike S a n = 0 := by
  apply sum_eq_zero
  intro p hp
  have hnot : ¬p ∣ n := fun h => (not_lt_of_ge ((Nat.le_of_dvd hn h).trans hnM)) (hM p hp)
  rw [if_neg hnot, mul_zero]

private theorem primeSpike_sq_eq (S : Finset ℕ) (a : ℕ → ℝ) {N n : ℕ}
    (hP : ∀ p ∈ S, p.Prime)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q)
    (hn : n ∈ Icc 1 N) :
    primeSpike S a n ^ 2 =
      ∑ p ∈ S, ((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) ^ 2 * (if p ∣ n then 1 else 0) := by
  let z := fun p : ℕ => ((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) * (if p ∣ n then 1 else 0)
  have hcross (p : ℕ) (hp : p ∈ S) (q : ℕ) (hq : q ∈ S) (hne : p ≠ q) : z p * z q = 0 := by
    by_cases hpn : p ∣ n
    · by_cases hqn : q ∣ n
      · have hcop := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hne
        have hpq := Nat.le_of_dvd ((mem_Icc.mp hn).1) (hcop.mul_dvd_of_dvd_of_dvd hpn hqn)
        exact False.elim ((not_lt_of_ge (hpq.trans (mem_Icc.mp hn).2)) (hdisj p hp q hq hne))
      · simp only [z, if_neg hqn, mul_zero]
    · simp only [z, if_neg hpn, mul_zero, zero_mul]
  change (∑ p ∈ S, z p) ^ 2 = _
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, z p * z q := by
      rw [sq, sum_mul]
      exact sum_congr rfl fun p _ => mul_sum _ _ _
    _ = ∑ p ∈ S, z p ^ 2 := by
      apply sum_congr rfl
      intro p hp
      rw [sum_eq_single_of_mem p hp (fun q hq hqp => hcross p hp q hq hqp.symm), sq]
    _ = _ := sum_congr rfl fun p _ => by
      dsimp only [z]
      split_ifs <;> simp only [mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0)]

private theorem sum_primeSpike_sq_div (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hP : ∀ p ∈ S, p.Prime)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q) :
    (∑ n ∈ Icc 1 N, primeSpike S a n ^ 2 / n) =
      ∑ p ∈ S, ((p : ℝ) / p.totient) * (harmonic (N / p) : ℝ) * a p ^ 2 := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ S,
        (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) ^ 2 * (if p ∣ n then 1 else 0)) / n := by
      apply sum_congr rfl
      intro n hn
      rw [primeSpike_sq_eq S a hP hdisj hn, sum_div]
    _ = ∑ p ∈ S, ∑ n ∈ Icc 1 N,
        (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) ^ 2 * (if p ∣ n then 1 else 0)) / n := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      have htot : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr (hP p hp).pos
      have heq : (∑ n ∈ Icc 1 N,
          (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) ^ 2 * (if p ∣ n then 1 else 0)) / n) =
          ((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) ^ 2 *
            ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) := by
        rw [sum_filter, mul_sum]
        apply sum_congr rfl
        intro n _
        by_cases hpn : p ∣ n <;> simp only [hpn, if_true, if_false, mul_one, mul_zero, zero_div]
        ring
      rw [heq, sum_inv_multiples_real N p (hP p hp).pos, div_pow,
        Real.sq_sqrt htot.le]
      field_simp

private theorem sum_primeSpike_div (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hP : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ Icc 1 N, primeSpike S a n / n) =
      ∑ p ∈ S, (a p / Real.sqrt (p.totient : ℝ)) * (harmonic (N / p) : ℝ) := by
  simp only [primeSpike, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have heq : (∑ n ∈ Icc 1 N,
      (((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) * (if p ∣ n then 1 else 0)) / n) =
      ((p : ℝ) * a p / Real.sqrt (p.totient : ℝ)) *
        ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) := by
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro n _
    by_cases hpn : p ∣ n <;> simp only [hpn, if_true, if_false, mul_one, mul_zero, zero_div]
    ring
  rw [heq, sum_inv_multiples_real N p (hP p hp).pos]
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (hP p hp).pos)).ne'
  field_simp

/-- Above pairwise product horizons, the prime-conductor Gram is a positive
diagonal plus the correction from its common constant mode. -/
theorem primeConductor_gram_eq_diagonal_add_rank_two (S : Finset ℕ) (a : ℕ → ℝ) {N : ℕ}
    (hL : 0 < Real.log (N : ℝ)) (hP : ∀ p ∈ S, p.Prime)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q) :
    Real.log (N : ℝ) * ‖∑ p ∈ S, a p • normalizedRamanujanHorizonVector p N‖ ^ 2 =
      (∑ p ∈ S, ((p : ℝ) / p.totient) * (harmonic (N / p) : ℝ) * a p ^ 2) +
      (harmonic N : ℝ) * (∑ p ∈ S, a p / Real.sqrt (p.totient : ℝ)) ^ 2 -
      2 * (∑ p ∈ S, a p / Real.sqrt (p.totient : ℝ)) *
        ∑ p ∈ S, (a p / Real.sqrt (p.totient : ℝ)) * (harmonic (N / p) : ℝ) := by
  rw [norm_prime_packet_eq S a hP N]
  have hcancel : Real.log (N : ℝ) *
      ((∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n) / Real.log N) =
      ∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n := by field_simp
  rw [hcancel]
  have hexpand : (∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n) =
      (∑ n ∈ Icc 1 N, primeSpike S a n ^ 2 / n) +
      (harmonic N : ℝ) * primeOffset S a ^ 2 -
      2 * primeOffset S a * ∑ n ∈ Icc 1 N, primeSpike S a n / n := by
    rw [harmonic_real_eq_sum, sum_mul, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [hexpand, sum_primeSpike_sq_div S a N hP hdisj, sum_primeSpike_div S a N hP]
  rfl

private theorem harmonic_head_eq {M N : ℕ} (hMN : M ≤ N) :
    (∑ n ∈ Icc 1 N, if n ≤ M then (1 / Real.sqrt n) ^ 2 else 0) = (harmonic M : ℝ) := by
  have hfilter : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n
    simp only [mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hMN⟩, h.2⟩⟩
  simp only [div_sqrt_nat_sq, one_pow]
  rw [← sum_filter, hfilter, ← harmonic_real_eq_sum]

/-- Harmonic mass below the divisibility spikes pays their shared constant mode.
The resulting finite lower bound has no prime-distribution input. -/
theorem primeConductor_lower_frame_of_disjoint_multiples (S : Finset ℕ) (a : ℕ → ℝ)
    {M N : ℕ} (hL : 0 < Real.log (N : ℝ)) (hMN : M ≤ N)
    (hP : ∀ p ∈ S, p.Prime) (hM : ∀ p ∈ S, M < p)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q) :
    (harmonic M : ℝ) *
      (∑ p ∈ S, ((p : ℝ) / p.totient) * (harmonic (N / p) : ℝ) * a p ^ 2) ≤
      (harmonic N : ℝ) * Real.log N *
        ‖∑ p ∈ S, a p • normalizedRamanujanHorizonVector p N‖ ^ 2 := by
  have hf : ∀ n ∈ Icc 1 N, n ≤ M → primeSpike S a n / Real.sqrt n = 0 := by
    intro n hn hnM
    rw [primeSpike_vanishes_before S a hM ((mem_Icc.mp hn).1) hnM, zero_div]
  have hh := norm_sub_scalar_ge_missing_support (Icc 1 N) (fun n => n ≤ M)
    (fun n => primeSpike S a n / Real.sqrt n) (fun n => 1 / Real.sqrt n)
    (primeOffset S a) hf
  have hG : (∑ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2) = (harmonic N : ℝ) := by
    simp only [div_sqrt_nat_sq, one_pow]
    exact (harmonic_real_eq_sum N).symm
  have hA : (∑ n ∈ Icc 1 N, (primeSpike S a n / Real.sqrt n) ^ 2) =
      ∑ n ∈ Icc 1 N, primeSpike S a n ^ 2 / n :=
    sum_congr rfl fun n _ => div_sqrt_nat_sq _ n
  have hE : (∑ n ∈ Icc 1 N,
      (primeSpike S a n / Real.sqrt n - primeOffset S a * (1 / Real.sqrt n)) ^ 2) =
      ∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n := by
    apply sum_congr rfl
    intro n _
    rw [show primeSpike S a n / Real.sqrt n - primeOffset S a * (1 / Real.sqrt n) =
      (primeSpike S a n - primeOffset S a) / Real.sqrt n by ring, div_sqrt_nat_sq]
  simp only [hG, hE, harmonic_head_eq hMN, hA, sum_primeSpike_sq_div S a N hP hdisj] at hh
  calc
    _ ≤ (harmonic N : ℝ) *
        ∑ n ∈ Icc 1 N, (primeSpike S a n - primeOffset S a) ^ 2 / n := hh
    _ = _ := by rw [norm_prime_packet_eq S a hP N]; field_simp

/-- Prime conductors strictly above the square-root horizon retain a uniform lower
frame bound through every fixed polynomial exponent below one. -/
theorem primeConductorBand_lower_frame {N : ℕ} {θ : ℝ}
    (hL1 : 1 ≤ Real.log (N : ℝ)) (hθ : θ < 1)
    (S : Finset ℕ) (hP : ∀ p ∈ S, p.Prime)
    (hband : ∀ p ∈ S, Real.sqrt (N : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) ^ θ)
    (a : ℕ → ℝ) :
    ((1 - θ) / 4) * (∑ p ∈ S, a p ^ 2) ≤
      ‖∑ p ∈ S, a p • normalizedRamanujanHorizonVector p N‖ ^ 2 := by
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hcases : N = 0 ∨ N = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hL1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  let M := ⌊Real.sqrt (N : ℝ)⌋₊
  have hMroot : (M : ℝ) ≤ Real.sqrt (N : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hrootN : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith only [Real.sq_sqrt hN.le, Real.sqrt_nonneg (N : ℝ), hN1]
  have hMN : M ≤ N := by exact_mod_cast hMroot.trans hrootN
  have hMp : ∀ p ∈ S, M < p := by
    intro p hp
    exact_mod_cast hMroot.trans_lt (hband p hp).1
  have hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → N < p * q := by
    intro p hp q hq _hne
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (hP p hp).pos
    have hh : (N : ℝ) < (p : ℝ) * q := by
      calc
        _ = Real.sqrt (N : ℝ) * Real.sqrt N := by rw [← sq, Real.sq_sqrt hN.le]
        _ < (p : ℝ) * Real.sqrt N := mul_lt_mul_of_pos_right (hband p hp).1 hs
        _ ≤ (p : ℝ) * q := mul_le_mul_of_nonneg_left (hband q hq).1.le hpR.le
    exact_mod_cast hh
  have hhead : Real.log (N : ℝ) / 2 ≤ (harmonic M : ℝ) := by
    have hh := log_le_harmonic_floor (Real.sqrt (N : ℝ)) (Real.sqrt_nonneg _)
    have heq := congrArg Real.log (Real.sq_sqrt hN.le)
    rw [Real.log_pow] at heq
    norm_num only [Nat.cast_ofNat] at heq
    change Real.log (Real.sqrt (N : ℝ)) ≤ (harmonic M : ℝ) at hh
    linarith only [hh, heq]
  have htotal : (harmonic N : ℝ) ≤ 2 * Real.log N := by
    linarith only [harmonic_le_one_add_log N, hL1]
  have hdiag : ((1 - θ) * Real.log N) * (∑ p ∈ S, a p ^ 2) ≤
      ∑ p ∈ S, ((p : ℝ) / p.totient) * (harmonic (N / p) : ℝ) * a p ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (hP p hp).pos
    have htot : 0 < (p.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (hP p hp).pos
    have hratio : 1 ≤ (p : ℝ) / p.totient := (one_le_div htot).mpr
      (by exact_mod_cast Nat.totient_le p)
    have hH : (1 - θ) * Real.log N ≤ (harmonic (N / p) : ℝ) := by
      have hh := log_le_harmonic_floor ((N : ℝ) / p) (div_nonneg hN.le hpR.le)
      rw [Nat.floor_div_natCast, Nat.floor_natCast, Real.log_div hN.ne' hpR.ne'] at hh
      have hlogp := Real.log_le_log hpR (hband p hp).2
      rw [Real.log_rpow hN] at hlogp
      linarith only [hh, hlogp]
    have hH0 : 0 ≤ (harmonic (N / p) : ℝ) :=
      (mul_nonneg (sub_pos.mpr hθ).le hL.le).trans hH
    exact mul_le_mul_of_nonneg_right
      (hH.trans (le_mul_of_one_le_left hH0 hratio)) (sq_nonneg _)
  have hfinite := primeConductor_lower_frame_of_disjoint_multiples S a hL hMN hP hMp hdisj
  let X := ‖∑ p ∈ S, a p • normalizedRamanujanHorizonVector p N‖ ^ 2
  let A := ∑ p ∈ S, a p ^ 2
  have hX : 0 ≤ X := sq_nonneg _
  have hA : 0 ≤ A := sum_nonneg fun p _ => sq_nonneg (a p)
  have hmain : (Real.log N / 2) * ((1 - θ) * Real.log N * A) ≤
      (2 * Real.log N) * Real.log N * X := by
    have hlo := mul_le_mul hhead hdiag
      (mul_nonneg (mul_nonneg (sub_pos.mpr hθ).le hL.le) hA)
      ((div_nonneg hL.le zero_le_two).trans hhead)
    have hup := mul_le_mul_of_nonneg_right htotal (mul_nonneg hL.le hX)
    exact hlo.trans (hfinite.trans (by nlinarith only [hup]))
  have hscaled : Real.log (N : ℝ) ^ 2 * (((1 - θ) / 4) * A) ≤
      Real.log (N : ℝ) ^ 2 * X := by nlinarith only [hmain]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp hscaled

#print axioms primeConductor_gram_eq_diagonal_add_rank_two
#print axioms primeConductor_lower_frame_of_disjoint_multiples
#print axioms primeConductorBand_lower_frame

end GaloisForLFunctions.CompletedArithmeticForms
