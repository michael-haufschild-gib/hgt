import GaloisForLFunctions.RHTower.Sieve.ReciprocalMoebiusAmplitude
import Mathlib.NumberTheory.EulerProduct.Basic

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Localized reciprocal–Möbius amplitudes

The reciprocal--Möbius amplitude is restricted to integers whose prime factors divide a fixed
positive integer `r`. Finite-prime Euler products then give its exact global masses:

* signed mass `1` for `r = 1` and `0` otherwise;
* absolute mass `2 ^ ω(r)`.

These identities supply the one-variable fibres of the absolutely summable bivariate correction in
the sharp Barban--Vehov diagonal.
-/

namespace RHTower.Sieve

noncomputable section

def primeSupportedOn (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p ∣ r

theorem primeSupportedOn_mul_iff (r m n : ℕ) :
    primeSupportedOn r (m * n) ↔ primeSupportedOn r m ∧ primeSupportedOn r n := by
  constructor
  · intro h
    constructor
    · intro p hp hpm
      exact h p hp (dvd_mul_of_dvd_left hpm n)
    · intro p hp hpn
      exact h p hp (dvd_mul_of_dvd_right hpn m)
  · rintro ⟨hm, hn⟩ p hp hpmn
    exact (hp.dvd_mul.mp hpmn).elim (hm p hp) (hn p hp)

@[simp] theorem primeSupportedOn_one (r : ℕ) : primeSupportedOn r 1 := by
  intro p hp h
  exact (hp.not_dvd_one h).elim

def localizedReciprocalMoebiusAmplitude (r : ℕ) : ArithmeticFunction ℝ :=
  by
    classical
    exact ⟨fun n => if primeSupportedOn r n then reciprocalMoebiusAmplitude n else 0, by simp⟩

@[simp] theorem localizedReciprocalMoebiusAmplitude_one (r : ℕ) :
    localizedReciprocalMoebiusAmplitude r 1 = 1 := by
  classical
  simp [localizedReciprocalMoebiusAmplitude]

theorem isMultiplicative_localizedReciprocalMoebiusAmplitude (r : ℕ) :
    (localizedReciprocalMoebiusAmplitude r).IsMultiplicative := by
  classical
  constructor
  · exact localizedReciprocalMoebiusAmplitude_one r
  · intro m n hmn
    have hamp := isMultiplicative_reciprocalMoebiusAmplitude.map_mul_of_coprime hmn
    by_cases hm : primeSupportedOn r m <;>
      by_cases hn : primeSupportedOn r n <;>
      simp [localizedReciprocalMoebiusAmplitude, primeSupportedOn_mul_iff, hm, hn, hamp]

theorem primeSupportedOn_prime_pow_iff {r p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    primeSupportedOn r (p ^ i) ↔ p ∣ r := by
  constructor
  · intro h
    exact h p hp (dvd_pow_self p (by omega))
  · intro hpr q hq hqpow
    have hqp : q ∣ p := hq.dvd_of_dvd_pow hqpow
    have hEq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    simpa [hEq] using hpr

theorem localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd
    {r p i : ℕ} (hp : p.Prime) (hpr : p ∣ r) :
    localizedReciprocalMoebiusAmplitude r (p ^ i) =
      reciprocalMoebiusAmplitude (p ^ i) := by
  classical
  rcases i with _ | i
  · simp
  · change (if primeSupportedOn r (p ^ (i + 1)) then
        reciprocalMoebiusAmplitude (p ^ (i + 1)) else 0) = _
    rw [if_pos ((primeSupportedOn_prime_pow_iff
      (r := r) (p := p) (i := i + 1) hp (by omega)).2 hpr)]

theorem localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd
    {r p i : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    localizedReciprocalMoebiusAmplitude r (p ^ (i + 1)) = 0 := by
  classical
  change (if primeSupportedOn r (p ^ (i + 1)) then
      reciprocalMoebiusAmplitude (p ^ (i + 1)) else 0) = 0
  rw [if_neg]
  exact fun hs => hpr ((primeSupportedOn_prime_pow_iff
    (r := r) (p := p) (i := i + 1) hp (by omega)).1 hs)

theorem primeSupportedOn_mem_smoothNumbers {r n : ℕ} (hr : 0 < r)
    (h : primeSupportedOn r n) : n ∈ (r + 1).smoothNumbers := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpn
  exact Nat.lt_succ_iff.mpr (Nat.le_of_dvd hr (h p hp hpn))

theorem localizedReciprocalMoebiusAmplitude_eq_zero_of_not_mem_smoothNumbers
    {r n : ℕ} (hr : 0 < r) (h : n ∉ (r + 1).smoothNumbers) :
    localizedReciprocalMoebiusAmplitude r n = 0 := by
  classical
  change (if primeSupportedOn r n then reciprocalMoebiusAmplitude n else 0) = 0
  rw [if_neg]
  exact fun hs => h (primeSupportedOn_mem_smoothNumbers hr hs)

theorem summable_abs_localizedReciprocalMoebiusAmplitude_prime_pow
    {r p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => |localizedReciprocalMoebiusAmplitude r (p ^ i)|) := by
  by_cases hpr : p ∣ r
  · exact (summable_abs_reciprocalMoebiusAmplitude_prime_pow hp).congr
      (fun i => by rw [localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd hp hpr])
  · have htail : Summable (fun i : ℕ =>
        |localizedReciprocalMoebiusAmplitude r (p ^ (i + 1))|) := by
      exact summable_zero.congr (fun i => by
        simp [localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hpr])
    exact (summable_nat_add_iff 1).mp (by simpa only [Nat.add_comm] using htail)

theorem summable_localizedReciprocalMoebiusAmplitude_prime_pow
    {r p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => localizedReciprocalMoebiusAmplitude r (p ^ i)) := by
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using
    summable_abs_localizedReciprocalMoebiusAmplitude_prime_pow (r := r) hp

theorem tsum_localizedReciprocalMoebiusAmplitude_prime_pow
    {r p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) =
      if p ∣ r then 0 else 1 := by
  classical
  by_cases hpr : p ∣ r
  · rw [if_pos hpr]
    calc
      (∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) =
          ∑' i : ℕ, reciprocalMoebiusAmplitude (p ^ i) := by
        apply tsum_congr
        intro i
        rw [localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd hp hpr]
      _ = 0 := tsum_reciprocalMoebiusAmplitude_prime_pow hp
  · rw [if_neg hpr]
    have hsum :=
      (summable_localizedReciprocalMoebiusAmplitude_prime_pow (r := r) hp).sum_add_tsum_nat_add 1
    have htail : (∑' i : ℕ,
        localizedReciprocalMoebiusAmplitude r (p ^ (i + 1))) = 0 := by
      rw [show (fun i : ℕ => localizedReciprocalMoebiusAmplitude r (p ^ (i + 1))) =
          fun _ => 0 by
        funext i
        exact localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hpr]
      exact tsum_zero
    rw [show ∑ i ∈ Finset.range 1,
        localizedReciprocalMoebiusAmplitude r (p ^ i) = 1 by simp, htail] at hsum
    linarith

theorem tsum_abs_localizedReciprocalMoebiusAmplitude_prime_pow
    {r p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, |localizedReciprocalMoebiusAmplitude r (p ^ i)|) =
      if p ∣ r then 2 else 1 := by
  classical
  by_cases hpr : p ∣ r
  · rw [if_pos hpr]
    calc
      (∑' i : ℕ, |localizedReciprocalMoebiusAmplitude r (p ^ i)|) =
          ∑' i : ℕ, |reciprocalMoebiusAmplitude (p ^ i)| := by
        apply tsum_congr
        intro i
        rw [localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd hp hpr]
      _ = 2 := tsum_abs_reciprocalMoebiusAmplitude_prime_pow hp
  · rw [if_neg hpr]
    have hsum :=
      (summable_abs_localizedReciprocalMoebiusAmplitude_prime_pow (r := r) hp).sum_add_tsum_nat_add 1
    have htail : (∑' i : ℕ,
        |localizedReciprocalMoebiusAmplitude r (p ^ (i + 1))|) = 0 := by
      rw [show (fun i : ℕ => |localizedReciprocalMoebiusAmplitude r (p ^ (i + 1))|) =
          fun _ => 0 by
        funext i
        simp [localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hpr]]
      exact tsum_zero
    rw [show ∑ i ∈ Finset.range 1,
        |localizedReciprocalMoebiusAmplitude r (p ^ i)| = 1 by simp, htail] at hsum
    linarith

private theorem hasSum_localizedReciprocalMoebiusAmplitude_euler
    {r : ℕ} (hr : 0 < r) :
    HasSum (fun n : ℕ => localizedReciprocalMoebiusAmplitude r n)
      (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) := by
  let S : Set ℕ := {n | n ∈ (r + 1).smoothNumbers}
  have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n : ℕ => localizedReciprocalMoebiusAmplitude r n)
    (localizedReciprocalMoebiusAmplitude_one r)
    (fun {_ _} h =>
      (isMultiplicative_localizedReciprocalMoebiusAmplitude r).map_mul_of_coprime h)
    (fun {_} hp => by
      simpa [Real.norm_eq_abs] using
        summable_abs_localizedReciprocalMoebiusAmplitude_prime_pow (r := r) hp)
    (r + 1)
  have hind : HasSum
      (S.indicator (fun n : ℕ => localizedReciprocalMoebiusAmplitude r n))
      (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) :=
    (hasSum_subtype_iff_indicator (s := S)
      (f := fun n : ℕ => localizedReciprocalMoebiusAmplitude r n)).mp heuler.2
  have hfun : S.indicator (fun n : ℕ => localizedReciprocalMoebiusAmplitude r n) =
      fun n : ℕ => localizedReciprocalMoebiusAmplitude r n := by
    funext n
    by_cases hn : n ∈ (r + 1).smoothNumbers
    · simp [S, hn]
    · simp [S, hn,
        localizedReciprocalMoebiusAmplitude_eq_zero_of_not_mem_smoothNumbers hr hn]
  rw [hfun] at hind
  exact hind

private theorem hasSum_abs_localizedReciprocalMoebiusAmplitude_euler
    {r : ℕ} (hr : 0 < r) :
    HasSum (fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|)
      (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, |localizedReciprocalMoebiusAmplitude r (p ^ i)|) := by
  let S : Set ℕ := {n | n ∈ (r + 1).smoothNumbers}
  have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|)
    (by simp)
    (fun {_ _} h => by
      rw [(isMultiplicative_localizedReciprocalMoebiusAmplitude r).map_mul_of_coprime h,
        abs_mul])
    (fun {_} hp => by
      simpa [Real.norm_eq_abs, abs_abs] using
        summable_abs_localizedReciprocalMoebiusAmplitude_prime_pow (r := r) hp)
    (r + 1)
  have hind : HasSum
      (S.indicator (fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|))
      (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, |localizedReciprocalMoebiusAmplitude r (p ^ i)|) :=
    (hasSum_subtype_iff_indicator (s := S)
      (f := fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|)).mp heuler.2
  have hfun : S.indicator (fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|) =
      fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n| := by
    funext n
    by_cases hn : n ∈ (r + 1).smoothNumbers
    · simp [S, hn]
    · simp [S, hn,
        localizedReciprocalMoebiusAmplitude_eq_zero_of_not_mem_smoothNumbers hr hn]
  rw [hfun] at hind
  exact hind

private theorem filter_primesBelow_dvd_eq_primeFactors {r : ℕ} (hr : 0 < r) :
    (r + 1).primesBelow.filter (fun p => p ∣ r) = r.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hplt, hp⟩, hpr⟩
    exact ⟨hp, hpr, hr.ne'⟩
  · rintro ⟨hp, hpr, -⟩
    exact ⟨⟨Nat.lt_succ_iff.mpr (Nat.le_of_dvd hr hpr), hp⟩, hpr⟩

/-- Exact absolute mass of the amplitude restricted to the primes dividing `r`. -/
theorem hasSum_abs_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    HasSum (fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|)
      ((2 : ℝ) ^ r.primeFactors.card) := by
  have h := hasSum_abs_localizedReciprocalMoebiusAmplitude_euler hr
  convert h using 1
  rw [show (∏ p ∈ (r + 1).primesBelow,
      ∑' i : ℕ, |localizedReciprocalMoebiusAmplitude r (p ^ i)|) =
      ∏ p ∈ (r + 1).primesBelow, if p ∣ r then 2 else 1 by
    apply Finset.prod_congr rfl
    intro p hp
    rw [tsum_abs_localizedReciprocalMoebiusAmplitude_prime_pow
      (Nat.mem_primesBelow.mp hp).2]]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
    filter_primesBelow_dvd_eq_primeFactors hr]

theorem summable_abs_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    Summable (fun n : ℕ => |localizedReciprocalMoebiusAmplitude r n|) :=
  (hasSum_abs_localizedReciprocalMoebiusAmplitude hr).summable

theorem summable_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    Summable (fun n : ℕ => localizedReciprocalMoebiusAmplitude r n) := by
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using summable_abs_localizedReciprocalMoebiusAmplitude hr

theorem tsum_abs_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    (∑' n : ℕ, |localizedReciprocalMoebiusAmplitude r n|) =
      (2 : ℝ) ^ r.primeFactors.card :=
  (hasSum_abs_localizedReciprocalMoebiusAmplitude hr).tsum_eq

/-- Signed localized amplitude has mass one only at the empty prime support. -/
theorem hasSum_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    HasSum (fun n : ℕ => localizedReciprocalMoebiusAmplitude r n)
      (if r = 1 then 1 else 0) := by
  have h := hasSum_localizedReciprocalMoebiusAmplitude_euler hr
  rw [show (∏ p ∈ (r + 1).primesBelow,
      ∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) =
      (if r = 1 then 1 else 0) by
    rw [show (∏ p ∈ (r + 1).primesBelow,
        ∑' i : ℕ, localizedReciprocalMoebiusAmplitude r (p ^ i)) =
        ∏ p ∈ (r + 1).primesBelow, if p ∣ r then 0 else 1 by
      apply Finset.prod_congr rfl
      intro p hp
      rw [tsum_localizedReciprocalMoebiusAmplitude_prime_pow
        (Nat.mem_primesBelow.mp hp).2]]
    by_cases hr1 : r = 1
    · subst r
      simp
    · rw [if_neg hr1]
      have hrgt : 1 < r := by omega
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hrgt.ne'
      apply Finset.prod_eq_zero (i := p)
      · exact Nat.mem_primesBelow.mpr
          ⟨Nat.lt_succ_iff.mpr (Nat.le_of_dvd hr hpr), hp⟩
      · simp [hpr]] at h
  exact h

theorem tsum_localizedReciprocalMoebiusAmplitude {r : ℕ} (hr : 0 < r) :
    (∑' n : ℕ, localizedReciprocalMoebiusAmplitude r n) =
      if r = 1 then 1 else 0 :=
  (hasSum_localizedReciprocalMoebiusAmplitude hr).tsum_eq

end

end RHTower.Sieve
