import GaloisForLFunctions.RHTower.MobiusFriableLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.RouteBFullSupport
import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment

/-!
# Largest-prime decomposition of a Steinhaus carrier

When `X < Y²`, every non-`Y`-smooth integer `n ≤ X` has a unique factorisation
`n = p * m` with `p > Y` prime and `m ≤ X / p < Y`.  Applying this arithmetic
bijection to arbitrary complex coefficients gives an exact decomposition of a
Steinhaus carrier into a smooth background and linear large-prime phase channels.

The channel multiplying `X p` reads only phase coordinates at primes at most `Y`.
This is the deterministic interface needed before a conditional local-limit or
small-ball theorem can be applied to the independent large-prime coordinates.
-/

namespace RHTower

open Finset Nat
open SteinhausModel

/-- The arithmetic largest-prime bijection, with arbitrary additive weights. -/
theorem sum_Icc_eq_smooth_add_largePrimeSigma
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (X Y : ℕ) (hXY : X < Y * Y) :
    ∑ n ∈ Finset.Icc 1 X, f n =
      ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, f n +
        ∑ x ∈ (largePrimes X Y).sigma (fun p => Finset.Icc 1 (X / p)), f (x.1 * x.2) := by
  classical
  have hAfilter : Sieve.smoothUpTo (Nat.primesLE Y) X =
      {n ∈ Finset.Icc 1 X | ∀ p ∈ n.primeFactors, p ≤ Y} := by
    ext n
    rw [mem_smoothUpTo_iff, Finset.mem_filter, Finset.mem_Icc]
  set B : Finset ℕ := {n ∈ Finset.Icc 1 X | ¬ ∀ p ∈ n.primeFactors, p ≤ Y} with hB
  have hsplit : ∑ n ∈ Finset.Icc 1 X, f n =
      ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, f n + ∑ n ∈ B, f n := by
    rw [hAfilter, hB]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  set S : Finset ((_ : ℕ) × ℕ) :=
    (largePrimes X Y).sigma (fun p => Finset.Icc 1 (X / p)) with hS
  have hkey : ∑ n ∈ B, f n = ∑ x ∈ S, f (x.1 * x.2) := by
    refine (Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_).symm
    · rintro ⟨p, m⟩ hx
      simp only [hS, Finset.mem_sigma] at hx
      obtain ⟨hp, hm⟩ := hx
      obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
      obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.1 hm
      have hle : p * m ≤ X := by
        calc
          p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmle
          _ ≤ X := Nat.mul_div_le X p
      have hpos : 1 ≤ p * m :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hpprime.pos.ne' (by omega))
      have hpmem : p ∈ (p * m).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpprime, Dvd.intro m rfl, by omega⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, hle⟩, ?_⟩
      intro hcon
      exact absurd (hcon p hpmem) (by omega)
    · rintro ⟨p, m⟩ hx ⟨p', m'⟩ hy hxy
      simp only [hS, Finset.mem_sigma] at hx hy
      obtain ⟨hp, hm⟩ := hx
      obtain ⟨hp', hm'⟩ := hy
      obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
      obtain ⟨⟨hpX', hpprime'⟩, hpY'⟩ := mem_largePrimes.1 hp'
      obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.1 hm
      obtain ⟨hm1', hmle'⟩ := Finset.mem_Icc.1 hm'
      have hle : p * m ≤ X := by
        calc
          p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmle
          _ ≤ X := Nat.mul_div_le X p
      have hn0 : p * m ≠ 0 := Nat.mul_ne_zero hpprime.pos.ne' (by omega)
      have hpmem : p ∈ (p * m).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpprime, Dvd.intro m rfl, hn0⟩
      have hp'mem : p' ∈ (p * m).primeFactors := by
        rw [hxy]
        exact Nat.mem_primeFactors.2
          ⟨hpprime', Dvd.intro m' rfl, by rw [← hxy]; exact hn0⟩
      have hpp : p = p' := eq_of_two_large_primes hle hXY hpmem hp'mem hpY hpY'
      subst hpp
      have hmm : m = m' := Nat.eq_of_mul_eq_mul_left hpprime.pos hxy
      subst hmm
      rfl
    · intro n hn
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.1 hn
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.1 hmem
      obtain ⟨p, hp, hpY⟩ : ∃ p ∈ n.primeFactors, Y < p := by
        by_contra hcon
        exact hnot (fun p hp => not_lt.1 (fun h => hcon ⟨p, hp, h⟩))
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
      refine ⟨⟨p, n / p⟩, ?_, hmul⟩
      simp only [hS, Finset.mem_sigma]
      refine ⟨mem_largePrimes.2 ⟨⟨by omega, hpprime⟩, hpY⟩,
        Finset.mem_Icc.2 ⟨?_, Nat.div_le_div_right hnX⟩⟩
      exact Nat.div_pos hpn hpprime.pos
    · rintro ⟨p, m⟩ hx
      rfl
  rw [hsplit, hkey, hS]

/-- The `Y`-smooth background of a finite Steinhaus carrier. -/
noncomputable def steinhausSmoothCarrier (a : ℕ → ℂ) (X Y : ℕ) (omega : Omega) : ℂ :=
  ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, a n * SteinhausModel.X n omega

/-- Coefficient of the large-prime phase `X p` after the exact decomposition. -/
noncomputable def steinhausLargePrimeChannel (a : ℕ → ℂ) (X p : ℕ) (omega : Omega) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (X / p), a (p * m) * SteinhausModel.X m omega

/-- The smooth background reads only phase coordinates at primes at most `Y`. -/
theorem steinhausSmoothCarrier_congr_of_eqOn_smallPrimes
    (a : ℕ → ℂ) (X Y : ℕ) {omega omega' : Omega}
    (hphase : ∀ q ∈ Nat.primesLE Y, omega q = omega' q) :
    steinhausSmoothCarrier a X Y omega = steinhausSmoothCarrier a X Y omega' := by
  classical
  unfold steinhausSmoothCarrier
  refine Finset.sum_congr rfl (fun n hn => ?_)
  congr 1
  apply X_congr_of_eqOn_primeFactors
  intro q hq
  apply hphase q
  rw [Nat.mem_primesLE]
  exact ⟨(mem_smoothUpTo_iff.1 hn).2 q hq, Nat.prime_of_mem_primeFactors hq⟩

/-- A phase indexing a large-prime channel is outside the small-prime conditioning set. -/
theorem largePrime_not_mem_primesLE {X Y p : ℕ} (hp : p ∈ largePrimes X Y) :
    p ∉ Nat.primesLE Y := by
  intro hsmall
  have hpY := (mem_largePrimes.1 hp).2
  have hpLeY := (Nat.mem_primesLE.1 hsmall).1
  omega

/-- **Exact conditional-channel decomposition.** Below the first seam, every arbitrary-coefficient
Steinhaus carrier is a smooth background plus a linear sum in the large-prime phases. -/
theorem steinhausCarrier_eq_smooth_add_largePrimeChannels
    (a : ℕ → ℂ) (X Y : ℕ) (omega : Omega) (hXY : X < Y * Y) :
    ∑ n ∈ Finset.Icc 1 X, a n * SteinhausModel.X n omega =
      steinhausSmoothCarrier a X Y omega +
        ∑ p ∈ largePrimes X Y,
          SteinhausModel.X p omega * steinhausLargePrimeChannel a X p omega := by
  classical
  rw [sum_Icc_eq_smooth_add_largePrimeSigma
    (fun n => a n * SteinhausModel.X n omega) X Y hXY]
  unfold steinhausSmoothCarrier steinhausLargePrimeChannel
  rw [Finset.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
  obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.1 hm
  rw [SteinhausModel.X_mul hpprime.ne_zero (Nat.one_le_iff_ne_zero.mp hm1)]
  ring

/-- Every cofactor in a large-prime channel is strictly below the phase cut. -/
theorem steinhausLargePrimeChannel_cofactor_lt
    {X Y p m : ℕ} (hXY : X < Y * Y) (hp : p ∈ largePrimes X Y)
    (hm : m ∈ Finset.Icc 1 (X / p)) :
    m < Y := by
  exact lt_of_le_of_lt (Finset.mem_Icc.1 hm).2 (div_lt_of_mem_largePrimes hXY hp)

/-- A large-prime channel coefficient reads only coordinates at primes at most `Y`. -/
theorem steinhausLargePrimeChannel_congr_of_eqOn_smallPrimes
    (a : ℕ → ℂ) {X Y p : ℕ} {omega omega' : Omega}
    (hXY : X < Y * Y) (hp : p ∈ largePrimes X Y)
    (hphase : ∀ q ∈ Nat.primesLE Y, omega q = omega' q) :
    steinhausLargePrimeChannel a X p omega =
      steinhausLargePrimeChannel a X p omega' := by
  classical
  unfold steinhausLargePrimeChannel
  refine Finset.sum_congr rfl (fun m hm => ?_)
  congr 1
  apply X_congr_of_eqOn_primeFactors
  intro q hq
  apply hphase q
  rw [Nat.mem_primesLE]
  refine ⟨?_, Nat.prime_of_mem_primeFactors hq⟩
  have hqm : q ≤ m :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 hm).1)
      (Nat.dvd_of_mem_primeFactors hq)
  exact le_trans hqm (Nat.le_of_lt (steinhausLargePrimeChannel_cofactor_lt hXY hp hm))

/-- Exact mean-square energy of one conditional large-prime channel. -/
theorem integral_normSq_steinhausLargePrimeChannel
    (a : ℕ → ℂ) (X p : ℕ) :
    ∫ omega, ‖steinhausLargePrimeChannel a X p omega‖ ^ (2 : ℕ)
        ∂SteinhausModel.steinhausMeasure =
      ∑ m ∈ Finset.Icc 1 (X / p), ‖a (p * m)‖ ^ (2 : ℕ) := by
  unfold steinhausLargePrimeChannel
  exact SteinhausModel.integral_normSq_dpoly_complex
    (fun m => a (p * m)) (Finset.Icc 1 (X / p))
    (fun m hm => Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.1 hm).1)

/-- **Exact channel-energy partition.** The expected squared energies of all conditional
large-prime channels are precisely the arbitrary coefficient mass in the non-smooth sector. -/
theorem steinhausCoefficientMass_eq_smooth_add_largePrimeChannelEnergy
    (a : ℕ → ℂ) (X Y : ℕ) (hXY : X < Y * Y) :
    ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ (2 : ℕ) =
      ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, ‖a n‖ ^ (2 : ℕ) +
        ∑ p ∈ largePrimes X Y,
          ∫ omega, ‖steinhausLargePrimeChannel a X p omega‖ ^ (2 : ℕ)
            ∂SteinhausModel.steinhausMeasure := by
  classical
  calc
    ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ (2 : ℕ) =
        ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, ‖a n‖ ^ (2 : ℕ) +
          ∑ x ∈ (largePrimes X Y).sigma (fun p => Finset.Icc 1 (X / p)),
            ‖a (x.1 * x.2)‖ ^ (2 : ℕ) :=
      sum_Icc_eq_smooth_add_largePrimeSigma (fun n => ‖a n‖ ^ (2 : ℕ)) X Y hXY
    _ = ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, ‖a n‖ ^ (2 : ℕ) +
        ∑ p ∈ largePrimes X Y,
          ∫ omega, ‖steinhausLargePrimeChannel a X p omega‖ ^ (2 : ℕ)
            ∂SteinhausModel.steinhausMeasure := by
      rw [Finset.sum_sigma]
      congr 1
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [integral_normSq_steinhausLargePrimeChannel]

end RHTower
