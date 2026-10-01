import GaloisForLFunctions.RHTower.SteinhausFrozenCarrierLocalTarget
import GaloisForLFunctions.RHTower.SteinhausSmoothCarrierProjection



open MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Retain all primes through the polynomial cutoff except the free window (Y,N]. -/
def steinhausWindowRetainedPrimes (L N Y : ℕ) : Finset ℕ :=
  Nat.primesLE L \ largePrimes N Y

/-- A longer polynomial still has an exact affine law in the primes of a bounded free window.
The background is the literal projection onto all retained primes, including those above N. -/
theorem steinhausCarrier_freeze_window_eq_smooth_add_circleChannels
    (a : ℕ → ℂ) (L N Y : ℕ) (hYN : Y ≤ N) (hNL : N ≤ L) (hLY : L < Y * Y)
    (ω η : Omega) :
    (∑ n ∈ Icc 1 L, a n * X n (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω η)) =
      (∑ n ∈ Sieve.smoothUpTo (steinhausWindowRetainedPrimes L N Y) L, a n * X n ω) +
        ∑ p ∈ largePrimes N Y, charFactor 1 (η p) * steinhausLargePrimeChannel a L p ω := by
  classical
  let S := steinhausWindowRetainedPrimes L N Y
  let P := largePrimes N Y
  let Q := largePrimes L Y
  have hPQ : P ⊆ Q := by
    intro p hp
    obtain ⟨⟨hpN, hpp⟩, hpY⟩ := mem_largePrimes.mp hp
    exact mem_largePrimes.mpr ⟨⟨hpN.trans hNL, hpp⟩, hpY⟩
  have hsmall (ζ : Omega) (q : ℕ) (hq : q ∈ Nat.primesLE Y) :
      freezeSteinhausPrefix S ω ζ q = ω q := by
    have hqS : q ∈ S := by
      apply mem_sdiff.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hq).1.trans (hYN.trans hNL),
        (Nat.mem_primesLE.mp hq).2⟩, ?_⟩
      intro hqP
      exact not_lt_of_ge (Nat.mem_primesLE.mp hq).1 (mem_largePrimes.mp hqP).2
    simp only [freezeSteinhausPrefix, if_pos hqS]
  let B : ℂ := steinhausSmoothCarrier a L Y ω +
    ∑ p ∈ Q \ P, X p ω * steinhausLargePrimeChannel a L p ω
  have hsplit (ζ : Omega) :
      (∑ n ∈ Icc 1 L, a n * X n (freezeSteinhausPrefix S ω ζ)) =
        B + ∑ p ∈ P, X p ζ * steinhausLargePrimeChannel a L p ω := by
    rw [steinhausCarrier_eq_smooth_add_largePrimeChannels a L Y _ hLY,
      steinhausSmoothCarrier_congr_of_eqOn_smallPrimes a L Y (hsmall ζ)]
    have hchannels : (∑ p ∈ Q, X p (freezeSteinhausPrefix S ω ζ) *
        steinhausLargePrimeChannel a L p (freezeSteinhausPrefix S ω ζ)) =
        ∑ p ∈ Q, X p (freezeSteinhausPrefix S ω ζ) * steinhausLargePrimeChannel a L p ω := by
      apply sum_congr rfl
      intro p hp
      rw [steinhausLargePrimeChannel_congr_of_eqOn_smallPrimes a hLY hp (hsmall ζ)]
    rw [hchannels, ← sum_sdiff hPQ]
    have hretained : (∑ p ∈ Q \ P, X p (freezeSteinhausPrefix S ω ζ) *
        steinhausLargePrimeChannel a L p ω) = ∑ p ∈ Q \ P, X p ω * steinhausLargePrimeChannel a L p ω := by
      apply sum_congr rfl
      intro p hp
      have hpQ := (mem_sdiff.mp hp).1
      have hpP := (mem_sdiff.mp hp).2
      have hpp := (mem_largePrimes.mp hpQ).1.2
      have hpS : p ∈ S := mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr (mem_largePrimes.mp hpQ).1, hpP⟩
      rw [steinhausCharacter_prime_eq_charFactor hpp, steinhausCharacter_prime_eq_charFactor hpp]
      simp only [freezeSteinhausPrefix, if_pos hpS]
    have hfree : (∑ p ∈ P, X p (freezeSteinhausPrefix S ω ζ) *
        steinhausLargePrimeChannel a L p ω) = ∑ p ∈ P, X p ζ * steinhausLargePrimeChannel a L p ω := by
      apply sum_congr rfl
      intro p hp
      have hpp := (mem_largePrimes.mp hp).1.2
      have hpS : p ∉ S := fun hpS => (mem_sdiff.mp hpS).2 hp
      rw [steinhausCharacter_prime_eq_charFactor hpp, steinhausCharacter_prime_eq_charFactor hpp]
      simp only [freezeSteinhausPrefix, if_neg hpS]
    rw [hretained, hfree]
    exact (add_assoc _ _ _).symm
  have hi (p : ℕ) : Integrable (fun ζ => X p ζ * steinhausLargePrimeChannel a L p ω)
      steinhausMeasure := by
    have h := integrable_X_mul_conj p 1
    simp only [X_one, map_one, mul_one] at h
    exact h.mul_const _
  have hzero (p : ℕ) (hp : p ∈ P) : (∫ ζ, X p ζ ∂steinhausMeasure) = 0 := by
    have hpp := (mem_largePrimes.mp hp).1.2
    simpa only [X_one, map_one, mul_one, if_neg hpp.ne_one] using
      (integral_X_mul_conj hpp.ne_zero (one_ne_zero : (1 : ℕ) ≠ 0))
  have hbackground : B = ∑ n ∈ Sieve.smoothUpTo S L, a n * X n ω := by
    have h := integral_frozenPrefix_carrier_eq_smooth a L S ω
    have heq : (fun ζ => ∑ n ∈ Icc 1 L, a n * X n (freezeSteinhausPrefix S ω ζ)) =
        (fun ζ => B + ∑ p ∈ P, X p ζ * steinhausLargePrimeChannel a L p ω) := funext hsplit
    rw [heq, integral_add (integrable_const _) (integrable_finsetSum _ (fun p _ => hi p)),
      integral_finsetSum _ (fun p _ => hi p)] at h
    simp_rw [integral_mul_const] at h
    have hz : (∑ p ∈ P, (∫ ζ, X p ζ ∂steinhausMeasure) * steinhausLargePrimeChannel a L p ω) = 0 := by
      apply sum_eq_zero
      intro p hp
      rw [hzero p hp, zero_mul]
    rw [hz, add_zero] at h
    simpa using h
  change (∑ n ∈ Icc 1 L, a n * X n (freezeSteinhausPrefix S ω η)) = _
  rw [hsplit, hbackground]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [steinhausCharacter_prime_eq_charFactor (mem_largePrimes.mp hp).1.2]

end RHTower
