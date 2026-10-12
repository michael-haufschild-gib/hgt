import GaloisForLFunctions.RHTower.PaperLagCayleySource
import GaloisForLFunctions.HTGeometry.PaperRecurrentDiagonal

/-! # Every arithmetic phase recurs in the actual lag curvature

Fixed prime powers retain their individual prime phase. Integers divisible by
both two and three retain the non-prime-power phase. These channels escape every
finite coordinate set and determine the full recurrent arithmetic model.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHTower.PaperLagCayley

open GaloisForLFunctions.HTGeometry

def basePhase : Circle := circleCayley (-1)

def primePhase (p : Nat.Primes) : Circle := circleCayley (Real.log p - 1)

theorem basePhase_coe : (basePhase : ℂ) = Complex.I := paperRealCayley_neg_one

def primeIndex (p : Nat.Primes) (k : ℕ) : ℕ := (p : ℕ) ^ (k + 2) - 3

theorem prime_pow_ge_three (p : Nat.Primes) (k : ℕ) : 3 ≤ (p : ℕ) ^ (k + 2) := by
  have hp := p.property.two_le
  have hpow := pow_le_pow_right₀ (show 1 ≤ (p : ℕ) by omega) (show 2 ≤ k + 2 by omega)
  have hsq : 4 ≤ (p : ℕ) ^ 2 := by nlinarith
  omega

theorem arithmetic_primeIndex (p : Nat.Primes) (k : ℕ) :
    arithmetic (primeIndex p k) = Real.log p - 1 := by
  rw [arithmetic, primeIndex, Nat.sub_add_cancel (prime_pow_ge_three p k),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime p.property]

theorem arithmeticPhase_primeIndex (p : Nat.Primes) (k : ℕ) :
    arithmeticPhase (primeIndex p k) = primePhase p := by
  rw [arithmeticPhase, arithmetic_primeIndex]
  rfl

theorem tendsto_primeIndex (p : Nat.Primes) : Tendsto (primeIndex p) atTop atTop :=
  (tendsto_sub_atTop_nat 3).comp
    ((tendsto_pow_atTop_atTop_of_one_lt p.property.one_lt).comp (tendsto_add_atTop_nat 2))

def compositeIndex (k : ℕ) : ℕ := 6 * (k + 1) - 3

theorem composite_not_primePow (k : ℕ) : ¬ IsPrimePow (6 * (k + 1)) := by
  intro h
  obtain ⟨p, r, hp, _, he⟩ := (isPrimePow_nat_iff _).1 h
  have h2 : 2 ∣ p ^ r := by rw [he]; exact ⟨3 * (k + 1), by ring⟩
  have h3 : 3 ∣ p ^ r := by rw [he]; exact ⟨2 * (k + 1), by ring⟩
  have hp2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow h2)
  have hp3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem arithmetic_compositeIndex (k : ℕ) : arithmetic (compositeIndex k) = -1 := by
  rw [arithmetic, compositeIndex, Nat.sub_add_cancel (by omega : 3 ≤ 6 * (k + 1)),
    ArithmeticFunction.vonMangoldt_apply, if_neg (composite_not_primePow k), zero_sub]

theorem arithmeticPhase_compositeIndex (k : ℕ) :
    arithmeticPhase (compositeIndex k) = basePhase := by
  rw [arithmeticPhase, arithmetic_compositeIndex]
  rfl

theorem tendsto_compositeIndex : Tendsto compositeIndex atTop atTop :=
  tendsto_atTop_mono (fun k => by dsimp [compositeIndex]; omega) tendsto_id

theorem arithmeticPhase_cases (n : ℕ) :
    arithmeticPhase n = basePhase ∨ ∃ p : Nat.Primes, arithmeticPhase n = primePhase p := by
  by_cases hp : IsPrimePow (n + 3)
  · right
    refine ⟨⟨(n + 3).minFac, Nat.minFac_prime (by omega)⟩, ?_⟩
    simp only [arithmeticPhase, arithmetic, ArithmeticFunction.vonMangoldt_apply, if_pos hp]
    rfl
  · left
    simp only [arithmeticPhase, arithmetic, ArithmeticFunction.vonMangoldt_apply, if_neg hp,
      zero_sub, basePhase]

theorem primePhase_coe_injective : Function.Injective (fun p : Nat.Primes => (primePhase p : ℂ)) := by
  intro p q h
  have he := injective_realCayley h
  have hlog : Real.log (p : ℝ) = Real.log (q : ℝ) := by
    change Real.log (p : ℝ) - 1 = Real.log (q : ℝ) - 1 at he
    linarith
  apply Subtype.ext
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : 0 < (q : ℝ) := by exact_mod_cast q.property.pos
  exact_mod_cast Real.log_injOn_pos hp hq hlog

theorem infinite_prime_phases : (Set.range fun p : Nat.Primes => (primePhase p : ℂ)).Infinite :=
  Set.infinite_range_of_injective primePhase_coe_injective

theorem recurrent_arithmetic_observable (f : C(Circle, ℂ)) :
    PaperDiagonalRecurrent (fun n => f (arithmeticPhase n)) := by
  intro n
  rcases arithmeticPhase_cases n with h | ⟨p, h⟩
  · refine ⟨compositeIndex, tendsto_compositeIndex, fun k => ?_⟩
    change f (arithmeticPhase (compositeIndex k)) = f (arithmeticPhase n)
    rw [arithmeticPhase_compositeIndex, h]
  · refine ⟨primeIndex p, tendsto_primeIndex p, fun k => ?_⟩
    change f (arithmeticPhase (primeIndex p k)) = f (arithmeticPhase n)
    rw [arithmeticPhase_primeIndex, h]

theorem tendsto_phase_prime (p : Nat.Primes) :
    Tendsto (fun k => (phase (primeIndex p k) : ℂ)) atTop (𝓝 (primePhase p : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := phase_discrepancy_tendsto.comp (tendsto_primeIndex p)
  change Tendsto (fun k => ‖(phase (primeIndex p k) : ℂ) - arithmeticPhase (primeIndex p k)‖)
    atTop (𝓝 0) at h
  simpa only [arithmeticPhase_primeIndex] using h

theorem tendsto_phase_composite :
    Tendsto (fun k => (phase (compositeIndex k) : ℂ)) atTop (𝓝 (basePhase : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := phase_discrepancy_tendsto.comp tendsto_compositeIndex
  change Tendsto (fun k => ‖(phase (compositeIndex k) : ℂ) - arithmeticPhase (compositeIndex k)‖)
    atTop (𝓝 0) at h
  simpa only [arithmeticPhase_compositeIndex] using h

def escapingPrime (k : ℕ) : Nat.Primes :=
  ⟨Classical.choose (Nat.exists_infinite_primes (k + 3)),
    (Classical.choose_spec (Nat.exists_infinite_primes (k + 3))).2⟩

theorem escapingPrime_ge (k : ℕ) : k + 3 ≤ (escapingPrime k : ℕ) :=
  (Classical.choose_spec (Nat.exists_infinite_primes (k + 3))).1

theorem tendsto_escapingPrime : Tendsto (fun k => (escapingPrime k : ℕ)) atTop atTop :=
  tendsto_atTop_mono (fun k => (Nat.le_add_right k 3).trans (escapingPrime_ge k)) tendsto_id

theorem tendsto_primePhase_one :
    Tendsto (fun k => primePhase (escapingPrime k)) atTop (𝓝 (1 : Circle)) := by
  have hp : Tendsto (fun k => (escapingPrime k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_escapingPrime
  have hlog := Real.tendsto_log_atTop.comp hp
  have hx : Tendsto (fun k => Real.log (escapingPrime k : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop (b + 1))] with k hk
    dsimp at hk
    linarith
  apply tendsto_subtype_rng.2
  exact paperRealCayley_tendsto_one.comp hx

theorem observable_one_eq_zero (f : C(Circle, ℂ))
    (h : ∀ p : Nat.Primes, f (primePhase p) = 0) : f 1 = 0 := by
  have hf := f.continuous.continuousAt.tendsto.comp tendsto_primePhase_one
  have hzero : Tendsto (fun k => f (primePhase (escapingPrime k))) atTop (𝓝 (0 : ℂ)) := by
    simpa only [h] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hf hzero

end RHTower.PaperLagCayley
