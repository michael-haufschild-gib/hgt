import GaloisForLFunctions.HTGeometry.RationalDenominatorLadder

/-!
# Frequencies realizing a divisibility ladder

Given a divisibility ladder `a` of positive integers, the frequencies `b k = a k · p k` with `p` a
rapidly growing sequence of primes have two properties at once: the gaps grow faster than any fixed
multiplier, and the set of integers dividing a whole tail of `b` is exactly the set of integers
dividing some `a K`.  The auxiliary prime is invisible to the tail-divisibility test because a
divisor of every `a k · p k` is coprime to `p k` as soon as `p k` exceeds it, and the primes are
strictly increasing.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

/-- **Ladder frequencies.**  Every divisibility ladder is the tail-divisibility spectrum of a
frequency sequence with eventually superlinear gaps. -/
theorem exists_ladderFrequencies {a : ℕ → ℕ} (hpos : ∀ K, 0 < a K)
    (hstep : ∀ K, a K ∣ a (K + 1)) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (∀ k, 0 < b k) ∧
      (∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1)) ∧
      ∀ d : ℕ, 0 < d → ((∃ K, d ∣ a K) ↔ ∃ N, ∀ k, N ≤ k → d ∣ b k) := by
  choose f hfle hfprime using Nat.exists_infinite_primes
  set p : ℕ → ℕ := fun k =>
    Nat.rec (f 2) (fun k pk => f (max (pk + 1) ((k + 2) * (a k * pk) + 1))) k with hp
  have hp0 : p 0 = f 2 := rfl
  have hpsucc : ∀ k, p (k + 1) = f (max (p k + 1) ((k + 2) * (a k * p k) + 1)) := fun _ => rfl
  have hpprime : ∀ k, (p k).Prime := by
    intro k
    cases k with
    | zero => rw [hp0]; exact hfprime 2
    | succ k => rw [hpsucc]; exact hfprime _
  have hpsucc_ge : ∀ k, max (p k + 1) ((k + 2) * (a k * p k) + 1) ≤ p (k + 1) := by
    intro k; rw [hpsucc]; exact hfle _
  have hpmono : StrictMono p := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have := hpsucc_ge k
    have : p k + 1 ≤ p (k + 1) := le_trans (le_max_left _ _) this
    omega
  set b : ℕ → ℕ := fun k => a k * p k with hb
  have hbpos : ∀ k, 0 < b k := fun k => Nat.mul_pos (hpos k) (hpprime k).pos
  have hbgap : ∀ k, (k + 2) * b k < b (k + 1) := by
    intro k
    have h1 : (k + 2) * (a k * p k) + 1 ≤ p (k + 1) :=
      le_trans (le_max_right _ _) (hpsucc_ge k)
    have h2 : p (k + 1) ≤ a (k + 1) * p (k + 1) :=
      Nat.le_mul_of_pos_left _ (hpos (k + 1))
    show (k + 2) * (a k * p k) < a (k + 1) * p (k + 1)
    omega
  have hbmono : StrictMono b := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 := hbgap k
    have h2 : b k ≤ (k + 2) * b k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine ⟨b, hbmono, hbpos, fun C => ?_, fun d hd => ⟨?_, ?_⟩⟩
  · filter_upwards [eventually_ge_atTop C] with k hk
    have h1 := hbgap k
    have h2 : C * b k ≤ (k + 2) * b k := Nat.mul_le_mul_right _ (by omega)
    omega
  · rintro ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    exact dvd_trans (dvd_trans hK (ladder_dvd_of_le hstep hk)) ⟨p k, rfl⟩
  · rintro ⟨N, hN⟩
    set k : ℕ := max N (d + 1) with hk
    have hkN : N ≤ k := le_max_left _ _
    have hkd : d + 1 ≤ k := le_max_right _ _
    have hpk : d < p k := lt_of_lt_of_le (by omega) (le_trans hkd hpmono.le_apply)
    have hcop : Nat.Coprime d (p k) := by
      refine (Nat.Prime.coprime_iff_not_dvd (hpprime k)).2 ?_ |>.symm
      intro hdvd
      exact absurd (Nat.le_of_dvd hd hdvd) (by omega)
    exact ⟨k, hcop.dvd_of_dvd_mul_right (hN k hkN)⟩

end GaloisForLFunctions.HTGeometry
