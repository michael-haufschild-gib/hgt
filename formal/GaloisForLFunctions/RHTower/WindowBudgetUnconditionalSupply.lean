import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.PrimeWindowSupply

/-!
# Unconditional discharge of the window supply at every length

`WindowBudget` steers the defect walk with primes whose log lies in prescribed sine windows,
against the interface Prop `PrimeWindowSupply L`; until now only lengths `L > log 2` were
discharged (Bertrand).  The corpus's own elementary prime number theorem supplies a prime in
EVERY multiplicative window of positive logarithmic length past an explicit threshold
(`exists_prime_log_window`), so the interface holds at every `L > 0`.  Consequences: the sine
steering wheel `sin (τ·log q)` reaches both signs with the uniform floor `√2/2` at EVERY
frequency `τ > 0` — not only below `π/(2·log 2)` — and the mirror-tilt defect walk has strictly
positive and strictly negative steps beyond any bound at every interior point of the strip.
This closes the frequency restriction of the corpus's Diophantine window tuning: a fixed target
frequency, however large, has cofinal prime supply in every quarter-period phase window.
-/

namespace RHTower

/-- **Unconditional window supply at every positive length.**  The interface Prop of
`WindowBudget` holds for every `L > 0`: past a threshold, every logarithmic window of length
`L` contains a prime.  Bertrand's restriction `L > log 2` is removed by the elementary prime
number theorem. -/
theorem primeWindowSupply_of_pos {L : ℝ} (hL : 0 < L) : PrimeWindowSupply L := by
  obtain ⟨R₀, hR₀⟩ := exists_prime_log_window (show (0 : ℝ) < L / 3 by linarith)
  refine ⟨R₀, fun b hb => ?_⟩
  obtain ⟨p, hp, h1, h2⟩ := hR₀ (b + L / 3) (by linarith)
  exact ⟨p, hp, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩

/-- **Unconditional positive sine steering at every frequency**: for every `τ > 0` there are
arbitrarily large primes `q` with `sin (τ·log q) ≥ √2/2`. -/
theorem exists_prime_sin_pos_unconditional {τ : ℝ} (hτ : 0 < τ) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      Real.sqrt 2 / 2 ≤ Real.sin (τ * Real.log q) :=
  exists_prime_sin_pos_of_supply hτ (primeWindowSupply_of_pos (by positivity)) Q

/-- **Unconditional negative sine steering at every frequency**: for every `τ > 0` there are
arbitrarily large primes `q` with `sin (τ·log q) ≤ -√2/2`. -/
theorem exists_prime_sin_neg_unconditional {τ : ℝ} (hτ : 0 < τ) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      Real.sin (τ * Real.log q) ≤ -(Real.sqrt 2 / 2) :=
  exists_prime_sin_neg_of_supply hτ (primeWindowSupply_of_pos (by positivity)) Q

/-- **The unconditional steering wheel at every height**: at every interior strip point the
mirror-tilt defect walk has strictly positive steps at arbitrarily large prime scales. -/
theorem exists_prime_mirrorTiltIncrement_pos_unconditional {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hτ : 0 < s.im) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧ 0 < mirrorTiltIncrement q s :=
  exists_prime_mirrorTiltIncrement_pos_of_supply h0 h1 hτ
    (primeWindowSupply_of_pos (by positivity)) Q

/-- **The unconditional reverse steering wheel at every height.** -/
theorem exists_prime_mirrorTiltIncrement_neg_unconditional {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hτ : 0 < s.im) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧ mirrorTiltIncrement q s < 0 :=
  exists_prime_mirrorTiltIncrement_neg_of_supply h0 h1 hτ
    (primeWindowSupply_of_pos (by positivity)) Q

end RHTower
