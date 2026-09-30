import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity

/-!
# Removing primes destroys Weil positivity

For a set `R` of primes, let `Λ_R(n) = Λ(n)` unless `n` is a power of a prime in `R`, and
`Λ_R(n) = 0` otherwise: the von Mangoldt function of `ζ(s) ∏_{p ∈ R}(1 - p^{-s})`.  Removing finitely
many Euler factors does not move the zeros of `ζ` in the critical strip (the new zeros lie on
`Re s = 0`), but it destroys Weil positivity for the archimedean datum of `ζ`, unconditionally:
`Λ_R ≤ Λ`, and a full-cone Weil-positive minorant of `Λ` equals `Λ`
(`eq_vonMangoldt_of_weilPositiveFull_of_le`).
-/

namespace RHTower
namespace RemovedPrimes

open ArithmeticFunction

/-- The von Mangoldt function with the powers of the primes in `R` removed. -/
noncomputable def vonMangoldtWithout (R : Set ℕ) (n : ℕ) : ℝ :=
  Set.indicator {m | ¬ ∃ p ∈ R, ∃ k, m = p ^ k} (fun m => (vonMangoldt m : ℝ)) n

theorem vonMangoldtWithout_le (R : Set ℕ) (n : ℕ) :
    vonMangoldtWithout R n ≤ (vonMangoldt n : ℝ) :=
  Set.indicator_le_self' (fun _ _ => vonMangoldt_nonneg) n

/-- **Removing any prime destroys Weil positivity.**  If `R` contains a prime, then the von Mangoldt
function with the powers of the primes of `R` removed is not full-cone Weil-positive. -/
theorem not_weilPositiveFull_vonMangoldtWithout {R : Set ℕ} {p : ℕ} (hp : p.Prime) (hpR : p ∈ R) :
    ¬ WeilPositiveFull (vonMangoldtWithout R) := by
  intro hW
  have h := eq_vonMangoldt_of_weilPositiveFull_of_le hW fun n _ => vonMangoldtWithout_le R n
  have hp2 := h p hp.two_le
  have hmem : p ∉ {m : ℕ | ¬ ∃ q ∈ R, ∃ k, m = q ^ k} := by
    simp only [Set.mem_setOf_eq, not_not]
    exact ⟨p, hpR, 1, (pow_one p).symm⟩
  have h0 : vonMangoldtWithout R p = 0 := Set.indicator_of_notMem hmem _
  rw [h0, vonMangoldt_apply_prime hp] at hp2
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' hp2.symm

/-- In particular, the von Mangoldt function of `(1 - 2^{-s}) ζ(s)` (the prime `2` removed) is not
full-cone Weil-positive. -/
theorem not_weilPositiveFull_without_two :
    ¬ WeilPositiveFull (vonMangoldtWithout {2}) :=
  not_weilPositiveFull_vonMangoldtWithout Nat.prime_two rfl

end RemovedPrimes
end RHTower
