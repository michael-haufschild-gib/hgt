import GaloisForLFunctions.RHTower.DeningerRootFactor
import GaloisForLFunctions.RHTower.DeningerRootIndex

/-!
# A root adjunction is never isolated

In an infinite cyclic group the subgroup of `m`-th powers is not isolated for `|m| ≥ 2`: the
generator has its `|m|`-th power inside it while lying outside.  So the base group of a root
adjunction is never isolated in its infinite cyclic factor, and the criterion for unique roots over
an isolated base group does not apply to a root adjunction.

* `deningerZpow_not_isolated` : the failure of isolation.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The `m`-th powers of an infinite cyclic group are not isolated for `|m| ≥ 2`.** -/
theorem deningerZpow_not_isolated (m : ℤ) (hm : 2 ≤ m.natAbs) :
    ∃ (x : Multiplicative ℤ) (n : ℕ), 0 < n ∧
      x ^ n ∈ ((zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)).range ∧
      x ∉ ((zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)).range := by
  refine ⟨Multiplicative.ofAdd (1 : ℤ), m.natAbs, by omega, ?_, ?_⟩
  · rw [deningerZpowRange]
    refine ⟨if 0 ≤ m then 1 else -1, ?_⟩
    have h : Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ m.natAbs) =
        (m.natAbs : ℤ) := by simp
    show _ = Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ m.natAbs)
    rw [h]
    rcases le_or_gt 0 m with hpos | hneg
    · rw [if_pos hpos]
      simp only [one_smul]
      omega
    · rw [if_neg (by omega)]
      simp only [neg_smul, one_smul]
      omega
  · rw [deningerZpowRange]
    rintro ⟨c, hc⟩
    have h1 : (1 : ℤ) = c * m := by
      have h2 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = c • m := hc.symm
      simpa using h2
    have hdvd : m ∣ 1 := ⟨c, by rw [h1, mul_comm]⟩
    rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hdvd) with h | h <;> omega

end RootAdjunction

end RHTower
