import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# A root of an element of valuation one has trivial order

If `z ^ k = c` and `c` has valuation one, then `k = 1`: the valuation of `z` would otherwise be a
proper fraction of one in a value group of integers.

```text
eq_one_of_pow_eq_of_addVal_eq_one          for a discrete valuation ring
eq_one_of_pow_eq_of_addValuation_eq_one    for an integer-valued valuation on a field
```

This is the last step of a Kummer-descent argument: an intermediate field of a cyclic extension
`O(c^{1/L})/O` is `O(c^{1/k})` for some `k ∣ L`, and a marked divisor on which `c` has order one
forces `k = 1`, so the intermediate field is trivial.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing


/-- **A `k`-th root of an element of valuation one forces `k = 1`.** -/
theorem eq_one_of_pow_eq_of_addVal_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {z c : R} {k : ℕ}
    (hzk : z ^ k = c) (hc : addVal R c = 1) : k = 1 := by
  have hpow : addVal R c = k • addVal R z := by
    rw [← hzk]
    exact addVal_pow z k
  rw [hc, nsmul_eq_mul] at hpow
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hpow
  rcases eq_or_ne (addVal R z) 0 with h0 | h0
  · rw [h0, mul_zero] at hpow
    simp at hpow
  · have h1 : (1 : ℕ∞) ≤ addVal R z := Order.one_le_iff_ne_zero.mpr h0
    have hkle : (k : ℕ∞) ≤ (k : ℕ∞) * addVal R z := by
      calc (k : ℕ∞) = (k : ℕ∞) * 1 := (mul_one _).symm
        _ ≤ (k : ℕ∞) * addVal R z := by gcongr
    rw [← hpow] at hkle
    have : k ≤ 1 := by exact_mod_cast hkle
    omega

/-- **A `k`-th root of an element of valuation one forces `k = 1`**, for a valuation with values in
the integers.  This is the form a Kummer subextension consumes: the block field is
`O(c^{1/k})` for some `k` dividing the cyclic degree, and the marked coordinate divisor gives
`v(c) = 1`. -/
theorem eq_one_of_pow_eq_of_addValuation_eq_one {M : Type*} [Field M]
    (w : AddValuation M (WithTop ℤ)) {z c : M} {k : ℕ}
    (hzk : z ^ k = c) (hc : w c = ((1 : ℤ) : WithTop ℤ)) : k = 1 := by
  have hpow : w c = k • w z := by
    rw [← hzk]
    exact AddValuation.map_pow w z k
  rw [hc] at hpow
  rcases eq_or_ne (w z) ⊤ with htop | htop
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hpow
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [succ_nsmul, htop, add_top] at hpow
      simp at hpow
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← ha] at hpow
    have hcast : ((1 : ℤ) : WithTop ℤ) = ((k • a : ℤ) : WithTop ℤ) := by
      rw [hpow]
      norm_cast
    have hint : (1 : ℤ) = k • a := by exact_mod_cast hcast
    rw [nsmul_eq_mul] at hint
    have hk : (k : ℤ) ∣ 1 := ⟨a, hint⟩
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one hk)
    omega

end GaloisForLFunctions.HTGeometry
