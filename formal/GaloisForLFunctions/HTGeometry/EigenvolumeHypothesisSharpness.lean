import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# The side conditions of the horizon theorem are indispensable

The horizon theorem concludes that the order is `-1` on the whole divisorial support, from the
local order law together with three side conditions: surjectivity of the divisor map, finiteness of
the support, and ramification somewhere on every recurrent cycle.  Finiteness was already known to
be indispensable.  The other two are as well, and the counterexamples are small.

Without ramification the law is satisfied by any constant order, and without surjectivity the
backward orbit can escape to infinity so that no component is recurrent at all.  In both cases the
order can be an arbitrary integer.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Ramification cannot be dropped.**  With every ramification index equal to one and the divisor
map the identity, the local order law holds for a constant order of any value. -/
theorem exists_unramified_order_ne_neg_one :
    ∃ (F : Unit → Unit) (c : Unit → ℤ) (e : Unit → ℕ),
      Function.Surjective F ∧ (∀ y, 1 ≤ e y) ∧
      (∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) ∧
      {y : Unit | c y ≠ 0}.Finite ∧
      ∃ x, c x ≠ 0 ∧ c x ≠ -1 := by
  refine ⟨id, fun _ => 5, fun _ => 1, Function.surjective_id, fun _ => le_refl 1, fun _ => by
    norm_num, Set.toFinite _, ⟨(), by norm_num, by norm_num⟩⟩

/-- **Surjectivity cannot be dropped.**  For the successor map no component is recurrent, so the
ramification condition is vacuous, yet the order at the only component of the support is not
`-1`. -/
theorem exists_nonsurjective_order_ne_neg_one :
    ∃ (F : ℕ → ℕ) (c : ℕ → ℤ) (e : ℕ → ℕ),
      ¬ Function.Surjective F ∧ (∀ y, 1 ≤ e y) ∧
      (∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) ∧
      {y : ℕ | c y ≠ 0}.Finite ∧
      (∀ y : ℕ, c y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y → ∃ k < n, 1 < e (F^[k] y)) ∧
      ∃ x, c x ≠ 0 ∧ c x ≠ -1 := by
  classical
  refine ⟨Nat.succ, fun n => if n = 0 then 1 else 0, fun n => if n = 0 then 2 else 1, ?_, ?_, ?_,
    ?_, ?_, ⟨0, by norm_num, by norm_num⟩⟩
  · intro hsurj
    obtain ⟨n, hn⟩ := hsurj 0
    exact Nat.succ_ne_zero n hn
  · intro y
    by_cases h : y = 0 <;> simp [h]
  · intro x
    by_cases h : x = 0
    · subst h
      norm_num
    · simp [h]
  · refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro y hy
    by_contra hne
    have hy0 : y ≠ 0 := by simpa using hne
    exact hy (by simp [hy0])
  · intro y hy n hn hper
    exfalso
    rw [Nat.succ_iterate] at hper
    omega

end GaloisForLFunctions.HTGeometry
