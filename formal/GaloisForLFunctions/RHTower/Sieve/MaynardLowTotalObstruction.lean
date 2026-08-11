import GaloisForLFunctions.RHTower.Sieve.MaynardAggregateGreedySelection

/-!
# Low-total obstruction in the complete dyadic aggregate

The complete Heath--Brown aggregate contains an all-zero dyadic-index box.  Its total logarithmic
length is exactly zero.  Consequently no positive all-short grouping threshold can be imposed on
every box before pointwise selection.  A valid argument must first split off low-total boxes and
bound their aggregate, then pigeonhole only the surviving eligible boxes.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The zero dyadic tuple. -/
def zeroDyadicTuple (r : ℕ) : Fin r → ℕ := fun _ => 0

theorem zeroDyadicTuple_mem (r M : ℕ) :
    zeroDyadicTuple r ∈ dyadicChoiceSet r M := by
  simp [zeroDyadicTuple, dyadicChoiceSet]

@[simp] theorem dyadicLogExponent_zero (T0 : ℝ) :
    dyadicLogExponent T0 0 = 0 := by
  simp [dyadicLogExponent, Real.logb_one]

@[simp] theorem heathBrownBoxFactorExponent_zero
    (k m : ℕ) (i : HeathBrownBoxFactorIndex k m) :
    heathBrownBoxFactorExponent (zeroDyadicTuple (k - m))
      (zeroDyadicTuple (k - m - 1)) 0 i = 0 := by
  rcases i with i | i
  · rfl
  · rcases i with i | i <;> rfl

theorem zero_box_total_exponent (T0 : ℝ) (k m : ℕ) :
    (∑ i : HeathBrownBoxFactorIndex k m,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent (zeroDyadicTuple (k - m))
          (zeroDyadicTuple (k - m - 1)) 0 i)) = 0 := by
  simp

/-- **No-go:** universal positive total-mass hypothesis used by the first aggregate selector is
false for every nonempty packet. -/
theorem not_universal_heathBrown_box_total_positive
    (L X k : ℕ) (hk : 0 < k) (T0 t : ℝ) (ht : 0 < t) :
    ¬ (∀ m ∈ Finset.range k,
      ∀ q ∈ Finset.range (Nat.log 2 X + 1),
      ∀ b ∈ dyadicChoiceSet (k - m - 1) X,
      ∀ a ∈ dyadicChoiceSet (k - m) L,
        t ≤ ∑ i : HeathBrownBoxFactorIndex k m,
          dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i)) := by
  intro h
  have hm : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
  have hq : 0 ∈ Finset.range (Nat.log 2 X + 1) := by simp
  have hb := zeroDyadicTuple_mem (k - 0 - 1) X
  have ha := zeroDyadicTuple_mem (k - 0) L
  have hbad := h 0 hm 0 hq (zeroDyadicTuple (k - 0 - 1)) hb
    (zeroDyadicTuple (k - 0)) ha
  rw [zero_box_total_exponent] at hbad
  linarith

end RHTower.Sieve
