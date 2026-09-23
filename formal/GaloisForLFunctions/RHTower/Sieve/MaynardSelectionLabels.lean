import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicGreedyGroup
import GaloisForLFunctions.RHTower.Sieve.MaynardColorFiberCounting

/-!
# Finite labels for uniform Maynard selection

Every pointwise choice is encoded by one finite label: packet degree, log-block exponent, zeta
tuple, Möbius tuple, and a selected factor subfamily.  This makes the multiplicity paid by uniform
color-fibre counting explicit.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- All literal dyadic boxes in the `k`-term Heath--Brown packet. -/
abbrev HeathBrownBoxChoice (L X k : ℕ) :=
  Σ m : Fin k,
    Fin (Nat.log 2 X + 1) ×
      {b : Fin (k - (m : ℕ) - 1) → ℕ // b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X} ×
      {a : Fin (k - (m : ℕ)) → ℕ // a ∈ dyadicChoiceSet (k - (m : ℕ)) L}

def HeathBrownBoxChoice.m {L X k : ℕ} (c : HeathBrownBoxChoice L X k) : ℕ := c.1
def HeathBrownBoxChoice.q {L X k : ℕ} (c : HeathBrownBoxChoice L X k) : ℕ := c.2.1
def HeathBrownBoxChoice.b {L X k : ℕ} (c : HeathBrownBoxChoice L X k) :
    Fin (k - c.m - 1) → ℕ := c.2.2.1.1
def HeathBrownBoxChoice.a {L X k : ℕ} (c : HeathBrownBoxChoice L X k) :
    Fin (k - c.m) → ℕ := c.2.2.2.1

/-- Complete pointwise selection label: one box and one possible factor group inside it. -/
abbrev HeathBrownSelectionLabel (L X k : ℕ) :=
  Σ c : HeathBrownBoxChoice L X k,
    Finset (HeathBrownBoxFactorIndex k c.m)

/-- Exact number of literal dyadic boxes. -/
theorem card_heathBrownBoxChoice (L X k : ℕ) :
    Fintype.card (HeathBrownBoxChoice L X k) =
      ∑ m : Fin k,
        (Nat.log 2 X + 1) *
          (Nat.log 2 X + 1) ^ (k - (m : ℕ) - 1) *
          (Nat.log 2 L + 1) ^ (k - (m : ℕ)) := by
  simp [HeathBrownBoxChoice, card_dyadicChoiceSet, mul_assoc]

/-- Box multiplicity is bounded by the same fixed-degree polylog appearing in pointwise
aggregate-to-box selection. -/
theorem card_heathBrownBoxChoice_le (L X k : ℕ) :
    Fintype.card (HeathBrownBoxChoice L X k) ≤
      k * (Nat.log 2 X + 1) ^ k * (Nat.log 2 L + 1) ^ k := by
  rw [card_heathBrownBoxChoice]
  calc
    ∑ m : Fin k,
        (Nat.log 2 X + 1) *
          (Nat.log 2 X + 1) ^ (k - (m : ℕ) - 1) *
          (Nat.log 2 L + 1) ^ (k - (m : ℕ))
      ≤ ∑ _m : Fin k,
          (Nat.log 2 X + 1) ^ k * (Nat.log 2 L + 1) ^ k := by
        apply Finset.sum_le_sum
        intro m _hm
        have hm : (m : ℕ) < k := m.isLt
        have hxexp : (k - (m : ℕ) - 1) + 1 = k - (m : ℕ) := by omega
        have hxpow : (Nat.log 2 X + 1) *
            (Nat.log 2 X + 1) ^ (k - (m : ℕ) - 1) =
              (Nat.log 2 X + 1) ^ (k - (m : ℕ)) := by
          calc
            (Nat.log 2 X + 1) * (Nat.log 2 X + 1) ^ (k - (m : ℕ) - 1) =
                (Nat.log 2 X + 1) ^ (k - (m : ℕ) - 1) *
                  (Nat.log 2 X + 1) := by ac_rfl
            _ = (Nat.log 2 X + 1) ^ ((k - (m : ℕ) - 1) + 1) :=
              (pow_succ _ _).symm
            _ = (Nat.log 2 X + 1) ^ (k - (m : ℕ)) := congrArg _ hxexp
        rw [hxpow]
        exact Nat.mul_le_mul
          (pow_le_pow_right₀ (by omega) (Nat.sub_le k (m : ℕ)))
          (pow_le_pow_right₀ (by omega) (Nat.sub_le k (m : ℕ)))
    _ = k * (Nat.log 2 X + 1) ^ k * (Nat.log 2 L + 1) ^ k := by
      simp [mul_assoc]

/-- Exact selection-label count: every box contributes all subsets of its factor family. -/
theorem card_heathBrownSelectionLabel (L X k : ℕ) :
    Fintype.card (HeathBrownSelectionLabel L X k) =
      ∑ c : HeathBrownBoxChoice L X k,
        2 ^ Fintype.card (HeathBrownBoxFactorIndex k c.m) := by
  simp [HeathBrownSelectionLabel, Fintype.card_finset]

/-- Uniform selection-label bound. -/
theorem card_heathBrownSelectionLabel_le (L X k : ℕ) :
    Fintype.card (HeathBrownSelectionLabel L X k) ≤
      k * (Nat.log 2 X + 1) ^ k * (Nat.log 2 L + 1) ^ k * 2 ^ (2 * k) := by
  rw [card_heathBrownSelectionLabel]
  calc
    ∑ c : HeathBrownBoxChoice L X k,
        2 ^ Fintype.card (HeathBrownBoxFactorIndex k c.m)
      ≤ ∑ _c : HeathBrownBoxChoice L X k, 2 ^ (2 * k) := by
        apply Finset.sum_le_sum
        intro c _hc
        apply Nat.pow_le_pow_right
        · norm_num
        · have hm : (c.1 : ℕ) < k := c.1.isLt
          change Fintype.card (HeathBrownBoxFactorIndex k (c.1 : ℕ)) ≤ 2 * k
          rw [card_heathBrownBoxFactorIndex hm]
          omega
    _ = Fintype.card (HeathBrownBoxChoice L X k) * 2 ^ (2 * k) := by
      simp
    _ ≤ (k * (Nat.log 2 X + 1) ^ k * (Nat.log 2 L + 1) ^ k) * 2 ^ (2 * k) :=
      Nat.mul_le_mul_right (2 ^ (2 * k)) (card_heathBrownBoxChoice_le L X k)

/-- Concrete `k=60` label ceiling used by Route T. -/
theorem card_heathBrownSelectionLabel_sixty_le (L X : ℕ) :
    Fintype.card (HeathBrownSelectionLabel L X 60) ≤
      60 * (Nat.log 2 X + 1) ^ (60 : ℕ) * (Nat.log 2 L + 1) ^ (60 : ℕ) * 2 ^ (120 : ℕ) := by
  simpa using card_heathBrownSelectionLabel_le L X 60

end RHTower.Sieve
