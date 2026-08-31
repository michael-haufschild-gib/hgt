import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueIteration

/-!
# Exact integer parameters for Heath--Brown's second branch

The paper takes `N0 = max(T^(1/3), (R*T)^(1/4))`.  Mean-value recurrences use natural cutoffs, so
the canonical literal realization is the natural ceiling.  This file proves its complete rounding
package and the source cardinality bound `R ≤ T` for a distinct positive support below height `T`.
-/

namespace RHTower.Sieve

noncomputable section

/-- Canonical natural realization of Heath--Brown's second-branch scale. -/
def heathBrownSecondScale (T R : ℝ) : ℕ :=
  ⌈max (T ^ (1 / 3 : ℝ)) ((R * T) ^ (1 / 4 : ℝ))⌉₊

/-- The selected integer scale dominates `T^(1/3)`. -/
theorem heathBrown_rpow_oneThird_le_secondScale (T R : ℝ) :
    T ^ (1 / 3 : ℝ) ≤ (heathBrownSecondScale T R : ℝ) := by
  exact (le_max_left _ _).trans (Nat.le_ceil _)

/-- The selected integer scale dominates `(R*T)^(1/4)`. -/
theorem heathBrown_mul_rpow_oneFourth_le_secondScale (T R : ℝ) :
    (R * T) ^ (1 / 4 : ℝ) ≤ (heathBrownSecondScale T R : ℝ) := by
  exact (le_max_right _ _).trans (Nat.le_ceil _)

/-- The selected integer scale is positive throughout the source height range. -/
theorem one_le_heathBrownSecondScale {T R : ℝ} (hT : 1 ≤ T) :
    1 ≤ heathBrownSecondScale T R := by
  have hthird : 1 ≤ T ^ (1 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hcast : (1 : ℝ) ≤ (heathBrownSecondScale T R : ℝ) :=
    hthird.trans (heathBrown_rpow_oneThird_le_secondScale T R)
  exact_mod_cast hcast

/-- Natural ceiling costs less than one above the paper's real scale. -/
theorem cast_heathBrownSecondScale_lt_max_add_one
    {T R : ℝ} (hT : 0 ≤ T) :
    (heathBrownSecondScale T R : ℝ) <
      max (T ^ (1 / 3 : ℝ)) ((R * T) ^ (1 / 4 : ℝ)) + 1 := by
  apply Nat.ceil_lt_add_one
  exact (Real.rpow_nonneg hT _).trans (le_max_left _ _)

/-- Rounded scale is bounded by the sum of the two paper scales and one. -/
theorem cast_heathBrownSecondScale_le_add_add_one
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    (heathBrownSecondScale T R : ℝ) ≤
      T ^ (1 / 3 : ℝ) + (R * T) ^ (1 / 4 : ℝ) + 1 := by
  have ha : 0 ≤ T ^ (1 / 3 : ℝ) := Real.rpow_nonneg hT _
  have hb : 0 ≤ (R * T) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hR hT) _
  exact (cast_heathBrownSecondScale_lt_max_add_one hT).le.trans
    (by simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right (max_le_add_of_nonneg ha hb) 1)

/-- Since `T^(1/3) ≥ 1`, rounding is absorbed by one extra copy of that scale. -/
theorem cast_heathBrownSecondScale_le_two_mul_oneThird_add_oneFourth
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 ≤ R) :
    (heathBrownSecondScale T R : ℝ) ≤
      2 * T ^ (1 / 3 : ℝ) + (R * T) ^ (1 / 4 : ℝ) := by
  have hthird : 1 ≤ T ^ (1 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
  calc
    (heathBrownSecondScale T R : ℝ) ≤
        T ^ (1 / 3 : ℝ) + (R * T) ^ (1 / 4 : ℝ) + 1 :=
      cast_heathBrownSecondScale_le_add_add_one (zero_le_one.trans hT) hR
    _ ≤ 2 * T ^ (1 / 3 : ℝ) + (R * T) ^ (1 / 4 : ℝ) := by linarith

/-- Squaring the selected scale reaches the paper's first-branch threshold `T^(2/3)`. -/
theorem rpow_twoThirds_le_heathBrownSecondScale_sq
    {T R : ℝ} (hT : 0 ≤ T) :
    T ^ (2 / 3 : ℝ) ≤ (heathBrownSecondScale T R : ℝ) ^ 2 := by
  have hthird0 : 0 ≤ T ^ (1 / 3 : ℝ) := Real.rpow_nonneg hT _
  have hscale := heathBrown_rpow_oneThird_le_secondScale T R
  have hsquare : (T ^ (1 / 3 : ℝ)) ^ 2 ≤
      (heathBrownSecondScale T R : ℝ) ^ 2 := by nlinarith
  calc
    T ^ (2 / 3 : ℝ) = T ^ ((1 / 3 : ℝ) * 2) := by norm_num
    _ = (T ^ (1 / 3 : ℝ)) ^ (2 : ℝ) := Real.rpow_mul hT _ _
    _ = (T ^ (1 / 3 : ℝ)) ^ (2 : ℕ) := Real.rpow_natCast _ _
    _ ≤ (heathBrownSecondScale T R : ℝ) ^ 2 := hsquare

/-- A finite set of distinct positive integers below `T` has cardinality at most `T`. -/
theorem cast_card_le_height_of_pnat_support
    (A : Finset PNat) {T : ℝ} (hT : 0 ≤ T)
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ T) :
    (A.card : ℝ) ≤ T := by
  let U : Finset ℕ := Finset.Icc 1 ⌊T⌋₊
  have hcard : A.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (fun n : PNat => (n : ℕ))
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨n.pos, Nat.le_floor (hA n hn)⟩
    · intro x hx y hy hxy
      exact PNat.eq hxy
  have hU : U.card ≤ ⌊T⌋₊ := by
    change (Finset.Icc 1 ⌊T⌋₊).card ≤ ⌊T⌋₊
    rw [Nat.card_Icc]
    omega
  have hfloor : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT
  have hcast : (A.card : ℝ) ≤ (⌊T⌋₊ : ℝ) := by
    exact_mod_cast hcard.trans hU
  exact hcast.trans hfloor

end

end RHTower.Sieve
