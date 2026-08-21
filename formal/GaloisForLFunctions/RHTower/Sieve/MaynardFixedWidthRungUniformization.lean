import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketNatOrder

/-!
# Finite uniformization of fixed-width Route-T rungs

At fixed relative width, every telescope length is bounded by one canonical logarithmic natural
number.  Consequently pointwise existential packet rungs form one fixed finite union, suitable for
measure summation.
-/

noncomputable section
namespace RHTower.Sieve

/-- Canonical number of stopped dyadic rungs at fixed relative width. -/
def routeTFixedWidthRungCount (H0 : ℝ) : ℕ :=
  ⌈1 + Real.log ((1 / 4) / H0) / Real.log 2⌉₊

theorem routeTFixedWidthRungCount_pos
    {H0 : ℝ} (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4) :
    0 < routeTFixedWidthRungCount H0 := by
  apply Nat.ceil_pos.mpr
  have hratio : 1 ≤ (1 / 4) / H0 :=
    (le_div_iff₀ hH0).2 (by simpa using hH0quarter)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 ≤ Real.log ((1 / 4) / H0) := Real.log_nonneg hratio
  positivity

/-- Every admissible telescope length lies below the canonical fixed-width rung count. -/
theorem routeTComparableWidthLadder_index_le_fixedWidthRungCount
    {H0 : ℝ} (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4)
    {J : ℕ} (hJ : 0 < J)
    (hbelow : (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0) :
    J ≤ routeTFixedWidthRungCount H0 := by
  have hlog := routeTComparableWidthLadder_index_le_log
    hH0 hH0quarter hJ hbelow
  have hceil :
      1 + Real.log ((1 / 4) / H0) / Real.log 2 ≤
        (routeTFixedWidthRungCount H0 : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hlog.trans hceil

/-- Pointwise existential packet rungs are covered by one fixed finite union.  Replacing `J` by
the canonical upper bound weakens the packet threshold exactly from `D/J` to `D/Q`. -/
theorem fixedWidth_packet_bad_subset_rung_union
    {H0 D : ℝ} (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4) (hD : 0 ≤ D)
    {packet : ℕ → ℝ → ℂ} {P : Set ℝ}
    (hproducer : ∀ lambda ∈ P,
      ∃ J : ℕ, 0 < J ∧
        (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 ∧
        ∃ j ∈ Finset.range J,
          D / (J : ℝ) ≤ ‖packet j lambda‖) :
    P ⊆ ⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0),
      {lambda | D / (routeTFixedWidthRungCount H0 : ℝ) ≤ ‖packet j lambda‖} := by
  intro lambda hlambda
  obtain ⟨J, hJ, hbelow, j, hj, hlarge⟩ := hproducer lambda hlambda
  have hJQ : J ≤ routeTFixedWidthRungCount H0 :=
    routeTComparableWidthLadder_index_le_fixedWidthRungCount
      hH0 hH0quarter hJ hbelow
  have hJreal : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hJQreal : (J : ℝ) ≤ (routeTFixedWidthRungCount H0 : ℝ) := by
    exact_mod_cast hJQ
  have hthreshold :
      D / (routeTFixedWidthRungCount H0 : ℝ) ≤ D / (J : ℝ) :=
    div_le_div_of_nonneg_left hD hJreal hJQreal
  apply Set.mem_iUnion_of_mem j
  apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr
    ((Finset.mem_range.mp hj).trans_le hJQ))
  exact hthreshold.trans hlarge

end RHTower.Sieve
