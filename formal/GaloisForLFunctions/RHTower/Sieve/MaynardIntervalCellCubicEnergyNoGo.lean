import GaloisForLFunctions.RHTower.Sieve.MaynardSpatialMellinL4


/-!
# Cubic interval-cell energy no-go for Route T2

Route T2's cancellation-first Wold terminal program needs a power saving in the common-mode
low-shell bad-set estimate.  The existing spatial fourth-moment interface is controlled by
Maynard's exact additive-energy count `maynardRStar`.  A proposed generic repair was to obtain
that saving from cardinality-only `L²/L⁴` rearrangement.

This module kills that repair.  For the consecutive-cell packet `range n`, pair-sum fibres are
triangular and give the exact identity

`3 * maynardRStar(range n) = 2 * n^3 + n`.

Thus normalized energy tends to `2/3`, and no uniform quadratic cardinality bound exists.
Consecutive cells are legitimate generic Fourier packets, so no argument using only packet
cardinality and the present `L²/L⁴` interface can produce a subcubic saving.

The killed proof chain was:

generic cardinality-only `L²/L⁴` saving
`=>` low-shell bad-set power saving
`=>` prime-gap moment exponent below `3/2`
`=>` cancellation-first terminal-plus-edge control
`=>` zero Wold residual terminal width
`=>` RH.

The positive survivor must use arithmetic selected-cell structure that excludes or defeats this
interval packet, together with target-reciprocal localization before terminal and edge terms are
separated.  No computation or numerical zero data enters any proof.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private def intervalPairOfFirst (k : ℕ) : ℕ ↪ ℕ × ℕ where
  toFun a := (a, k - a)
  inj' := by
    intro a b h
    exact congrArg Prod.fst h

private theorem pairSumFiber_range_eq_map_Icc (n k : ℕ) :
    ((Finset.range n).product (Finset.range n)).filter
        (fun p => p.1 + p.2 = k) =
      (Finset.Icc (k + 1 - n) (min k (n - 1))).map
        (intervalPairOfFirst k) := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hrange : p.1 < n ∧ p.2 < n := by simpa using hp'.1
    have hab : p.1 + p.2 = k := hp'.2
    apply Finset.mem_map.mpr
    refine ⟨p.1, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      refine ⟨?_, ?_⟩
      · omega
      · exact le_min (by omega) (by omega)
    · apply Prod.ext
      · rfl
      · dsimp [intervalPairOfFirst]
        omega
  · intro hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_map.mp hp
    have ha' := Finset.mem_Icc.mp ha
    rw [← hpa]
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · have ha_lt : a < n := by omega
      have hsub_lt : k - a < n := by omega
      simpa [intervalPairOfFirst] using And.intro ha_lt hsub_lt
    · dsimp [intervalPairOfFirst]
      omega

private theorem card_pairSumFiber_range (n k : ℕ) :
    (((Finset.range n).product (Finset.range n)).filter
        (fun p => p.1 + p.2 = k)).card =
      if k < n then k + 1 else if k < 2 * n then 2 * n - 1 - k else 0 := by
  rw [pairSumFiber_range_eq_map_Icc, Finset.card_map, Nat.card_Icc]
  split_ifs with hkn hk2
  · have hn : 0 < n := by omega
    have hmin : min k (n - 1) = k := min_eq_left (by omega)
    rw [hmin]
    omega
  · have hmin : min k (n - 1) = n - 1 := min_eq_right (by omega)
    rw [hmin]
    omega
  · omega

/-- Exact triangular pair-sum decomposition for consecutive natural cells. -/
theorem maynardNatRStar_range_eq_sum_squares (n : ℕ) :
    maynardNatRStar (Finset.range n) n =
      ∑ k ∈ Finset.range n, ((k + 1) ^ 2 + k ^ 2) := by
  rw [maynardNatRStar, show 2 * n = n + n by omega,
    Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [card_pairSumFiber_range]
    simp only [Finset.mem_range] at hk
    simp [hk]
  · calc
      (∑ k ∈ Finset.range n,
          (((Finset.range n).product (Finset.range n)).filter
            (fun p => p.1 + p.2 = n + k)).card ^ 2) =
          ∑ k ∈ Finset.range n, (n - 1 - k) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_range] at hk
            rw [card_pairSumFiber_range]
            have h1 : ¬ n + k < n := by omega
            have h2 : n + k < 2 * n := by omega
            simp [h1, h2]
            omega
      _ = ∑ k ∈ Finset.range n, k ^ 2 :=
        Finset.sum_range_reflect (fun k => k ^ 2) n

/-- Consecutive natural cells have the exact cubic fourth-moment count. -/
theorem three_mul_maynardNatRStar_range (n : ℕ) :
    3 * maynardNatRStar (Finset.range n) n = 2 * n ^ 3 + n := by
  rw [maynardNatRStar_range_eq_sum_squares]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        3 * ((∑ k ∈ Finset.range n, ((k + 1) ^ 2 + k ^ 2)) +
            ((n + 1) ^ 2 + n ^ 2)) =
            3 * (∑ k ∈ Finset.range n, ((k + 1) ^ 2 + k ^ 2)) +
              3 * ((n + 1) ^ 2 + n ^ 2) := by ring
        _ = (2 * n ^ 3 + n) + 3 * ((n + 1) ^ 2 + n ^ 2) := by rw [ih]
        _ = 2 * (n + 1) ^ 3 + (n + 1) := by ring

/-- Integer-cell form of the exact interval-packet energy law. -/
theorem three_mul_maynardRStar_intervalCells (n : ℕ) :
    3 * maynardRStar
        ((Finset.range n).map maynardNatToIntEmbedding) =
      2 * n ^ 3 + n := by
  rw [← maynardNatRStar_eq_maynardRStar_map (S := Finset.range n)
    (N := n) (by simp)]
  exact three_mul_maynardNatRStar_range n

private theorem maynardRStar_intervalCells_div_cube_eq {n : ℕ} (hn : 0 < n) :
    (maynardRStar
        ((Finset.range n).map maynardNatToIntEmbedding) : ℝ) /
        (n : ℝ) ^ 3 =
      2 / 3 + 1 / (3 * (n : ℝ) ^ 2) := by
  have hformula := three_mul_maynardRStar_intervalCells n
  have hformulaR :
      3 * (maynardRStar
          ((Finset.range n).map maynardNatToIntEmbedding) : ℝ) =
        2 * (n : ℝ) ^ 3 + n := by
    exact_mod_cast hformula
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  nlinarith

/-- The interval packet asymptotically saturates two thirds of the cubic energy scale. -/
theorem tendsto_maynardRStar_intervalCells_div_cube :
    Filter.Tendsto
      (fun n : ℕ =>
        (maynardRStar
            ((Finset.range n).map maynardNatToIntEmbedding) : ℝ) /
          (n : ℝ) ^ 3)
      Filter.atTop (nhds (2 / 3 : ℝ)) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Filter.Tendsto
      (fun n : ℕ => 2 / 3 + (1 / 3) * ((n : ℝ)⁻¹) ^ 2)
      Filter.atTop (nhds (2 / 3 : ℝ)) := by
    simpa using
      tendsto_const_nhds.add ((hinv.pow 2).const_mul (1 / 3 : ℝ))
  apply hmodel.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  rw [maynardRStar_intervalCells_div_cube_eq (by omega : 0 < n)]
  field_simp

/-- Every proposed quadratic cardinality ceiling is violated by an interval packet. -/
theorem exists_intervalCells_maynardRStar_gt_quadratic (C : ℕ) :
    ∃ n : ℕ, C * n ^ 2 <
      maynardRStar ((Finset.range n).map maynardNatToIntEmbedding) := by
  refine ⟨3 * C + 1, ?_⟩
  have hformula := three_mul_maynardRStar_intervalCells (3 * C + 1)
  have hn : 3 * C < 3 * C + 1 := by omega
  have hn2 : 0 < (3 * C + 1) ^ 2 := by positivity
  have hmul := Nat.mul_lt_mul_of_pos_right hn hn2
  have hcub : (3 * C) * (3 * C + 1) ^ 2 < (3 * C + 1) ^ 3 := by
    calc
      (3 * C) * (3 * C + 1) ^ 2 <
          (3 * C + 1) * (3 * C + 1) ^ 2 := hmul
      _ = (3 * C + 1) ^ 3 := by ring
  have htarget : 3 * (C * (3 * C + 1) ^ 2) <
      2 * (3 * C + 1) ^ 3 + (3 * C + 1) := by
    calc
      3 * (C * (3 * C + 1) ^ 2) =
          (3 * C) * (3 * C + 1) ^ 2 := by ring
      _ < (3 * C + 1) ^ 3 := hcub
      _ ≤ 2 * (3 * C + 1) ^ 3 + (3 * C + 1) := by omega
  have hscaled : 3 * (C * (3 * C + 1) ^ 2) <
      3 * maynardRStar
        ((Finset.range (3 * C + 1)).map maynardNatToIntEmbedding) := by
    rw [hformula]
    exact htarget
  omega


/-- No uniform quadratic cardinality bound can control Maynard's fourth-moment count on all
consecutive-cell packets.  This is the formal T2 generic-`L²/L⁴` route kill. -/
theorem not_exists_uniform_quadratic_bound_maynardRStar_intervalCells :
    ¬ ∃ C : ℕ, ∀ n : ℕ,
      maynardRStar ((Finset.range n).map maynardNatToIntEmbedding) ≤ C * n ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_intervalCells_maynardRStar_gt_quadratic C
  exact (not_lt_of_ge (hC n)) hn

end
end RHTower.Sieve
