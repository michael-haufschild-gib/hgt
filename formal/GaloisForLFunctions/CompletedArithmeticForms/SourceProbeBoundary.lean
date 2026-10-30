import GaloisForLFunctions.CompletedArithmeticForms.TerminalCompletion

/-!
# Exact dual cost of a finite probe on arbitrary finite source supports

Fixing the probe support while allowing the source support to grow restores
the terminal Dirichlet edge. The sharp cost is attained by a neutral source
with one additional coordinate. This distinguishes probe truncation from
source truncation at the level of the complete covariance form.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower.DeletionAveragedDivisor

/-- The accumulated coordinate of a source packet, constant beyond its support. -/
def finiteSourcePrefix (c : ℕ → ℝ) (T n : ℕ) : ℝ := ∑ j ∈ Icc 1 (min n T), c j

/-- The accumulation carrier has an exact reciprocal terminal mass. -/
theorem hasSum_accumulationCarrier_tail (T : ℕ) :
    HasSum (fun i : ℕ => 1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2)))
      (1 / ((T : ℝ) + 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  have hden : Tendsto (fun i : ℕ => (i : ℝ) + T + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun i : ℕ => ((i : ℝ) + T + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun i : ℕ => 1 / ((T : ℝ) + 1) - ((i : ℝ) + T + 1)⁻¹)
      atTop (𝓝 (1 / ((T : ℝ) + 1) - 0)) := tendsto_const_nhds.sub hinv
  convert hlim using 1
  · funext N
    have hstep (i : ℕ) : 1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2)) =
        1 / ((i : ℝ) + T + 1) - 1 / (((i + 1 : ℕ) : ℝ) + T + 1) := by
      have h0 : (i : ℝ) + T + 1 ≠ 0 := by positivity
      have h1 : (i : ℝ) + T + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    simp_rw [hstep]
    rw [Finset.sum_range_sub']
    simp only [Nat.cast_zero, zero_add, one_div]
  · simp

/-- Terminal completion is exactly the literal infinite accumulation energy of the finite source. -/
theorem hasSum_finiteSourceEnergy (c : ℕ → ℝ) (T : ℕ) :
    HasSum (fun i : ℕ => finiteSourcePrefix c T (i + 1) ^ 2 /
      (((i : ℝ) + 1) * ((i : ℝ) + 2))) (finiteSourceEnergy c T) := by
  let f := fun i : ℕ => finiteSourcePrefix c T (i + 1) ^ 2 /
    (((i : ℝ) + 1) * ((i : ℝ) + 2))
  have hpref (L : ℕ) : L ≤ T → (∑ i ∈ range L, f i) = cumulativeEnergy c L := by
    induction L with
    | zero => intro h; simp [cumulativeEnergy]
    | succ L ih =>
      intro hLT
      rw [Finset.sum_range_succ, ih (by omega)]
      unfold cumulativeEnergy
      rw [sum_Icc_succ_top (by omega)]
      simp only [f, finiteSourcePrefix, min_eq_left hLT, Nat.cast_add, Nat.cast_one]
      ring
  have htail : HasSum (fun i => f (i + T))
      ((∑ j ∈ Icc 1 T, c j) ^ 2 / ((T : ℝ) + 1)) := by
    have h := (hasSum_accumulationCarrier_tail T).mul_left ((∑ j ∈ Icc 1 T, c j) ^ 2)
    have he (i : ℕ) : (∑ j ∈ Icc 1 T, c j) ^ 2 *
        (1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2))) = f (i + T) := by
      dsimp only [f, finiteSourcePrefix]
      rw [min_eq_right (show T ≤ i + T + 1 by omega)]
      push_cast
      ring
    simpa only [he, mul_one_div] using h
  have hfull := (hasSum_nat_add_iff T).mp htail
  rw [hpref T le_rfl] at hfull
  simpa only [finiteSourceEnergy, add_comm] using hfull

/-- A probe is zero beyond its prescribed coordinate support. -/
def finiteProbe (b : ℕ → ℝ) (T j : ℕ) : ℝ := if j ≤ T then b j else 0

/-- A fixed finite probe pays its local weighted variation and its terminal edge. -/
def finiteProbeDualCost (b : ℕ → ℝ) (T : ℕ) : ℝ :=
  finiteSourceDualCost b T + ((T : ℝ) * b T) ^ 2

theorem finiteSourceDualCost_mono (b : ℕ → ℝ) {K L : ℕ} (hKL : K ≤ L) :
    finiteSourceDualCost b K ≤ finiteSourceDualCost b L := by
  unfold finiteSourceDualCost dirichletEnergy
  exact sum_le_sum_of_subset_of_nonneg (range_mono hKL) (fun i hi hnot => sq_nonneg _)

theorem finiteSourceDualCost_finiteProbe_same (b : ℕ → ℝ) (T : ℕ) :
    finiteSourceDualCost (finiteProbe b T) T = finiteSourceDualCost b T := by
  unfold finiteSourceDualCost dirichletEnergy
  apply sum_congr rfl
  intro i hi
  simp only [finiteProbe, if_pos (show i ≤ T by have := mem_range.mp hi; omega),
    if_pos (show i + 1 ≤ T by have := mem_range.mp hi; omega)]

/-- One extra source coordinate exposes the entire terminal edge of the fixed probe. -/
theorem finiteSourceDualCost_finiteProbe_succ (b : ℕ → ℝ) (T : ℕ) :
    finiteSourceDualCost (finiteProbe b T) (T + 1) = finiteProbeDualCost b T := by
  change (∑ i ∈ range (T + 1),
    (((i + 1 : ℕ) : ℝ) * finiteProbe b T (i + 1) - (i : ℝ) * finiteProbe b T i) ^ 2) = _
  rw [Finset.sum_range_succ]
  change finiteSourceDualCost (finiteProbe b T) T +
    (((T + 1 : ℕ) : ℝ) * finiteProbe b T (T + 1) - (T : ℝ) * finiteProbe b T T) ^ 2 = _
  rw [finiteSourceDualCost_finiteProbe_same]
  simp only [finiteProbe, if_neg (by omega : ¬ T + 1 ≤ T), if_pos le_rfl,
    mul_zero, zero_sub, neg_sq, finiteProbeDualCost]

/-- Further source coordinates cannot increase the finite probe's exact dual cost. -/
theorem finiteSourceDualCost_finiteProbe_stable (b : ℕ → ℝ) {T K : ℕ} (hTK : T + 1 ≤ K) :
    finiteSourceDualCost (finiteProbe b T) K = finiteProbeDualCost b T := by
  rw [← finiteSourceDualCost_finiteProbe_succ]
  unfold finiteSourceDualCost dirichletEnergy
  symm
  apply sum_subset (range_mono hTK)
  intro i hi hn
  have hTi : T < i := by simp only [mem_range] at hn; omega
  simp only [finiteProbe, if_neg (by omega : ¬ i + 1 ≤ T), if_neg (by omega : ¬ i ≤ T),
    mul_zero, sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0)]

/-- The fixed probe cost controls every finite source support simultaneously. -/
theorem finiteSourceDualCost_finiteProbe_le (b : ℕ → ℝ) (T K : ℕ) :
    finiteSourceDualCost (finiteProbe b T) K ≤ finiteProbeDualCost b T := by
  rcases le_total K (T + 1) with hK | hK
  · exact (finiteSourceDualCost_mono _ hK).trans_eq (finiteSourceDualCost_finiteProbe_succ b T)
  · exact (finiteSourceDualCost_finiteProbe_stable b hK).le

/-- The exact cost over all source supports is attained at the first coordinate beyond the probe. -/
theorem finiteProbeDualCost_isGreatest (b : ℕ → ℝ) (T : ℕ) :
    IsGreatest {r : ℝ | ∃ K : ℕ, ∃ c : ℕ → ℝ,
      r = 2 * (∑ j ∈ Icc 1 K, c j * finiteProbe b T j) - finiteSourceEnergy c K}
      (finiteProbeDualCost b T) := by
  constructor
  · obtain ⟨c, hc⟩ := (finiteSourceDualCost_isGreatest (finiteProbe b T) (T + 1)).1
    refine ⟨T + 1, c, ?_⟩
    rwa [finiteSourceDualCost_finiteProbe_succ] at hc
  · rintro r ⟨K, c, rfl⟩
    exact (finiteSourceEnergy_schur_bound c (finiteProbe b T) K).trans
      (finiteSourceDualCost_finiteProbe_le b T K)

/-- The maximizing source for a fixed probe is neutral after its one-coordinate extension. -/
theorem finiteProbe_maximizer_mass_zero (b : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Icc 1 (T + 1), finiteSourceMaximizer (finiteProbe b T) (T + 1) j) = 0 := by
  rw [finiteSourceMaximizer_mass]
  simp only [finiteProbe, if_neg (by omega : ¬ T + 1 ≤ T), mul_zero]

/-- Source and probe truncation have the same cost exactly when their weighted terminal trace vanishes. -/
theorem finiteProbeDualCost_eq_source_iff (b : ℕ → ℝ) (T : ℕ) :
    finiteProbeDualCost b T = finiteSourceDualCost b T ↔ (T : ℝ) * b T = 0 := by
  rw [finiteProbeDualCost, add_eq_left, sq_eq_zero_iff]

#print axioms finiteSourceDualCost_finiteProbe_stable
#print axioms hasSum_finiteSourceEnergy
#print axioms finiteProbeDualCost_isGreatest
#print axioms finiteProbe_maximizer_mass_zero
#print axioms finiteProbeDualCost_eq_source_iff

end GaloisForLFunctions.CompletedArithmeticForms
