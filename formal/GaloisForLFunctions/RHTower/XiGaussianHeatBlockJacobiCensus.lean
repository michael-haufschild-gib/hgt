import GaloisForLFunctions.RHTower.XiGaussianHeatBlockInertia
import Mathlib.Data.ENat.Lattice

/-!
# An all-time block Jacobi census for the actual heat source

The first regular head after each regular head defines a canonical cofinal
partition of the moment ladder. Summing the block charges recovers the exact
negative inertia, even when intermediate determinants vanish. Its supremum
is the extended cardinality of the off-line frequency pairs at every positive
heat time, with no generic-time or nonzero-pivot hypothesis.
-/

open scoped BigOperators
open Matrix HTGeometry
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The first invertible head strictly after `n`. -/
def heatRegularHeadAfter (a : {t : ℝ // 0 < t}) (n : ℕ) : ℕ :=
  Nat.find (hcf_regular_heads_cofinal a (n + 1))

theorem heatRegularHeadAfter_spec (a : {t : ℝ // 0 < t}) (n : ℕ) :
    n < heatRegularHeadAfter a n ∧
      (momentHankelMatrix (heatRealMoments a) (heatRegularHeadAfter a n)).det ≠ 0 := by
  have h := Nat.find_spec (hcf_regular_heads_cofinal a (n + 1))
  exact ⟨h.1, h.2⟩

/-- Canonical enumeration of the regular heads, starting at the empty head. -/
def heatRegularHead (a : {t : ℝ // 0 < t}) : ℕ → ℕ
  | 0 => 0
  | j + 1 => heatRegularHeadAfter a (heatRegularHead a j)

theorem heatRegularHead_det_ne_zero (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (momentHankelMatrix (heatRealMoments a) (heatRegularHead a j)).det ≠ 0 := by
  cases j with
  | zero => simp [heatRegularHead]
  | succ j => exact (heatRegularHeadAfter_spec a _).2

theorem heatRegularHead_lt_succ (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularHead a j < heatRegularHead a (j + 1) := (heatRegularHeadAfter_spec a _).1

theorem le_heatRegularHead (a : {t : ℝ // 0 < t}) (j : ℕ) : j ≤ heatRegularHead a j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => have := heatRegularHead_lt_succ a j; omega

/-- Length of the `j`th canonical block. -/
def heatRegularGap (a : {t : ℝ // 0 < t}) (j : ℕ) : ℕ :=
  heatRegularHead a (j + 1) - heatRegularHead a j

theorem heatRegularHead_add_gap (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularHead a j + heatRegularGap a j = heatRegularHead a (j + 1) := by
  have := heatRegularHead_lt_succ a j
  unfold heatRegularGap
  omega

/-- Every canonical gap is a genuine normal block of the actual source. -/
theorem heatRegularGap_normalBlock (a : {t : ℝ // 0 < t}) (j : ℕ) :
    MomentNormalBlock (heatRealMoments a) (heatRegularHead a j) (heatRegularGap a j) := by
  obtain ⟨d, hd⟩ := exists_momentNormalBlock (nondegenerate_heatRealMoments a)
    (heatRegularHead_det_ne_zero a j)
  have hmin : heatRegularHead a (j + 1) ≤ heatRegularHead a j + d :=
    Nat.find_min' (hcf_regular_heads_cofinal a (heatRegularHead a j + 1))
      ⟨by have := hd.length_pos; omega, hd.next_regular⟩
  have hlt := heatRegularHead_lt_succ a j
  have he : heatRegularHead a (j + 1) = heatRegularHead a j + d := by
    by_contra hne
    have hz := hd.intermediate_singular (k := heatRegularGap a j)
      (by unfold heatRegularGap; omega) (by unfold heatRegularGap; omega)
    rw [heatRegularHead_add_gap] at hz
    exact heatRegularHead_det_ne_zero a (j + 1) hz
  have hgap : heatRegularGap a j = d := by unfold heatRegularGap; omega
  rwa [hgap]

/-- Every section belongs to an enumerated block. -/
theorem exists_heatRegularHead_cover (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) := by
  classical
  let P := fun j => heatRegularHead a j ≤ N
  let j := Nat.findGreatest P N
  have hj : P j := Nat.findGreatest_spec (Nat.zero_le N) (by simp [P, heatRegularHead])
  refine ⟨j, hj, ?_⟩
  by_contra h
  have hnext : P (j + 1) := by dsimp [P]; omega
  have hbound : j + 1 ≤ N := (le_heatRegularHead a (j + 1)).trans hnext
  exact Nat.findGreatest_is_greatest (P := P) (n := N) (k := j + 1)
    (by dsimp [j]; omega) hbound hnext

/-- The determinant-only census through `J` complete normal blocks. -/
def heatBlockCensus (a : {t : ℝ // 0 < t}) (J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range J, heatNormalBlockCharge a (heatRegularHead a j) (heatRegularGap a j)

/-- Exact Jacobi rule at every canonical head, including arbitrary singular gaps. -/
theorem hcf_block_jacobi_rule (a : {t : ℝ // 0 < t}) (J : ℕ) :
    hermNegIndex (heatMomentSection a (heatRegularHead a J)) = heatBlockCensus a J := by
  induction J with
  | zero =>
    change hermNegIndex (heatMomentSection a 0) = 0
    exact hermNegIndex_heatMomentSection_zero (a : ℝ)
  | succ J ih =>
    have h := heat_normal_block_charge a.property (heatRegularGap_normalBlock a J)
    rw [heatRegularHead_add_gap, ih] at h
    simpa only [heatBlockCensus, Finset.sum_range_succ] using h

/-- **Unconditional signature resolution at every section.** All three
indices are determined by canonical block lengths and endpoint determinant
signs; singular sections and their null directions are included. -/
theorem hcf_all_time_block_signature (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      hermPosIndex (heatMomentSection a N) =
        heatRegularHead a j - heatBlockCensus a j +
          (N - heatRegularHead a j -
            heatNormalBlockCharge a (heatRegularHead a j) (heatRegularGap a j)) ∧
      hermNegIndex (heatMomentSection a N) = heatBlockCensus a j +
        (N - heatRegularHead a j +
          heatNormalBlockCharge a (heatRegularHead a j) (heatRegularGap a j) - heatRegularGap a j) ∧
      hermNullIndex (heatMomentSection a N) =
        min (N - heatRegularHead a j) (heatRegularHead a (j + 1) - N) := by
  obtain ⟨j, hj, hj1⟩ := exists_heatRegularHead_cover a N
  have hblock := heatRegularGap_normalBlock a j
  have hgap := heatRegularHead_add_gap a j
  have hprofile := heat_normal_block_inertia a.property hblock
    (k := N - heatRegularHead a j) (by omega)
  have he : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
  rw [he, hcf_block_jacobi_rule] at hprofile
  have hsum := posIndex_add_negIndex_add_nullIndex
    (isHermitian_heatMomentSection a (heatRegularHead a j))
  have hnull := hblock.nullity (k := 0) (Nat.zero_le _)
  simp only [Nat.add_zero, Nat.zero_min] at hnull
  rw [hermNullIndex_heatMomentSection_eq, hnull, hcf_block_jacobi_rule] at hsum
  simp only [Fintype.card_fin, Nat.add_zero] at hsum
  refine ⟨j, hj, hj1, ?_, hprofile.2.1, ?_⟩
  · rw [hprofile.1]
    congr 1
    omega
  · rw [hprofile.2.2]
    congr 1
    omega

/-- **All-time off-line census.** The canonical block charges recover the
complete extended cardinality of the actual off-line frequency pairs. -/
theorem hcf_all_time_block_census (a : {t : ℝ // 0 < t}) :
    (⨆ J : ℕ, (heatBlockCensus a J : ℕ∞)) = xiUpperFrequencies.encard := by
  classical
  rcases xiUpperFrequencies.finite_or_infinite with hU | hU
  · rw [hU.encard_eq_coe_toFinset_card]
    apply le_antisymm
    · apply iSup_le
      intro J
      rw [← hcf_block_jacobi_rule]
      exact_mod_cast hermNegIndex_heatMomentSection_le a.property hU (heatRegularHead a J)
    · obtain ⟨N, hN⟩ := exists_hermNegIndex_heatMomentSection_eq a.property hU
      have he := hN (heatRegularHead a N) (le_heatRegularHead a N)
      rw [hcf_block_jacobi_rule] at he
      exact he ▸ le_iSup (fun J : ℕ => (heatBlockCensus a J : ℕ∞)) N
  · rw [hU.encard_eq]
    apply ENat.eq_top_iff_forall_ge.mpr
    intro m
    obtain ⟨N, hN⟩ := exists_le_hermNegIndex_heatMomentSection_of_infinite a.property hU m
    have hm := hN (heatRegularHead a N) (le_heatRegularHead a N)
    rw [hcf_block_jacobi_rule] at hm
    exact le_trans (by exact_mod_cast hm)
      (le_iSup (fun J : ℕ => (heatBlockCensus a J : ℕ∞)) N)

end
end RHTower
