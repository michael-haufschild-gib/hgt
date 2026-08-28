import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGeometricSchedule

/-!
# Minimal exact geometric schedule for Proposition 2.2

The aligned natural schedule is ideal for eliminating rounding spills, but its final clipped
block need not be a literal interval `(Q, (1 + delta) Q]`.  Proposition 2.2's Type-II alternative
requires that literal block equality.  This file instead stops the source's exact geometric
schedule at its first level above the root cutoff.  Every preceding block is then exact and every
block lower scale lies strictly below the root cutoff.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

private theorem exists_geometricLevel_ge
    {delta : ℝ} (hdelta : 0 < delta) (start : ℕ) (z : ℝ) :
    ∃ j : ℕ, z ≤ mtGeometricLevel delta start j := by
  have htend : Filter.Tendsto (fun j : ℕ => (1 + delta) ^ j)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have hevent : ∀ᶠ j : ℕ in Filter.atTop, z ≤ (1 + delta) ^ j :=
    htend (Filter.eventually_ge_atTop z)
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨j, (hj j le_rfl).trans ?_⟩
  rw [mtGeometricLevel]
  exact pow_le_pow_right₀ (by linarith) (by omega : j ≤ start + j)

/-- First exact geometric level at or above the root cutoff. -/
def mtMinimalGeometricDepth
    (delta : ℝ) (start : ℕ) (z : ℝ) (hdelta : 0 < delta) : ℕ :=
  Nat.find (exists_geometricLevel_ge hdelta start z)

theorem mtMinimalGeometricDepth_spec
    {delta : ℝ} (hdelta : 0 < delta) (start : ℕ) (z : ℝ) :
    z ≤ mtGeometricLevel delta start
      (mtMinimalGeometricDepth delta start z hdelta) := by
  exact Nat.find_spec (exists_geometricLevel_ge hdelta start z)

theorem mtGeometricLevel_lt_of_lt_minimalDepth
    {delta : ℝ} (hdelta : 0 < delta) (start : ℕ) (z : ℝ)
    {j : ℕ} (hj : j < mtMinimalGeometricDepth delta start z hdelta) :
    mtGeometricLevel delta start j < z := by
  exact lt_of_not_ge (Nat.find_min (exists_geometricLevel_ge hdelta start z) hj)

theorem mtMinimalGeometricDepth_pos
    {delta : ℝ} (hdelta : 0 < delta) (start : ℕ) {z : ℝ}
    (hroot : mtGeometricLevel delta start 0 < z) :
    0 < mtMinimalGeometricDepth delta start z hdelta := by
  by_contra hzero
  have hdepth : mtMinimalGeometricDepth delta start z hdelta = 0 :=
    Nat.eq_zero_of_not_pos hzero
  have hspec := mtMinimalGeometricDepth_spec hdelta start z
  rw [hdepth] at hspec
  exact (not_le_of_gt hroot) hspec

theorem mtGeometricLevel_succ_eq
    (delta : ℝ) (start j : ℕ) :
    mtGeometricLevel delta start (j + 1) =
      mtGeometricLevel delta start j * (1 + delta) := by
  simp only [mtGeometricLevel]
  rw [show start + (j + 1) = start + j + 1 by omega, pow_succ]

/-- Source data using every full geometric block up to the first level bracketing `z`. -/
def MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    (z0 D start : ℕ) (delta z : ℝ) (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z) :
    MTFiniteIterationSourceData (mtMinimalGeometricDepth delta start z hdelta) :=
  MTFiniteIterationSourceData.ofGeometricSchedule z0 D start delta z hdelta hz0 hroot
    (mtMinimalGeometricDepth_spec hdelta start z)

@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricSchedule_block
    (z0 D start : ℕ) (delta z : ℝ) (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block i =
      mtAdjacentPrimeBlock
        (mtRealBlockEndpoint (mtGeometricLevel delta start)) i := by
  rfl

/-- Every block in the minimal schedule is exactly a source Type-II block. -/
theorem mem_ofMinimalGeometricSchedule_block_iff
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) (q : ℕ) :
    q ∈ (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i ↔
      q.Prime ∧ mtGeometricLevel delta start i.1 < (q : ℝ) ∧
        (q : ℝ) ≤ mtGeometricLevel delta start i.1 * (1 + delta) := by
  rw [MTFiniteIterationSourceData.ofMinimalGeometricSchedule_block,
    mem_mtAdjacentPrimeBlock_real_iff]
  · rw [mtGeometricLevel_succ_eq]
    tauto
  · exact fun j => (mtGeometricLevel_pos hdelta start j).le

/-- Every block lower scale in the minimal schedule lies in the literal source range. -/
theorem mtMinimalGeometricSchedule_scale_mem
    {delta z : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    mtGeometricLevel delta start 0 ≤ mtGeometricLevel delta start i.1 ∧
      mtGeometricLevel delta start i.1 < z := by
  exact ⟨(mtGeometricLevel_strictMono hdelta start).monotone (Nat.zero_le i.1),
    mtGeometricLevel_lt_of_lt_minimalDepth hdelta start z i.2⟩

/-- Root cutoff of the minimal schedule is the natural ceiling of the requested real cutoff. -/
@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricSchedule_cutoff_last
    (z0 D start : ℕ) (delta z : ℝ) (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z) :
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).cutoff
        (Fin.last (mtMinimalGeometricDepth delta start z hdelta)) = Nat.ceil z := by
  simp [MTFiniteIterationSourceData.ofMinimalGeometricSchedule,
    MTFiniteIterationSourceData.ofGeometricSchedule,
    MTFiniteIterationSourceData.ofRootedRealSchedule,
    MTFiniteIterationSourceData.ofRealAdjacentSchedule,
    MTFiniteIterationSourceData.ofAdjacentSchedule,
    MTFiniteIterationSourceData.ofPrefixUnion, mtRealSiftCutoff]

end

end RHTower.Sieve
