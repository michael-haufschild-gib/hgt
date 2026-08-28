import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRootedEndpointSchedule
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPaperDilation

/-!
# Rooted minimal geometric source schedule

Full real geometric blocks stop at the first level above the literal natural root.  Internal
cutoffs are their natural endpoints; only initial and terminal endpoint collars remain.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Natural endpoint of the `j`-th exact geometric level. -/
def mtMinimalGeometricEndpoint (delta : ℝ) (start j : ℕ) : ℕ :=
  mtRealBlockEndpoint (mtGeometricLevel delta start) j

/-- First geometric exponent whose level lies strictly above a natural lower cutoff. -/
def mtFirstGeometricStart (delta : ℝ) (z₀ : ℕ) : ℕ :=
  adicIndex delta 1 (z₀ : ℝ) + 1

theorem mtFirstGeometricStart_bracket {delta : ℝ} (hdelta : 0 < delta)
    {z₀ : ℕ} (hz₀ : 1 ≤ z₀) :
    (z₀ : ℝ) < mtGeometricLevel delta (mtFirstGeometricStart delta z₀) 0 ∧
      mtGeometricLevel delta (mtFirstGeometricStart delta z₀) 0 ≤
        (z₀ : ℝ) * (1 + delta) := by
  have hblock := adicIndex_block hdelta (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) ≤ (z₀ : ℝ) by exact_mod_cast hz₀)
  constructor
  · simpa [mtFirstGeometricStart, mtGeometricLevel] using hblock.2
  · calc
      mtGeometricLevel delta (mtFirstGeometricStart delta z₀) 0 =
          (1 + delta) ^ (adicIndex delta 1 (z₀ : ℝ)) * (1 + delta) := by
        simp [mtFirstGeometricStart, mtGeometricLevel, pow_succ]
      _ ≤ (z₀ : ℝ) * (1 + delta) :=
        mul_le_mul_of_nonneg_right (by simpa using hblock.1) (by linarith)

theorem mtMinimalGeometricEndpoint_monotone {delta : ℝ} (hdelta : 0 < delta)
    (start : ℕ) : Monotone (mtMinimalGeometricEndpoint delta start) := by
  intro i j hij
  exact Nat.add_le_add_right
    (Nat.floor_mono ((mtGeometricLevel_strictMono hdelta start).monotone hij)) 1

/-- Exact geometric blocks with endpoint-aligned internal cutoffs and literal root cutoff. -/
def MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ)) :
    MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta) := by
  let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
  let endpoint := mtMinimalGeometricEndpoint delta start
  have hz₀Endpoint : z₀ ≤ endpoint 0 := by
    exact (Nat.le_floor hz₀).trans (Nat.le_add_right _ _)
  have hEndpointRoot : endpoint 0 ≤ z₁ := by
    have hfloor : Nat.floor (mtGeometricLevel delta start 0) < z₁ :=
      (Nat.floor_lt (mtGeometricLevel_pos hdelta start 0).le).mpr hroot
    dsimp [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    omega
  have hRootEndpoint : z₁ ≤ endpoint t := by
    have hspec := mtMinimalGeometricDepth_spec hdelta start (z₁ : ℝ)
    have hfloor : z₁ ≤ Nat.floor (mtGeometricLevel delta start t) :=
      Nat.le_floor hspec
    exact hfloor.trans (Nat.le_add_right _ _)
  exact MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
    z₀ D z₁ endpoint (mtMinimalGeometricEndpoint_monotone hdelta start)
    hz₀Endpoint hEndpointRoot hRootEndpoint

@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_block
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (i : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).block i =
      mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i := by
  rfl

@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_cutoff_last
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).cutoff
        (Fin.last (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta)) = z₁ := by
  simp [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule]

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_cutoff_le_root
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).cutoff j ≤ z₁ := by
  induction j using Fin.lastCases with
  | last => simp
  | cast i =>
      simp only [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule,
        MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_cutoff_castSucc]
      change mtMinimalGeometricEndpoint delta start i.1 ≤ z₁
      have hlevel := mtGeometricLevel_lt_of_lt_minimalDepth
        hdelta start (z₁ : ℝ) i.2
      have hfloor : Nat.floor (mtGeometricLevel delta start i.1) < z₁ :=
        (Nat.floor_lt (mtGeometricLevel_pos hdelta start i.1).le).mpr hlevel
      simp only [mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
      omega

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lowerSpill_subset
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lowerSpill j ⊆
        primesIco z₀ (mtMinimalGeometricEndpoint delta start 0) := by
  let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
  have ht : 0 < t := mtMinimalGeometricDepth_pos hdelta start hroot
  change mtAdjacentLowerSpill z₀ (mtMinimalGeometricEndpoint delta start)
      (mtRootedEndpointCutoff (mtMinimalGeometricEndpoint delta start) z₁) j ⊆ _
  rw [mtAdjacentLowerSpill]
  split
  · rename_i hj
    have hjzero : j = (0 : Fin (t + 1)) := Fin.ext hj
    subst j
    let i0 : Fin t := ⟨0, ht⟩
    have hcast : (0 : Fin (t + 1)) = i0.castSucc := Fin.ext rfl
    rw [hcast, mtRootedEndpointCutoff_castSucc]
  · exact Subset.rfl

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_upperSpill_subset
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).upperSpill j ⊆
        primesIco z₁ (mtMinimalGeometricEndpoint delta start
          (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta)) := by
  let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
  change mtAdjacentUpperSpill (mtMinimalGeometricEndpoint delta start)
      (mtRootedEndpointCutoff (mtMinimalGeometricEndpoint delta start) z₁) j ⊆ _
  rw [mtAdjacentUpperSpill]
  split
  · simp
  · induction j using Fin.lastCases with
    | last => simpa using
        (Subset.rfl : primesIco z₁
          (mtMinimalGeometricEndpoint delta start t) ⊆ _)
    | cast i => simp [primesIco]

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j k : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j =
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower k := by
  rfl

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_mem
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1))
    (i : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta)) {q : ℕ}
    (hq : q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j q =
        mtMinimalGeometricEndpoint delta start i.1 := by
  simp only [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule]
  apply MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_mem
  exact hq

theorem MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_lower_eq_of_not_mem
    (z₀ D start z₁ : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (j : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta + 1)) {q : ℕ}
    (hq : ¬ ∃ i : Fin (mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta),
      q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j q = z₀ := by
  simp only [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule]
  apply MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_not_mem
  exact hq

end

end RHTower.Sieve
