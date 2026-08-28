import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricRooted

/-!
# Real-rooted minimal geometric source schedule

Geometric blocks stop at the literal real root, while the terminal natural sifting cutoff is its
ceiling.  Internal cutoffs remain aligned with block endpoints.  This simultaneously gives the
exact natural source condition `p < z` and the strict real Type-II scale bound `Q_i < z`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Endpoint-aligned geometric blocks indexed by a real root, with terminal cutoff `ceil z₁`. -/
def MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁) :
    MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta start z₁ hdelta) := by
  let t := mtMinimalGeometricDepth delta start z₁ hdelta
  let endpoint := mtMinimalGeometricEndpoint delta start
  have hz₀Endpoint : z₀ ≤ endpoint 0 := by
    exact (Nat.le_floor hz₀).trans (Nat.le_add_right _ _)
  have hEndpointRoot : endpoint 0 ≤ Nat.ceil z₁ := by
    have hfloor : Nat.floor (mtGeometricLevel delta start 0) < Nat.ceil z₁ :=
      (Nat.floor_lt (mtGeometricLevel_pos hdelta start 0).le).mpr
        (hroot.trans_le (Nat.le_ceil z₁))
    dsimp [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    omega
  have hRootEndpoint : Nat.ceil z₁ ≤ endpoint t := by
    have hspec := mtMinimalGeometricDepth_spec hdelta start z₁
    have hceil : Nat.ceil z₁ ≤ Nat.floor (mtGeometricLevel delta start t) + 1 := by
      apply (Nat.ceil_le).mpr
      have hfloor : mtGeometricLevel delta start t <
          ((Nat.floor (mtGeometricLevel delta start t) + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Nat.lt_floor_add_one (mtGeometricLevel delta start t)
      exact hspec.trans_lt hfloor |>.le
    simpa [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint] using hceil
  exact MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
    z₀ D (Nat.ceil z₁) endpoint (mtMinimalGeometricEndpoint_monotone hdelta start)
    hz₀Endpoint hEndpointRoot hRootEndpoint

@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_block
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (i : Fin (mtMinimalGeometricDepth delta start z₁ hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).block i =
      mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i := by
  rfl

@[simp] theorem
    MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_last
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).cutoff
        (Fin.last (mtMinimalGeometricDepth delta start z₁ hdelta)) = Nat.ceil z₁ := by
  simp [MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule]

theorem ofMinimalGeometricCeilRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
    (z₀ D start : ℕ) (z₁ : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).block =
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z₀ D start delta z₁ hdelta hz₀ hroot).block := by
  funext i
  rw [MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_block,
    MTFiniteIterationSourceData.ofMinimalGeometricSchedule_block]
  rfl

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_le_root
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).cutoff j ≤ Nat.ceil z₁ := by
  induction j using Fin.lastCases with
  | last => simp
  | cast i =>
      simp only [MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule,
        MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_cutoff_castSucc]
      have hlevel := mtGeometricLevel_lt_of_lt_minimalDepth
        hdelta start z₁ i.2
      have hfloor : Nat.floor (mtGeometricLevel delta start i.1) < Nat.ceil z₁ :=
        (Nat.floor_lt (mtGeometricLevel_pos hdelta start i.1).le).mpr
          (hlevel.trans_le (Nat.le_ceil z₁))
      simp only [mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
      omega

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lowerSpill_subset
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lowerSpill j ⊆
        primesIco z₀ (mtMinimalGeometricEndpoint delta start 0) := by
  let t := mtMinimalGeometricDepth delta start z₁ hdelta
  have ht : 0 < t := mtMinimalGeometricDepth_pos hdelta start hroot
  change mtAdjacentLowerSpill z₀ (mtMinimalGeometricEndpoint delta start)
      (mtRootedEndpointCutoff (mtMinimalGeometricEndpoint delta start) (Nat.ceil z₁)) j ⊆ _
  rw [mtAdjacentLowerSpill]
  split
  · rename_i hj
    have hjzero : j = (0 : Fin (t + 1)) := Fin.ext hj
    subst j
    let i0 : Fin t := ⟨0, ht⟩
    have hcast : (0 : Fin (t + 1)) = i0.castSucc := Fin.ext rfl
    rw [hcast, mtRootedEndpointCutoff_castSucc]
  · exact Subset.rfl

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_upperSpill_subset
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).upperSpill j ⊆
        primesIco (Nat.ceil z₁) (mtMinimalGeometricEndpoint delta start
          (mtMinimalGeometricDepth delta start z₁ hdelta)) := by
  let t := mtMinimalGeometricDepth delta start z₁ hdelta
  change mtAdjacentUpperSpill (mtMinimalGeometricEndpoint delta start)
      (mtRootedEndpointCutoff (mtMinimalGeometricEndpoint delta start) (Nat.ceil z₁)) j ⊆ _
  rw [mtAdjacentUpperSpill]
  split
  · simp
  · induction j using Fin.lastCases with
    | last =>
        simpa only [mtRootedEndpointCutoff_last, Fin.val_last] using
          (Subset.rfl : primesIco (Nat.ceil z₁)
            (mtMinimalGeometricEndpoint delta start t) ⊆ _)
    | cast i => simp [primesIco]

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j k : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j =
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower k := by
  rfl

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_mem
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1))
    (i : Fin (mtMinimalGeometricDepth delta start z₁ hdelta)) {q : ℕ}
    (hq : q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j q =
        mtMinimalGeometricEndpoint delta start i.1 := by
  simp only [MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule]
  apply MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_mem
  exact hq

theorem MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_lower_eq_of_not_mem
    (z₀ D start : ℕ) (z₁ delta : ℝ) (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z₁)
    (j : Fin (mtMinimalGeometricDepth delta start z₁ hdelta + 1)) {q : ℕ}
    (hq : ¬ ∃ i : Fin (mtMinimalGeometricDepth delta start z₁ hdelta),
      q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z₀ D start z₁ delta hdelta hz₀ hroot).lower j q = z₀ := by
  simp only [MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule]
  apply MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_not_mem
  exact hq

end

end RHTower.Sieve
