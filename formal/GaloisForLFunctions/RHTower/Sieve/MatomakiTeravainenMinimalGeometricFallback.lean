import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGridFreePaperScale

/-!
# Totalized lower levels for the rooted geometric schedule

Prime levels outside the selected block union are irrelevant to the exact prefix kernel.  For the
rooted geometric schedule, totalizing those unused values at `z₀` makes the lower endpoint spill
compatible with the grid-free `c₃` estimate without changing any source identity or main box.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Replace unused lower-level values while preserving every exact source-data identity. -/
def MTFiniteIterationSourceData.withLowerFallback {t : ℕ}
    (data : MTFiniteIterationSourceData t) (fallback : ℕ → ℕ)
    (hsupport : ∀ j q,
      q ∈ (primesIco data.z₀ (data.cutoff j) \ data.lowerSpill j) ∪
          data.upperSpill j →
        ∃ i, q ∈ data.block i) :
    MTFiniteIterationSourceData t where
  z₀ := data.z₀
  D := data.D
  block := data.block
  cutoff := data.cutoff
  lowerSpill := data.lowerSpill
  upperSpill := data.upperSpill
  lower := fun j q => if ∃ i, q ∈ data.block i then data.lower j q else fallback q
  block_prime := data.block_prime
  block_lower := data.block_lower
  block_disjoint := data.block_disjoint
  cutoff_ge := data.cutoff_ge
  lower_subset := data.lower_subset
  spill_disjoint := data.spill_disjoint
  prefix_eq := by
    intro j
    rw [data.prefix_eq j]
    ext n
    by_cases hn : n = 0
    · subst n
      simp [mtBoundaryKernel]
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
      rw [mtBoundaryKernel_apply_of_pos _ _ hnPos,
        mtBoundaryKernel_apply_of_pos _ _ hnPos]
      apply Finset.sum_congr rfl
      intro q hq
      have hqSupport := hsupport j q hq
      simp [hqSupport]

/-- Minimal geometric source data with all unused lower levels totalized at the source cutoff. -/
def MTFiniteIterationSourceData.ofMinimalGeometricScheduleWithFallback
    (z0 D start : ℕ) (delta z : ℝ) (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z) :
    MTFiniteIterationSourceData (mtMinimalGeometricDepth delta start z hdelta) := by
  let t := mtMinimalGeometricDepth delta start z hdelta
  let Q := mtGeometricLevel delta start
  let W : Fin (t + 1) → ℝ := mtRootedRealCutoff Q z
  let endpoint := mtRealBlockEndpoint Q
  let cutoff := mtRealSiftCutoff W
  let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  apply data.withLowerFallback (fun _ => z0)
  intro j q hq
  have hQmono : Monotone Q := (mtGeometricLevel_strictMono hdelta start).monotone
  have hEndpointMono : Monotone endpoint := by
    intro a b hab
    exact Nat.add_le_add_right (Nat.floor_mono (hQmono hab)) 1
  have hEndpoint0 : z0 ≤ endpoint 0 := by
    exact (Nat.le_floor hz0).trans (Nat.le_add_right _ _)
  have hCutoffEndpoint : ∀ k, cutoff k ≤ endpoint k.1 := by
    intro k
    apply (Nat.ceil_le).mpr
    have hQfloor : Q k.1 < ((Nat.floor (Q k.1) + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Q k.1)
    have hWQ : W k ≤ Q k.1 := by
      induction k using Fin.lastCases with
      | last =>
          simpa [W, Q, t] using mtMinimalGeometricDepth_spec hdelta start z
      | cast i => simp [W, Q]
    exact hWQ.trans hQfloor.le
  have hEndpointCutoff : ∀ i : Fin t, endpoint 0 ≤ cutoff i.succ := by
    intro i
    have hQ0W : Q 0 < W i.succ := by
      by_cases hlast : i.succ = Fin.last t
      · rw [hlast]
        simpa [W] using hroot
      · have hvalLt : i.succ.1 < t := by
          have hvalLe : i.succ.1 ≤ t := by omega
          exact lt_of_le_of_ne hvalLe (by
            intro heq
            apply hlast
            exact Fin.ext heq)
        let k : Fin t := ⟨i.succ.1, hvalLt⟩
        have hik : i.succ = k.castSucc := Fin.ext rfl
        rw [hik]
        simp only [W, mtRootedRealCutoff_castSucc]
        exact mtGeometricLevel_strictMono hdelta start (by simp [k])
    have hfloorCeil : Nat.floor (Q 0) < Nat.ceil (W i.succ) :=
      (Nat.floor_lt (mtGeometricLevel_pos hdelta start 0).le).mpr
        (hQ0W.trans_le (Nat.le_ceil (W i.succ)))
    change Nat.floor (Q 0) + 1 ≤ Nat.ceil (W i.succ)
    omega
  have hprefix := mtAdjacentPrimeBlock_prefix_eq_source z0 endpoint cutoff
    hEndpointMono hEndpoint0 hCutoffEndpoint hEndpointCutoff j
  have hqPrefix : q ∈ (mtBlockPrefix j).biUnion (mtAdjacentPrimeBlock endpoint) := by
    rw [hprefix]
    simpa [data, MTFiniteIterationSourceData.ofMinimalGeometricSchedule,
      MTFiniteIterationSourceData.ofGeometricSchedule,
      MTFiniteIterationSourceData.ofRootedRealSchedule,
      MTFiniteIterationSourceData.ofRealAdjacentSchedule,
      MTFiniteIterationSourceData.ofAdjacentSchedule,
      MTFiniteIterationSourceData.ofPrefixUnion, Q, W, endpoint, cutoff] using hq
  obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqPrefix
  exact ⟨i, by
    simpa [data, MTFiniteIterationSourceData.ofMinimalGeometricSchedule,
      MTFiniteIterationSourceData.ofGeometricSchedule,
      MTFiniteIterationSourceData.ofRootedRealSchedule,
      MTFiniteIterationSourceData.ofRealAdjacentSchedule,
      MTFiniteIterationSourceData.ofAdjacentSchedule,
      MTFiniteIterationSourceData.ofPrefixUnion, Q, endpoint] using hqi⟩

@[simp] theorem MTFiniteIterationSourceData.ofMinimalGeometricScheduleWithFallback_block
    (z0 D start : ℕ) (delta z : ℝ) (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricScheduleWithFallback
      z0 D start delta z hdelta hz0 hroot).block i =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i := by
  rfl

end

end RHTower.Sieve
