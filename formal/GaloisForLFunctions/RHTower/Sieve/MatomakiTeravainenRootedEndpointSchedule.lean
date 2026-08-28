import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricFallback

/-!
# Rooted endpoint cutoffs for exact geometric blocks

Internal recursive cutoffs use the natural block endpoints themselves.  The terminal cutoff is
the literal source endpoint.  This removes every internal rounding spill while preserving exact
real geometric blocks.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Natural block endpoints internally, literal source endpoint at the root. -/
def mtRootedEndpointCutoff {t : ℕ} (endpoint : ℕ → ℕ) (z₁ : ℕ) :
    Fin (t + 1) → ℕ :=
  Fin.lastCases z₁ (fun i => endpoint i.1)

@[simp] theorem mtRootedEndpointCutoff_last {t : ℕ}
    (endpoint : ℕ → ℕ) (z₁ : ℕ) :
    mtRootedEndpointCutoff (t := t) endpoint z₁ (Fin.last t) = z₁ := by
  simp [mtRootedEndpointCutoff]

@[simp] theorem mtRootedEndpointCutoff_castSucc {t : ℕ}
    (endpoint : ℕ → ℕ) (z₁ : ℕ) (i : Fin t) :
    mtRootedEndpointCutoff (t := t) endpoint z₁ i.castSucc = endpoint i.1 := by
  simp [mtRootedEndpointCutoff]

/-- Adjacent prime blocks with endpoint-aligned internal cutoffs and a literal root cutoff. -/
def MTFiniteIterationSourceData.ofRootedEndpointSchedule {t : ℕ}
    (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t) :
    MTFiniteIterationSourceData t := by
  apply MTFiniteIterationSourceData.ofAdjacentSchedule z₀ D endpoint
    (mtRootedEndpointCutoff endpoint z₁) hmono hz₀Endpoint
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using hz₀Endpoint.trans hEndpointRoot
    | cast i =>
        simp only [mtRootedEndpointCutoff_castSucc]
        exact hz₀Endpoint.trans (hmono (Nat.zero_le i.1))
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using hRootEndpoint
    | cast i => simp
  · intro i
    by_cases hlast : i.succ = Fin.last t
    · rw [hlast, mtRootedEndpointCutoff_last]
      exact hEndpointRoot
    · have hvalLt : i.succ.1 < t := by
        have hvalLe : i.succ.1 ≤ t := by omega
        exact lt_of_le_of_ne hvalLe (by
          intro heq
          apply hlast
          exact Fin.ext heq)
      let k : Fin t := ⟨i.succ.1, hvalLt⟩
      have hik : i.succ = k.castSucc := Fin.ext rfl
      rw [hik, mtRootedEndpointCutoff_castSucc]
      exact hmono (Nat.zero_le k.1)

/-- Totalize unused lower levels at the literal lower source endpoint. -/
def MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback {t : ℕ}
    (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t) :
    MTFiniteIterationSourceData t := by
  let cutoff := mtRootedEndpointCutoff (t := t) endpoint z₁
  let data := MTFiniteIterationSourceData.ofRootedEndpointSchedule
    z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint
  apply data.withLowerFallback (fun _ => z₀)
  intro j q hq
  have hprefix := mtAdjacentPrimeBlock_prefix_eq_source z₀ endpoint cutoff
    hmono hz₀Endpoint (by
      intro k
      induction k using Fin.lastCases with
      | last => simpa [cutoff] using hRootEndpoint
      | cast i => simp [cutoff]) (by
        intro i
        by_cases hlast : i.succ = Fin.last t
        · rw [hlast]
          simpa [cutoff] using hEndpointRoot
        · have hvalLt : i.succ.1 < t := by
            have hvalLe : i.succ.1 ≤ t := by omega
            exact lt_of_le_of_ne hvalLe (by
              intro heq
              apply hlast
              exact Fin.ext heq)
          let k : Fin t := ⟨i.succ.1, hvalLt⟩
          have hik : i.succ = k.castSucc := Fin.ext rfl
          rw [hik]
          simp only [cutoff, mtRootedEndpointCutoff_castSucc]
          exact hmono (Nat.zero_le k.1)) j
  have hqPrefix : q ∈ (mtBlockPrefix j).biUnion (mtAdjacentPrimeBlock endpoint) := by
    rw [hprefix]
    simpa [data, cutoff,
      MTFiniteIterationSourceData.ofRootedEndpointSchedule,
      MTFiniteIterationSourceData.ofAdjacentSchedule,
      MTFiniteIterationSourceData.ofPrefixUnion] using hq
  obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqPrefix
  exact ⟨i, by
    simpa [data, MTFiniteIterationSourceData.ofRootedEndpointSchedule,
      MTFiniteIterationSourceData.ofAdjacentSchedule,
      MTFiniteIterationSourceData.ofPrefixUnion] using hqi⟩

@[simp] theorem MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_block
    {t : ℕ} (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t) (i : Fin t) :
    (MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
      z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint).block i =
      mtAdjacentPrimeBlock endpoint i := by
  rfl

@[simp] theorem MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_cutoff_last
    {t : ℕ} (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t) :
    (MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
      z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint).cutoff
        (Fin.last t) = z₁ := by
  simp [MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback,
    MTFiniteIterationSourceData.withLowerFallback,
    MTFiniteIterationSourceData.ofRootedEndpointSchedule,
    MTFiniteIterationSourceData.ofAdjacentSchedule,
    MTFiniteIterationSourceData.ofPrefixUnion]

@[simp] theorem MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_cutoff_castSucc
    {t : ℕ} (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t) (i : Fin t) :
    (MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
      z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint).cutoff
        i.castSucc = endpoint i.1 := by
  simp [MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback,
    MTFiniteIterationSourceData.withLowerFallback,
    MTFiniteIterationSourceData.ofRootedEndpointSchedule,
    MTFiniteIterationSourceData.ofAdjacentSchedule,
    MTFiniteIterationSourceData.ofPrefixUnion]

theorem MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_mem
    {t : ℕ} (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t)
    (j : Fin (t + 1)) (i : Fin t) {q : ℕ}
    (hq : q ∈ mtAdjacentPrimeBlock endpoint i) :
    (MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
      z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint).lower j q =
        endpoint i.1 := by
  change (if h : ∃ k : Fin t, q ∈ mtAdjacentPrimeBlock endpoint k then
      mtBlockLower (mtAdjacentPrimeBlock endpoint)
        (mtRootedEndpointCutoff endpoint z₁) q else z₀) = endpoint i.1
  rw [dif_pos ⟨i, hq⟩]
  simpa using mtBlockLower_eq_of_mem (mtAdjacentPrimeBlock endpoint)
    (mtRootedEndpointCutoff endpoint z₁)
    (mtAdjacentPrimeBlock_disjoint endpoint hmono) i hq

theorem MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback_lower_eq_of_not_mem
    {t : ℕ} (z₀ D z₁ : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint)
    (hz₀Endpoint : z₀ ≤ endpoint 0)
    (hEndpointRoot : endpoint 0 ≤ z₁)
    (hRootEndpoint : z₁ ≤ endpoint t)
    (j : Fin (t + 1)) {q : ℕ}
    (hq : ¬ ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i) :
    (MTFiniteIterationSourceData.ofRootedEndpointScheduleWithFallback
      z₀ D z₁ endpoint hmono hz₀Endpoint hEndpointRoot hRootEndpoint).lower j q = z₀ := by
  change (if h : ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i then
      mtBlockLower (mtAdjacentPrimeBlock endpoint)
        (mtRootedEndpointCutoff endpoint z₁) q else z₀) = z₀
  rw [dif_neg hq]

end

end RHTower.Sieve
