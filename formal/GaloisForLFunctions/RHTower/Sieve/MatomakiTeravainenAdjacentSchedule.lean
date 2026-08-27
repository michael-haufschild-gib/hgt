import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationSource

/-!
# Adjacent block schedules for Matomäki--Teräväinen Lemma 2.3(ii)

The source intervals `(Q, (1 + δ_A)Q]` are adjacent.  After passing to integer endpoints,
their prime sets have the form `[b_j,b_{j+1})`.  This file proves the exact finite partition,
including both endpoint spill sets from `c₂`, and packages it as iteration source data.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Prime block between two adjacent integer endpoints. -/
def mtAdjacentPrimeBlock {t : ℕ} (endpoint : ℕ → ℕ) (i : Fin t) : Finset ℕ :=
  primesIco (endpoint i.1) (endpoint (i.1 + 1))

/-- Lower endpoint spill.  At the empty prefix it removes the whole source interval. -/
def mtAdjacentLowerSpill {t : ℕ} (z₀ : ℕ) (endpoint : ℕ → ℕ)
    (cutoff : Fin (t + 1) → ℕ) (j : Fin (t + 1)) : Finset ℕ :=
  if j.1 = 0 then primesIco z₀ (cutoff j) else primesIco z₀ (endpoint 0)

/-- Upper endpoint spill caused by a cutoff lying below the right integer block endpoint. -/
def mtAdjacentUpperSpill {t : ℕ} (endpoint : ℕ → ℕ)
    (cutoff : Fin (t + 1) → ℕ) (j : Fin (t + 1)) : Finset ℕ :=
  if j.1 = 0 then ∅ else primesIco (cutoff j) (endpoint j.1)

/-- Adjacent prime blocks telescope exactly over every index prefix. -/
theorem mtAdjacentPrimeBlock_prefix_biUnion {t : ℕ} (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint) (j : Fin (t + 1)) :
    (mtBlockPrefix j).biUnion (mtAdjacentPrimeBlock endpoint) =
      primesIco (endpoint 0) (endpoint j.1) := by
  classical
  induction j using Fin.induction with
  | zero =>
      ext q
      simp [mtBlockPrefix, primesIco]
  | @succ i ih =>
      ext q
      constructor
      · intro hq
        obtain ⟨k, hkPrefix, hkBlock⟩ := Finset.mem_biUnion.mp hq
        have hklt : k.1 < i.1 + 1 := by
          simpa [mem_mtBlockPrefix] using hkPrefix
        by_cases hki : k.1 < i.1
        · have hqOld :
              q ∈ (mtBlockPrefix i.castSucc).biUnion (mtAdjacentPrimeBlock endpoint) :=
            Finset.mem_biUnion.mpr ⟨k, mem_mtBlockPrefix.mpr hki, hkBlock⟩
          have hqIco : q ∈ primesIco (endpoint 0) (endpoint i.1) := by
            simpa using
              (show q ∈ primesIco (endpoint 0) (endpoint i.castSucc.1) from by
                rw [← ih]
                exact hqOld)
          obtain ⟨hqLower, hqUpper, hqPrime⟩ := mem_primesIco.mp hqIco
          exact mem_primesIco.mpr
            ⟨hqLower, hqUpper.trans_le (hmono (Nat.le_succ i.1)), hqPrime⟩
        · have hkiEq : k = i := Fin.ext (by omega)
          subst k
          obtain ⟨hqLower, hqUpper, hqPrime⟩ :=
            mem_primesIco.mp hkBlock
          exact mem_primesIco.mpr
            ⟨(hmono (Nat.zero_le i.1)).trans hqLower, hqUpper, hqPrime⟩
      · intro hq
        obtain ⟨hqLower, hqUpper, hqPrime⟩ := mem_primesIco.mp hq
        by_cases hqBefore : q < endpoint i.1
        · have hqOld : q ∈ primesIco (endpoint 0) (endpoint i.1) :=
            mem_primesIco.mpr ⟨hqLower, hqBefore, hqPrime⟩
          have hqPrefix :
              q ∈ (mtBlockPrefix i.castSucc).biUnion (mtAdjacentPrimeBlock endpoint) := by
            rw [ih]
            exact hqOld
          obtain ⟨k, hk, hkBlock⟩ := Finset.mem_biUnion.mp hqPrefix
          exact Finset.mem_biUnion.mpr
            ⟨k, mem_mtBlockPrefix.mpr ((mem_mtBlockPrefix.mp hk).trans (Nat.lt_succ_self _)),
              hkBlock⟩
        · exact Finset.mem_biUnion.mpr
            ⟨i, mem_mtBlockPrefix.mpr (Nat.lt_succ_self _),
              mem_primesIco.mpr ⟨Nat.le_of_not_gt hqBefore, hqUpper, hqPrime⟩⟩

/-- Distinct adjacent blocks are disjoint. -/
theorem mtAdjacentPrimeBlock_disjoint {t : ℕ} (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint) (i k : Fin t) (hik : i ≠ k) :
    Disjoint (mtAdjacentPrimeBlock endpoint i) (mtAdjacentPrimeBlock endpoint k) := by
  apply Finset.disjoint_left.mpr
  intro q hqi hqk
  obtain ⟨hiLower, hiUpper, -⟩ := mem_primesIco.mp hqi
  obtain ⟨hkLower, hkUpper, -⟩ := mem_primesIco.mp hqk
  rcases lt_or_gt_of_ne (fun h => hik (Fin.ext h)) with hikVal | hkiVal
  · have hbound : endpoint (i.1 + 1) ≤ endpoint k.1 := hmono (by omega)
    omega
  · have hbound : endpoint (k.1 + 1) ≤ endpoint i.1 := hmono (by omega)
    omega

/-- Exact prefix identity with lower and upper endpoint spill sets. -/
theorem mtAdjacentPrimeBlock_prefix_eq_source {t : ℕ} (z₀ : ℕ)
    (endpoint : ℕ → ℕ) (cutoff : Fin (t + 1) → ℕ)
    (hmono : Monotone endpoint)
    (hendpoint₀ : z₀ ≤ endpoint 0)
    (hcutoffEndpoint : ∀ j, cutoff j ≤ endpoint j.1)
    (hendpointCutoff : ∀ i : Fin t, endpoint 0 ≤ cutoff i.succ)
    (j : Fin (t + 1)) :
    (mtBlockPrefix j).biUnion (mtAdjacentPrimeBlock endpoint) =
      (primesIco z₀ (cutoff j) \
          mtAdjacentLowerSpill z₀ endpoint cutoff j) ∪
        mtAdjacentUpperSpill endpoint cutoff j := by
  rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono j]
  induction j using Fin.cases with
  | zero =>
      ext q
      simp [mtAdjacentLowerSpill, mtAdjacentUpperSpill, primesIco]
  | succ i =>
      have hleft := hendpointCutoff i
      have hright := hcutoffEndpoint i.succ
      ext q
      rw [mtAdjacentLowerSpill, if_neg (by simp),
        mtAdjacentUpperSpill, if_neg (by simp)]
      simp only [mem_primesIco, Finset.mem_union, Finset.mem_sdiff,
        Fin.val_succ]
      constructor
      · rintro ⟨hqEndpoint, hqRight, hqPrime⟩
        by_cases hqCutoff : q < cutoff i.succ
        · exact Or.inl ⟨⟨by omega, hqCutoff, hqPrime⟩, by
            intro hqLow
            exact (not_lt_of_ge hqEndpoint) hqLow.2.1⟩
        · exact Or.inr ⟨Nat.le_of_not_gt hqCutoff, hqRight, hqPrime⟩
      · rintro (⟨⟨hqz₀, hqCutoff, hqPrime⟩, hqNotLow⟩ |
          ⟨hqCutoff, hqRight, hqPrime⟩)
        · have hqEndpoint : endpoint 0 ≤ q := by
            by_contra hnot
            apply hqNotLow
            exact ⟨hqz₀, Nat.lt_of_not_ge hnot, hqPrime⟩
          exact ⟨hqEndpoint, hqCutoff.trans_le hright, hqPrime⟩
        · exact ⟨hleft.trans hqCutoff, hqRight, hqPrime⟩

/-- Adjacent integer endpoints and source cutoffs give concrete finite iteration data. -/
def MTFiniteIterationSourceData.ofAdjacentSchedule {t : ℕ}
    (z₀ D : ℕ) (endpoint : ℕ → ℕ) (cutoff : Fin (t + 1) → ℕ)
    (hmono : Monotone endpoint)
    (hendpoint₀ : z₀ ≤ endpoint 0)
    (hcutoff : ∀ j, z₀ ≤ cutoff j)
    (hcutoffEndpoint : ∀ j, cutoff j ≤ endpoint j.1)
    (hendpointCutoff : ∀ i : Fin t, endpoint 0 ≤ cutoff i.succ) :
    MTFiniteIterationSourceData t := by
  apply MTFiniteIterationSourceData.ofPrefixUnion z₀ D
    (mtAdjacentPrimeBlock endpoint) cutoff
    (mtAdjacentLowerSpill z₀ endpoint cutoff)
    (mtAdjacentUpperSpill endpoint cutoff)
  · intro i q hq
    exact (mem_primesIco.mp hq).2.2
  · intro i q hq
    exact hendpoint₀.trans
      ((hmono (Nat.zero_le i.1)).trans (mem_primesIco.mp hq).1)
  · exact mtAdjacentPrimeBlock_disjoint endpoint hmono
  · exact hcutoff
  · intro j q hq
    induction j using Fin.cases with
    | zero => simpa [mtAdjacentLowerSpill] using hq
    | succ i =>
        rw [mtAdjacentLowerSpill, if_neg (by simp)] at hq
        obtain ⟨hqz₀, hqEndpoint, hqPrime⟩ := mem_primesIco.mp hq
        exact mem_primesIco.mpr
          ⟨hqz₀, hqEndpoint.trans_le (hendpointCutoff i), hqPrime⟩
  · intro j
    apply Finset.disjoint_left.mpr
    intro q hqBase hqUpper
    induction j using Fin.cases with
    | zero =>
        rw [mtAdjacentUpperSpill, if_pos (by simp)] at hqUpper
        simp at hqUpper
    | succ i =>
        rw [mtAdjacentUpperSpill, if_neg (by simp)] at hqUpper
        have hqBaseMem : q ∈ primesIco z₀ (cutoff i.succ) :=
          (Finset.mem_sdiff.mp hqBase).1
        have hqLt : q < cutoff i.succ := (mem_primesIco.mp hqBaseMem).2.1
        have hqGe : cutoff i.succ ≤ q := (mem_primesIco.mp hqUpper).1
        omega
  · exact mtAdjacentPrimeBlock_prefix_eq_source z₀ endpoint cutoff hmono
      hendpoint₀ hcutoffEndpoint hendpointCutoff

end

end RHTower.Sieve
