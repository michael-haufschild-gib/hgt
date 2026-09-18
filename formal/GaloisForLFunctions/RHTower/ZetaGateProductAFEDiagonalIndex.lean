import Mathlib

/-!
# Parametrising the diagonals of the block twisted moment

For coprime `h' k' ≥ 1` the solutions of `(m+1)·h' = (n+1)·k'` in `ℕ × ℕ` are exactly
`(m+1, n+1) = ((j+1)k', (j+1)h')`, `j ∈ ℕ`.  This module provides the injective parametrisation
`diagIndex h' k' j = ((j+1)k' − 1, (j+1)h' − 1)`, its range, and the resulting split of a summable
double series into its diagonal (reindexed by `ℕ`) and off-diagonal parts.  The dual diagonal
`(n+1)·h' = (m+1)·k'` is the same statement with the roles of `h'` and `k'` exchanged.
-/

open Set

namespace RHTower.ZetaGateProductAFE

/-- The diagonal parametrisation `j ↦ ((j+1)k' − 1, (j+1)h' − 1)`. -/
def diagIndex (h' k' : ℕ) (j : ℕ) : ℕ × ℕ := ((j + 1) * k' - 1, (j + 1) * h' - 1)

theorem diagIndex_fst_add_one {h' k' : ℕ} (hk' : 0 < k') (j : ℕ) :
    (diagIndex h' k' j).1 + 1 = (j + 1) * k' := by
  unfold diagIndex
  have : 1 ≤ (j + 1) * k' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only
  omega

theorem diagIndex_snd_add_one {h' k' : ℕ} (hh' : 0 < h') (j : ℕ) :
    (diagIndex h' k' j).2 + 1 = (j + 1) * h' := by
  unfold diagIndex
  have : 1 ≤ (j + 1) * h' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only
  omega

theorem diagIndex_injective {h' k' : ℕ} (hk' : 0 < k') :
    Function.Injective (diagIndex h' k') := by
  intro i j hij
  have h1 : (diagIndex h' k' i).1 + 1 = (diagIndex h' k' j).1 + 1 := by rw [hij]
  rw [diagIndex_fst_add_one hk', diagIndex_fst_add_one hk'] at h1
  have := Nat.eq_of_mul_eq_mul_right hk' h1
  omega

/-- The diagonal condition for the parametrised pairs. -/
theorem diagIndex_mem {h' k' : ℕ} (hh' : 0 < h') (hk' : 0 < k') (j : ℕ) :
    ((diagIndex h' k' j).1 + 1) * h' = ((diagIndex h' k' j).2 + 1) * k' := by
  rw [diagIndex_fst_add_one hk', diagIndex_snd_add_one hh']
  ring

/-- **Range of the diagonal parametrisation.** For coprime `h', k'` the solutions of
`(m+1)h' = (n+1)k'` are exactly the parametrised pairs. -/
theorem range_diagIndex {h' k' : ℕ} (hh' : 0 < h') (hk' : 0 < k') (hcop : Nat.Coprime h' k') :
    Set.range (diagIndex h' k') = {P : ℕ × ℕ | (P.1 + 1) * h' = (P.2 + 1) * k'} := by
  ext P
  constructor
  · rintro ⟨j, rfl⟩
    exact diagIndex_mem hh' hk' j
  · intro hP
    simp only [Set.mem_setOf_eq] at hP
    -- `k' ∣ (P.1 + 1)` since `k' ∣ (P.1+1) h'` and `gcd(k', h') = 1`
    have hdvd : k' ∣ (P.1 + 1) * h' := ⟨P.2 + 1, by rw [hP]; ring⟩
    have hk'dvd : k' ∣ P.1 + 1 := by
      have hcop' : Nat.Coprime k' h' := hcop.symm
      exact hcop'.dvd_of_dvd_mul_right hdvd
    obtain ⟨j', hj'⟩ := hk'dvd
    have hj'' : P.1 + 1 = j' * k' := by rw [hj', mul_comm]
    have hj'pos : 0 < j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · rw [h0, zero_mul] at hj''; omega
      · exact h0
    refine ⟨j' - 1, ?_⟩
    have hj'eq : j' - 1 + 1 = j' := Nat.sub_add_cancel hj'pos
    -- second coordinate
    have hsnd : (P.2 + 1) * k' = (j' * h') * k' := by
      rw [← hP, hj'']; ring
    have hsnd' : P.2 + 1 = j' * h' := Nat.eq_of_mul_eq_mul_right hk' hsnd
    unfold diagIndex
    rw [hj'eq]
    ext
    · show j' * k' - 1 = P.1
      omega
    · show j' * h' - 1 = P.2
      omega

/-- Split a summable double series into its diagonal part (reindexed by `ℕ`) and the rest. -/
theorem tsum_eq_tsum_diagIndex_add_compl {h' k' : ℕ} (hh' : 0 < h') (hk' : 0 < k')
    (hcop : Nat.Coprime h' k') {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    ∑' P, f P = (∑' j, f (diagIndex h' k' j))
      + ∑' P : ↥({P : ℕ × ℕ | (P.1 + 1) * h' = (P.2 + 1) * k'}ᶜ), f P := by
  have hs := hf.subtype {P : ℕ × ℕ | (P.1 + 1) * h' = (P.2 + 1) * k'}
  have hsc := hf.subtype ({P : ℕ × ℕ | (P.1 + 1) * h' = (P.2 + 1) * k'}ᶜ)
  rw [← Summable.tsum_add_tsum_compl (s := {P : ℕ × ℕ | (P.1 + 1) * h' = (P.2 + 1) * k'}) hs hsc]
  congr 1
  rw [← range_diagIndex hh' hk' hcop, tsum_range f (diagIndex_injective hk')]

end RHTower.ZetaGateProductAFE
