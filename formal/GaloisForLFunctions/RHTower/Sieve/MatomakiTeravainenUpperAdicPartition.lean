import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTruncLegendreFactor

/-!
# Upper-closed `(1+δ)`-adic partitions

Proposition 2.2 uses intervals `(M,(1+δ)M]`, opposite to the endpoint convention of the prime
schedule.  Minimal power indices give an exact finite partition with this upper-closed convention.
-/

namespace RHTower.Sieve

open Filter Finset ArithmeticFunction

noncomputable section

private theorem exists_le_one_add_pow (δ : ℝ) (m : ℕ) (hδ : 0 < δ) :
    ∃ j : ℕ, (m : ℝ) ≤ (1 + δ) ^ j := by
  have htend : Tendsto (fun j : ℕ => (1 + δ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have hevent : ∀ᶠ j : ℕ in atTop, (m : ℝ) ≤ (1 + δ) ^ j :=
    htend (eventually_ge_atTop (m : ℝ))
  obtain ⟨j, hj⟩ := eventually_atTop.mp hevent
  exact ⟨j, hj j le_rfl⟩

/-- Least power of `1+δ` lying above a positive integer. -/
def mtUpperAdicIndex (δ : ℝ) (m : ℕ) : ℕ :=
  if hδ : 0 < δ then Nat.find (exists_le_one_add_pow δ m hδ) else 0

/-- Lower endpoint of the upper-closed block with index `j`.  Index zero is the block
`((1+δ)⁻¹,1]`. -/
def mtUpperAdicScale (δ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then (1 + δ)⁻¹ else (1 + δ) ^ (j - 1)

private theorem mtUpperAdicIndex_eq_find
    (δ : ℝ) (m : ℕ) (hδ : 0 < δ) :
    mtUpperAdicIndex δ m = Nat.find (exists_le_one_add_pow δ m hδ) := by
  simp [mtUpperAdicIndex, hδ]

theorem mtUpperAdicIndex_spec
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ≤ (1 + δ) ^ mtUpperAdicIndex δ m := by
  rw [mtUpperAdicIndex_eq_find δ m hδ]
  exact Nat.find_spec (exists_le_one_add_pow δ m hδ)

theorem mtUpperAdicIndex_mono
    {δ : ℝ} (hδ : 0 < δ) {m M : ℕ} (hmM : m ≤ M) :
    mtUpperAdicIndex δ m ≤ mtUpperAdicIndex δ M := by
  rw [mtUpperAdicIndex_eq_find δ m hδ, mtUpperAdicIndex_eq_find δ M hδ]
  apply Nat.find_min' (exists_le_one_add_pow δ m hδ)
  have hmMR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hspec := mtUpperAdicIndex_spec hδ M
  rw [mtUpperAdicIndex_eq_find δ M hδ] at hspec
  exact hmMR.trans hspec

theorem mtUpperAdicIndex_one {δ : ℝ} (hδ : 0 < δ) :
    mtUpperAdicIndex δ 1 = 0 := by
  rw [mtUpperAdicIndex_eq_find δ 1 hδ]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (exists_le_one_add_pow δ 1 hδ) (by simp))

/-- Every positive integer lies in its exact upper-closed adic block. -/
theorem mtUpperAdicIndex_block
    {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    mtUpperAdicScale δ (mtUpperAdicIndex δ m) < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ (mtUpperAdicIndex δ m) := by
  let j := mtUpperAdicIndex δ m
  have hupper : (m : ℝ) ≤ (1 + δ) ^ j := mtUpperAdicIndex_spec hδ m
  change mtUpperAdicScale δ j < (m : ℝ) ∧
    (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
  by_cases hj : j = 0
  · have hmOne : (m : ℝ) = 1 := by
      have : (m : ℝ) ≤ 1 := by simpa [j, hj] using hupper
      exact le_antisymm this (by exact_mod_cast hm)
    have hbase : 0 < 1 + δ := by linarith
    constructor
    · simpa [mtUpperAdicScale, hj, hmOne] using
        (inv_lt_one_of_one_lt₀ (by linarith : 1 < 1 + δ))
    · simp [mtUpperAdicScale, hj, hmOne, hbase.ne']
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hminimal : ¬(m : ℝ) ≤ (1 + δ) ^ k := by
      have hindexEq : mtUpperAdicIndex δ m = k + 1 := by simpa [j] using hk
      have hklt : k < Nat.find (exists_le_one_add_pow δ m hδ) := by
        rw [← mtUpperAdicIndex_eq_find δ m hδ, hindexEq]
        exact Nat.lt_succ_self k
      exact Nat.find_min (exists_le_one_add_pow δ m hδ) hklt
    constructor
    · simpa [mtUpperAdicScale, j, hk] using lt_of_not_ge hminimal
    · simpa [mtUpperAdicScale, j, hk, pow_succ, mul_comm] using hupper

/-- Membership in an upper-closed block is equivalent to equality of minimal power indices. -/
theorem mtUpperAdicIndex_eq_iff
    {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    mtUpperAdicIndex δ m = j ↔
      mtUpperAdicScale δ j < (m : ℝ) ∧
        (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j := by
  constructor
  · rintro rfl
    exact mtUpperAdicIndex_block hδ hm
  · intro hblock
    by_cases hj : j = 0
    · subst j
      have hmLeOne : (m : ℝ) ≤ 1 := by
        simpa [mtUpperAdicScale, (by linarith : (1 + δ) ≠ 0)] using hblock.2
      have hmNat : m ≤ 1 := by exact_mod_cast hmLeOne
      have hmEq : m = 1 := Nat.le_antisymm hmNat hm
      simpa [hmEq] using mtUpperAdicIndex_one hδ
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hlower : (1 + δ) ^ k < (m : ℝ) := by
        simpa [mtUpperAdicScale] using hblock.1
      have hupper : (m : ℝ) ≤ (1 + δ) ^ (k + 1) := by
        simpa [mtUpperAdicScale, pow_succ, mul_comm] using hblock.2
      have hindexUpper : mtUpperAdicIndex δ m ≤ k + 1 := by
        rw [mtUpperAdicIndex_eq_find δ m hδ]
        exact Nat.find_min' (exists_le_one_add_pow δ m hδ) hupper
      have hindexLower : k < mtUpperAdicIndex δ m := by
        apply Nat.lt_of_not_ge
        intro hle
        have hpow : (1 + δ) ^ mtUpperAdicIndex δ m ≤ (1 + δ) ^ k :=
          pow_le_pow_right₀ (by linarith) hle
        linarith [mtUpperAdicIndex_spec hδ m]
      omega

/-- Exact constant-one coefficient on one upper-closed adic block. -/
def mtUpperAdicOneAF (δ : ℝ) (j : ℕ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF (fun _ => 1) (mtUpperAdicScale δ j)
    ((1 + δ) * mtUpperAdicScale δ j)

/-- Every positive coefficient through `M` occurs in exactly one finite upper-closed adic block. -/
theorem sum_mtUpperAdicOneAF_apply
    {δ : ℝ} (hδ : 0 < δ) {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    (∑ j ∈ Finset.range (mtUpperAdicIndex δ M + 1), mtUpperAdicOneAF δ j) m = 1 := by
  rw [arithmeticFunction_finset_sum_apply]
  have hindexMem : mtUpperAdicIndex δ m ∈
      Finset.range (mtUpperAdicIndex δ M + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact mtUpperAdicIndex_mono hδ hmM
  calc
    ∑ j ∈ Finset.range (mtUpperAdicIndex δ M + 1), (mtUpperAdicOneAF δ j) m =
        (mtUpperAdicOneAF δ (mtUpperAdicIndex δ m)) m := by
      apply Finset.sum_eq_single (mtUpperAdicIndex δ m)
      · intro j hj hne
        rw [mtUpperAdicOneAF, mtRealIntervalAF_apply_of_pos _ _ _ hm]
        by_cases hblock : mtUpperAdicScale δ j < (m : ℝ) ∧
            (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
        · exact (hne ((mtUpperAdicIndex_eq_iff hδ hm j).2 hblock).symm).elim
        · simp [hblock]
      · intro hnot
        exact (hnot hindexMem).elim
    _ = 1 := by
      rw [mtUpperAdicOneAF, mtRealIntervalAF_apply_of_pos _ _ _ hm]
      simp [(mtUpperAdicIndex_eq_iff hδ hm (mtUpperAdicIndex δ m)).1 rfl]

end

end RHTower.Sieve
