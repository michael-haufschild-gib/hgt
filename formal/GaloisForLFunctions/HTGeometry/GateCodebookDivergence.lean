import GaloisForLFunctions.HTGeometry.FirstShortestWordSelection

/-!
# Codebook divergence: low index entropy forces large synthesis divergence

A law supported on a finite set has entropy at most the logarithm of its size, because the
divergence against the uniform law on that set is the deficit.  Combining that maximum-entropy
bound with the exact gate-cost decomposition, a codebook of few words each of which is long must
pay a synthesis divergence at least the gate cost of the common length minus the index entropy.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section MaxEntropy

variable {α : Type*}

/-- The uniform law on a finite support. -/
theorem hasSum_uniform (s : Finset α) (hcard : 0 < s.card) :
    HasSum (condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ)) 1 := by
  classical
  have hsupp : ∀ w ∉ s, condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w = 0 := by
    intro w hw
    unfold condLaw
    rw [if_neg (by simpa using hw)]
  have hfin : HasSum (fun w : α => condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w)
      (∑ w ∈ s, condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w) :=
    hasSum_sum_of_ne_finset_zero hsupp
  have hval : (∑ w ∈ s, condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w) = 1 := by
    have hterm : ∀ w ∈ s, condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w =
        (s.card : ℝ)⁻¹ := by
      intro w hw
      unfold condLaw
      rw [if_pos (by simpa using hw), one_div]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hval] at hfin
  exact hfin

/-- **Maximum entropy.**  A law supported on a finite set has entropy at most the logarithm of the
size of that set. -/
theorem entropy_le_log_card {q : α → ℝ} (s : Finset α) (hcard : 0 < s.card)
    (hq : ∀ w, 0 ≤ q w) (hsupp : ∀ w, w ∉ (↑s : Set α) → q w = 0) (hqsum : HasSum q 1)
    (hsum : Summable fun w => q w * Real.log (q w))
    (hsum' : Summable fun w =>
      q w * Real.log (q w / condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ) w)) :
    entropy q ≤ Real.log (s.card : ℝ) := by
  classical
  have hone : ∀ w : α, (0 : ℝ) < (fun _ : α => (1 : ℝ)) w := fun _ => one_pos
  have hcardR : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard
  have hsplit : relEntropy q (fun _ : α => (1 : ℝ)) = -entropy q := by
    unfold relEntropy entropy
    rw [← tsum_neg]
    refine tsum_congr fun w => ?_
    rw [div_one]
    ring
  have hsumdiv : Summable fun w => q w * Real.log (q w / (fun _ : α => (1 : ℝ)) w) := by
    refine hsum.congr fun w => ?_
    rw [div_one]
  have hcond := relEntropy_condLaw (q := q) (p := fun _ : α => (1 : ℝ)) (↑s : Set α)
    hcardR hq hone hsupp hqsum hsumdiv
  have hnn := relEntropy_nonneg_of_absolutelyContinuous (q := q)
    (p := condLaw (fun _ : α => (1 : ℝ)) (↑s : Set α) (s.card : ℝ)) hq
    (condLaw_nonneg (fun w => (hone w).le) _ hcardR) ?_ hqsum (hasSum_uniform s hcard) hsum'
  · rw [hcond, hsplit] at hnn
    linarith
  · intro w hqw
    by_cases hw : w ∈ (↑s : Set α)
    · unfold condLaw
      rw [if_pos hw]
      exact div_pos one_pos hcardR
    · exact absurd (hsupp w hw) (ne_of_gt hqw)

end MaxEntropy

section Codebook

variable {Γ : Type*} [Fintype Γ]

omit [Fintype Γ] in
/-- A law whose words are all long has large expected length. -/
theorem le_expectedLength {q : List Γ → ℝ} {S : ℕ} (hq : ∀ w, 0 ≤ q w)
    (hlong : ∀ w, q w ≠ 0 → S ≤ w.length) (hqsum : HasSum q 1)
    (hsum : Summable fun w => q w * (w.length : ℝ)) :
    (S : ℝ) ≤ expectedLength q := by
  have hterm : ∀ w : List Γ, q w * (S : ℝ) ≤ q w * (w.length : ℝ) := by
    intro w
    by_cases hw : q w = 0
    · rw [hw]; simp
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlong w hw) (hq w)
  have hbase : HasSum (fun w : List Γ => q w * (S : ℝ)) (S : ℝ) := by
    have := hqsum.mul_right ((S : ℝ))
    simpa using this
  unfold expectedLength
  calc (S : ℝ) = ∑' w : List Γ, q w * (S : ℝ) := hbase.tsum_eq.symm
    _ ≤ ∑' w : List Γ, q w * (w.length : ℝ) := hbase.summable.tsum_le_tsum hterm hsum

/-- **`(21)`.**  A codebook of at most `N` words, each of length at least `S`, must pay a synthesis
divergence of at least the gate cost of `S` minus the index entropy. -/
theorem le_relEntropy_wordPrior_of_codebook {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hM : 0 < Fintype.card Γ) {q : List Γ → ℝ} {S : ℕ} (s : Finset (List Γ)) (hcard : 0 < s.card)
    (hq : ∀ w, 0 ≤ q w) (hsupp : ∀ w, w ∉ (↑s : Set (List Γ)) → q w = 0)
    (hlong : ∀ w, q w ≠ 0 → S ≤ w.length) (hqsum : HasSum q 1)
    (hlen : Summable fun w => q w * (w.length : ℝ))
    (hent : Summable fun w => q w * Real.log (q w))
    (hentU : Summable fun w =>
      q w * Real.log (q w / condLaw (fun _ : List Γ => (1 : ℝ)) (↑s : Set (List Γ))
        (s.card : ℝ) w))
    (hrel : Summable fun w => q w * Real.log (q w / wordPrior a w)) :
    (S : ℝ) * Real.log ((Fintype.card Γ : ℝ) / a) - Real.log (s.card : ℝ) -
        Real.log (1 - a) ≤ relEntropy q (wordPrior a) := by
  have hgate := gateCost_eq_entropy_add_relEntropy (Γ := Γ) ha ha1 hM hq hqsum hlen hent.neg hrel
  have hS := le_expectedLength hq hlong hqsum hlen
  have hH := entropy_le_log_card s hcard hq hsupp hqsum hent hentU
  have hlogpos : 0 ≤ Real.log ((Fintype.card Γ : ℝ) / a) := by
    have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
    have h1 : (1 : ℝ) ≤ (Fintype.card Γ : ℝ) / a := by
      rw [le_div_iff₀ ha]
      have : (1 : ℝ) ≤ (Fintype.card Γ : ℝ) := by exact_mod_cast hM
      nlinarith
    exact Real.log_nonneg h1
  nlinarith [hgate, hS, hH, hlogpos]

end Codebook

end

end GaloisForLFunctions.HTGeometry
