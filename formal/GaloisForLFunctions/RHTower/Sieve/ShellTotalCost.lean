import GaloisForLFunctions.RHTower.Sieve.ShellAssembly

/-!
# The total shell cost

Cutting the shell range at the index where the uniform and the geometric shell bounds cross costs a
logarithm.  The cut index is `log(y/L) + O(1)`, where `y` is the scale carried by the geometric
bound and `L` the size of the uniform one; at that index the geometric tail is already of size `L`,
so the total is `(uniform bound)·(cut index) + O(L)` — this is the shape of the Halász exponent.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The crossing index of the two shell bounds. -/
theorem exists_cut_index {L y : ℝ} (hL : 0 < L) (hy : 0 < y) :
    ∃ K₀ : ℕ, Real.exp (-(K₀ : ℝ)) ≤ L / y ∧ (K₀ : ℝ) ≤ max 0 (Real.log (y / L)) + 1 := by
  rcases le_or_gt y L with hcase | hcase
  · refine ⟨0, ?_, ?_⟩
    · rw [Nat.cast_zero, neg_zero, Real.exp_zero, le_div_iff₀ hy]
      linarith
    · have : (0 : ℝ) ≤ max 0 (Real.log (y / L)) := le_max_left _ _
      simpa using by linarith
  · have hyL : (1 : ℝ) < y / L := by rw [lt_div_iff₀ hL]; linarith
    have hlog : (0 : ℝ) < Real.log (y / L) := Real.log_pos hyL
    refine ⟨⌈Real.log (y / L)⌉₊, ?_, ?_⟩
    · have hge : Real.log (y / L) ≤ (⌈Real.log (y / L)⌉₊ : ℝ) := Nat.le_ceil _
      have hstep : Real.exp (-(⌈Real.log (y / L)⌉₊ : ℝ)) ≤ Real.exp (-Real.log (y / L)) :=
        Real.exp_le_exp.2 (by linarith)
      have hid : Real.exp (-Real.log (y / L)) = L / y := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
      rw [hid] at hstep
      exact hstep
    · have hceil : (⌈Real.log (y / L)⌉₊ : ℝ) < Real.log (y / L) + 1 :=
        Nat.ceil_lt_add_one hlog.le
      have : Real.log (y / L) ≤ max 0 (Real.log (y / L)) := le_max_right _ _
      linarith

/-- **Equation (H1): the total shell cost.**  The uniform bound is paid `K₀` times and the
geometric tail contributes a further `O(L)`. -/
theorem shell_total_le {A B x L y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hL : 0 < L) (hy : 0 < y) {S : ℕ → ℝ}
    (hu : ∀ k, S k ≤ A * x * (L + 1))
    (hg : ∀ k, S k ≤ B * x * y * Real.exp (-(k : ℝ))) (K : ℕ) :
    ∃ K₀ : ℕ, (K₀ : ℝ) ≤ max 0 (Real.log (y / L)) + 1 ∧
      ∑ k ∈ Finset.range K, S k
        ≤ A * x * (L + 1) * (K₀ : ℝ) + 2 * B * x * L := by
  obtain ⟨K₀, hexp, hK₀⟩ := exists_cut_index hL hy
  refine ⟨K₀, hK₀, ?_⟩
  have hc₁ : (0 : ℝ) ≤ A * x * (L + 1) := by positivity
  have hc₂ : (0 : ℝ) ≤ B * x * y := by positivity
  have hbase := shell_assembly_le hc₁ hc₂ hu hg K₀ K
  refine hbase.trans ?_
  have htail : 2 * (B * x * y) * Real.exp (-(K₀ : ℝ)) ≤ 2 * B * x * L := by
    have hmul : (B * x * y) * Real.exp (-(K₀ : ℝ)) ≤ (B * x * y) * (L / y) :=
      mul_le_mul_of_nonneg_left hexp hc₂
    have hid : (B * x * y) * (L / y) = B * x * L := by
      field_simp
    rw [hid] at hmul
    linarith
  linarith

end

end RHTower.Sieve
