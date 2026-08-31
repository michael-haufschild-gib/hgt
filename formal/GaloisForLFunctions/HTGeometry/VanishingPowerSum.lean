import GaloisForLFunctions.HTGeometry.TwoSidedBalancing

/-!
# The Newton-polygon bound for a vanishing power sum

A relation `∑_{k ≤ m} α_k w^k = 0` with `w ≠ 0` and some `α_k ≠ 0` pins `‖w‖`:

```text
‖α_u‖ / ((m+1)‖α_v‖) ≤ ‖w‖^{v-u} ≤ (m+1)·‖α_u‖/‖α_v‖
```

for two indices `u < v` whose coefficients do not vanish.  The maximal term is nonzero — otherwise
every term, hence every coefficient, would vanish — so the balancing principle supplies a partner,
and the two-sided estimate follows.

Applied with `α_k = c_k(F(z))` and `w = F′(z)`, this converts an autonomous algebraic differential
relation into a comparison between `‖F′‖` and a power of `‖F‖`, which is what a growth argument
consumes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Newton-polygon bound for a vanishing power sum.**  A relation `∑ α_k w^k = 0` with some
`α_k ≠ 0` and `w ≠ 0` pins `‖w‖` to a power determined by two of the coefficients. -/
theorem exists_pow_between_of_vanishing_sum {m : ℕ} {α : ℕ → ℂ} {w : ℂ}
    (hw : w ≠ 0) (hrel : ∑ k ∈ Finset.range (m + 1), α k * w ^ k = 0)
    (hne : ∃ k, k ≤ m ∧ α k ≠ 0) :
    ∃ u v : ℕ, u < v ∧ v ≤ m ∧ α u ≠ 0 ∧ α v ≠ 0 ∧
      ‖α u‖ / (((m : ℝ) + 1) * ‖α v‖) ≤ ‖w‖ ^ (v - u) ∧
      ‖w‖ ^ (v - u) ≤ ((m : ℝ) + 1) * (‖α u‖ / ‖α v‖) := by
  classical
  set b : ℕ → ℂ := fun k => α k * w ^ k with hb
  have hnormb : ∀ k, ‖b k‖ = ‖α k‖ * ‖w‖ ^ k := by
    intro k
    rw [hb, norm_mul, norm_pow]
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  -- the maximal index
  obtain ⟨k, hkmem, hkmax⟩ :=
    (Finset.range (m + 1)).exists_max_image (fun i => ‖b i‖) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)
  -- the maximum is nonzero
  have hbk : b k ≠ 0 := by
    intro hzero
    obtain ⟨i, him, hi⟩ := hne
    have himem : i ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hbi : ‖b i‖ ≤ ‖b k‖ := hkmax i himem
    rw [hzero, norm_zero] at hbi
    have : b i = 0 := norm_eq_zero.mp (le_antisymm hbi (norm_nonneg _))
    rw [hb] at this
    exact hi (by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (pow_ne_zero i hw))
  obtain ⟨j, hjmem, hjk, hjbal⟩ := exists_ne_norm_le_card_mul hrel hkmem hbk
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  have hcard : ((Finset.range (m + 1)).card : ℝ) = (m : ℝ) + 1 := by
    rw [Finset.card_range]
    push_cast
    ring
  rw [hcard] at hjbal
  -- positivity of the two coefficients
  have hAk : 0 < ‖α k‖ := by
    rw [norm_pos_iff]
    intro hz
    apply hbk
    show α k * w ^ k = 0
    rw [hz, zero_mul]
  have hAj : 0 < ‖α j‖ := by
    rw [norm_pos_iff]
    intro hz
    have hbj0 : ‖α j * w ^ j‖ = 0 := by rw [hz, zero_mul, norm_zero]
    rw [hbj0, mul_zero] at hjbal
    have hbk0 : ‖α k * w ^ k‖ = 0 := le_antisymm hjbal (norm_nonneg _)
    exact hbk (norm_eq_zero.mp hbk0)
  have hmax' : ‖α j‖ * ‖w‖ ^ j ≤ ‖α k‖ * ‖w‖ ^ k := by
    rw [← hnormb, ← hnormb]
    exact hkmax j hjmem
  have hbal' : ‖α k‖ * ‖w‖ ^ k ≤ ((m : ℝ) + 1) * (‖α j‖ * ‖w‖ ^ j) := by
    rw [norm_mul, norm_pow, norm_mul, norm_pow] at hjbal
    exact hjbal
  obtain ⟨u, v, huv, hvm, hAu, hAv, hlow, hhigh⟩ :=
    exists_pow_between_of_balanced (A := fun i => ‖α i‖) hwn hkm hjm hjk hAk hAj hmax' hbal'
  refine ⟨u, v, huv, hvm, ?_, ?_, hlow, hhigh⟩
  · intro hz
    rw [hz, norm_zero] at hAu
    exact absurd hAu (lt_irrefl 0)
  · intro hz
    rw [hz, norm_zero] at hAv
    exact absurd hAv (lt_irrefl 0)

end GaloisForLFunctions.HTGeometry
