import GaloisForLFunctions.RHTower.Sieve.BlockProductLevelSplit
import GaloisForLFunctions.HTGeometry.CellMaxSetDiscretisation

/-!
# The level sets of a prime block, sampled at one-spaced frequencies

`integral_normSq_blockProduct_levelSplit` reduces the mean square of a bilinear block to the
cofactor's mean square over the level sets

```text
    S_V = { w ∈ [-G, G] : V ≤ ‖primeBlockPoly B w‖ } .
```

Every large-values estimate in the corpus — Halász–Montgomery, Huxley, Montgomery's counting bound —
is stated for a **one-spaced finite set of frequencies**, not for an integral over a level set, so
the missing step is a discretisation whose sample points lie *in* the level set.

The level set is closed: `primeBlockPoly` is continuous, so `S_V` is the intersection of a compact
interval with the preimage of a closed half-line.  `exists_spaced_families_setIntegral_le` therefore
applies verbatim, and produces two one-spaced families inside `S_V` carrying the whole integral at
the cost of a factor two.

* `isClosed_primeBlockLevelSet`;
* `exists_spaced_families_levelSet_le` — the discretisation.
-/

namespace RHTower.Sieve

open Finset MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- The frequencies of a window at which a prime block polynomial is at least `V`. -/
def primeBlockLevelSet (B : Finset ℕ) (G V : ℝ) : Set ℝ :=
  Set.Icc (-G) G ∩ {w | V ≤ ‖primeBlockPoly B w‖}

theorem isClosed_primeBlockLevelSet (B : Finset ℕ) (G V : ℝ) :
    IsClosed (primeBlockLevelSet B G V) :=
  isClosed_Icc.inter (isClosed_le continuous_const (continuous_primeBlockPoly B).norm)

theorem primeBlockLevelSet_subset (B : Finset ℕ) (G V : ℝ) :
    primeBlockLevelSet B G V ⊆ Set.Icc (-G) G := Set.inter_subset_left

/-- **The level-set mean square, sampled at one-spaced frequencies.**  The cofactor's mean square
over the level set is at most the sum of its values over two one-spaced finite families of
frequencies, both contained in the level set. -/
theorem exists_spaced_families_levelSet_le (a : ℕ → ℂ) (D B : Finset ℕ) {G : ℝ} (hG : 0 ≤ G)
    (V : ℝ) :
    ∃ P₁ P₂ : Finset ℝ,
      (∀ w ∈ P₁, w ∈ primeBlockLevelSet B G V)
      ∧ (∀ w ∈ P₂, w ∈ primeBlockLevelSet B G V)
      ∧ (∀ w ∈ P₁, ∀ u ∈ P₁, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∀ w ∈ P₂, ∀ u ∈ P₂, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∫ w in primeBlockLevelSet B G V, ‖logPoly a D w‖ ^ (2 : ℕ))
          ≤ (∑ w ∈ P₁, ‖logPoly a D w‖ ^ (2 : ℕ)) + ∑ w ∈ P₂, ‖logPoly a D w‖ ^ (2 : ℕ) := by
  classical
  set F : ℝ → ℝ := fun w => ‖logPoly a D w‖ ^ (2 : ℕ) with hF
  have hFcont : Continuous F := ((continuous_logPoly a D).norm).pow 2
  have hF0 : ∀ w, 0 ≤ F w := fun w => sq_nonneg _
  set U : Set ℝ := primeBlockLevelSet B G V with hU
  set m : ℕ := ⌈2 * G⌉₊ + 3 with hm
  have hmge : 2 * G + 3 ≤ (m : ℝ) := by
    have := Nat.le_ceil (2 * G)
    push_cast [hm]
    linarith
  obtain ⟨S₁, S₂, hS₁sub, hS₂sub, hS₁sep, hS₂sep, hdisc⟩ :=
    exists_spaced_families_setIntegral_le hFcont hF0 (isClosed_primeBlockLevelSet B G V)
      (-G - 1) 1 one_pos m
  have hcover : U ∩ Set.Ioc (-G - 1) (-G - 1 + (m : ℝ) * 1) = U := by
    refine Set.inter_eq_left.mpr fun w hw => ?_
    have h := primeBlockLevelSet_subset B G V hw
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hcover] at hdisc
  refine ⟨S₁, S₂, fun w hw => (hS₁sub (Finset.mem_coe.mpr hw)).1,
    fun w hw => (hS₂sub (Finset.mem_coe.mpr hw)).1, hS₁sep, hS₂sep, ?_⟩
  refine hdisc.trans (le_of_eq ?_)
  rw [one_mul]

/-- **The bilinear block, split by level and sampled at one-spaced frequencies.**  Combining the
dyadic level split with the level-set discretisation, the mean square of a bilinear block is the
base level times the cofactor's mean square plus, for each dyadic level, the cofactor's values at
two one-spaced families of frequencies *inside that level set*.  This is the exact shape the
Halász–Montgomery and Huxley large-values estimates consume. -/
theorem exists_spaced_families_blockProduct_levelSplit (a : ℕ → ℂ) (B D : Finset ℕ) {G : ℝ}
    (hG : 0 ≤ G) {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀) :
    ∃ P₁ P₂ : ℕ → Finset ℝ,
      (∀ j, ∀ w ∈ P₁ j, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
      ∧ (∀ j, ∀ w ∈ P₂ j, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
      ∧ (∀ j, ∀ w ∈ P₁ j, ∀ u ∈ P₁ j, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∀ j, ∀ w ∈ P₂ j, ∀ u ∈ P₂ j, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
          ≤ V₀ ^ (2 : ℕ) * (∫ w in Set.Icc (-G) G, ‖logPoly a D w‖ ^ (2 : ℕ))
            + ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
                ((∑ w ∈ P₁ j, ‖logPoly a D w‖ ^ (2 : ℕ)) + ∑ w ∈ P₂ j, ‖logPoly a D w‖ ^ (2 : ℕ)) := by
  classical
  have hlevel : ∀ j : ℕ, ∃ Q : Finset ℝ × Finset ℝ,
      (∀ w ∈ Q.1, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
        ∧ (∀ w ∈ Q.2, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
        ∧ (∀ w ∈ Q.1, ∀ u ∈ Q.1, w ≠ u → (1 : ℝ) ≤ |w - u|)
        ∧ (∀ w ∈ Q.2, ∀ u ∈ Q.2, w ≠ u → (1 : ℝ) ≤ |w - u|)
        ∧ (∫ w in primeBlockLevelSet B G (2 ^ j * V₀), ‖logPoly a D w‖ ^ (2 : ℕ))
            ≤ (∑ w ∈ Q.1, ‖logPoly a D w‖ ^ (2 : ℕ)) + ∑ w ∈ Q.2, ‖logPoly a D w‖ ^ (2 : ℕ) := by
    intro j
    obtain ⟨R₁, R₂, h₁, h₂, h₃, h₄, h₅⟩ :=
      exists_spaced_families_levelSet_le a D B hG (2 ^ j * V₀)
    exact ⟨(R₁, R₂), h₁, h₂, h₃, h₄, h₅⟩
  choose Q hQ₁ hQ₂ hQ₃ hQ₄ hQ₅ using hlevel
  refine ⟨fun j => (Q j).1, fun j => (Q j).2, hQ₁, hQ₂, hQ₃, hQ₄, ?_⟩
  refine (integral_normSq_blockProduct_levelSplit a B D hV₀ hJ).trans ?_
  have hsum : ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
        (∫ w in Set.Icc (-G) G ∩ {w | 2 ^ j * V₀ ≤ ‖primeBlockPoly B w‖},
          ‖logPoly a D w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
        ((∑ w ∈ (Q j).1, ‖logPoly a D w‖ ^ (2 : ℕ)) + ∑ w ∈ (Q j).2, ‖logPoly a D w‖ ^ (2 : ℕ)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hQ₅ j) (sq_nonneg _)
  linarith [hsum]

end

end RHTower.Sieve
