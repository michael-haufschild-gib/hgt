import GaloisForLFunctions.HTGeometry.ChamberLowerBound

/-!
# The chamber law at the extreme chambers

The two extreme chambers pin the grading.  In the all-positive chamber the grading is zero and the
Pick kernel admits no negative directions; in the all-negative chamber the grading is the full
dimension, and the scaled Gram is negative definite on the whole space at small heights.

The all-negative chamber sits at maximal Hamming distance from the positive one, so these two
statements are the endpoints of the distance grading.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset

noncomputable section

open scoped Classical ComplexOrder

/-- **The all-negative chamber has full grading.** -/
theorem negCount_eq_card_of_all_neg {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, c j < 0) :
    negCount c = d := by
  classical
  rw [negCount]
  have hfilter : (Finset.univ.filter fun j => c j < 0) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _
    exact hc j
  rw [hfilter]
  simp

/-- **The all-negative chamber is at maximal Hamming distance.** -/
theorem hammingDist_eq_card_of_all_neg {d : ℕ} (c : Fin d → ℝ) (hc : ∀ j, c j < 0) :
    hammingDist (signPattern c) (positiveChamber d) = d := by
  rw [← negCount_eq_hammingDist]
  exact negCount_eq_card_of_all_neg c hc

/-- **The chamber law in the all-negative chamber.**  With every inserted coefficient negative, the
scaled Pick Gram is negative definite on the whole space at small heights, so the negative index is
the full dimension — the Hamming distance of that chamber from the positive one. -/
theorem chamberLaw_all_negative {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0) :
    (∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0) ∧
      hammingDist (signPattern c) (positiveChamber d) = d := by
  refine ⟨eventually_negDef_totalGram_chamber ν a c ha hδ hc R hR hdom hatom, ?_⟩
  refine hammingDist_eq_card_of_all_neg c fun j => ?_
  exact lt_of_le_of_lt (hc j) (by linarith)

/-- **The positive chamber admits no negative directions.**  The zero of the grading, from the
upper bound. -/
theorem chamberLaw_all_positive {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (v : Fin (negCount c) → (Fin n → ℂ))
    (hPSD : (H + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W = 0 ∧ hammingDist (signPattern c) (positiveChamber d) = 0 := by
  refine ⟨no_neg_direction_of_mem_positiveChamber H c hc v hPSD W hW, ?_⟩
  rw [← negCount_eq_hammingDist]
  exact (negCount_eq_zero_iff c).2 hc

end

end GaloisForLFunctions.HTGeometry
