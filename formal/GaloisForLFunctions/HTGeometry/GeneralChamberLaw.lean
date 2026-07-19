import GaloisForLFunctions.HTGeometry.ChamberLawEquality

/-!
# The chamber law in a general chamber

The extreme chambers pin the two endpoints of the grading; between them the coefficient diagonal is
indefinite, so negative definiteness can only hold on the negative coordinates.  There it does: the
scaled Gram converges entrywise to the coefficient diagonal, and on vectors supported in the
negative coordinates the diagonal carries the margin of those coefficients alone.

Combining that lower bound with the inertia upper bound gives the chamber law at every chamber, with
the grading read as the Hamming distance from the positive chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset

noncomputable section

open scoped Classical ComplexOrder

/-- **Entrywise convergence gives eventual negative definiteness on the negative coordinates.**
Only the negative coefficients need the margin, because a vector supported in those coordinates
does not see the others. -/
theorem eventually_negDef_on_negSupported_of_entrywise
    {n : ℕ} {ι : Type*} {l : Filter ι} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ j k,
      ‖G i j k - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) j k‖ ≤ ε) :
    ∀ᶠ i in l, ∀ x ∈ negSupported c, x ≠ 0 →
      (star x ⬝ᵥ (G i).mulVec x).re < 0 := by
  filter_upwards [eventually_quadForm_sub_diagonal_le G c hδ hconv] with i hi
  exact negDef_on_negSupported_of_perturbed c hδ hc (G i) hi

/-- **The scaled Gram is eventually negative definite on the negative coordinates.**  The measure
part vanishes at small heights off the atoms, so the entrywise limit is the coefficient diagonal. -/
theorem eventually_negDef_totalGram_negSupported {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x ∈ negSupported c, x ≠ 0 →
      (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0 :=
  eventually_negDef_on_negSupported_of_entrywise (fun y => totalGram ν a c y) c hδ hc
    (entrywise_totalGram_sub_diagonal ν a c
      (fun l => tendsto_totalGram_diagonal_sub ν a c ha l
        (tendsto_measureGram_diagonal_of_dominant ν a l R hR (hdom l) (hatom l)))
      (fun l m hlm => tendsto_totalGram_offdiag ν a c ha hlm
        (tendsto_measureGram_offdiag_of_dominant ν a l m R hR
          (hdom l) (hdom m) (hatom l) (hatom m))))

/-- **The chamber law at an arbitrary chamber.**  At all small heights the negative index of the
scaled Pick Gram is exactly the Hamming distance of the coefficient sign pattern from the positive
chamber: no subspace on which the Gram is negative definite is larger, and the negative coordinate
subspace attains that dimension. -/
theorem chamberLaw_totalGram_general {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0)
    (v : ℝ → Fin (negCount c) → (Fin d → ℂ))
    (hPSD : ∀ᶠ y : ℝ in 𝓝[≠] 0, (totalGram ν a c y
      + ∑ i, Matrix.of fun j l => v y i j * star (v y i l)).PosSemidef) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c)
            = hammingDist (signPattern c) (positiveChamber d) := by
  filter_upwards [eventually_negDef_totalGram_negSupported ν a c ha hδ hc R hR hdom hatom, hPSD]
    with y hy hpsd
  exact chamberLaw_negIndex_eq_hammingDist (totalGram ν a c y) c (v y) hpsd hy

end

end GaloisForLFunctions.HTGeometry
