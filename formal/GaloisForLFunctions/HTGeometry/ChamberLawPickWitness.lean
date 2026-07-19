import GaloisForLFunctions.HTGeometry.GeneralChamberLaw
import GaloisForLFunctions.HTGeometry.AtomicGramPosSemidef
import GaloisForLFunctions.HTGeometry.ScaledCauchyProductIntegrable

/-!
# The chamber law with its own positive-semidefinite witness

The chamber law needs a positive semidefinite correction of the scaled Pick Gram by one rank-one
term per negative coefficient.  The Pick kernel supplies that correction itself: each atom
contributes a rank-one term weighted by its coefficient, so correcting exactly the negative ones
leaves the positive-part Gram, which is a square, plus the measure Gram, which is a conjugate Gram
of the scaled Cauchy kernels.

The integrability those kernels need is the same Herglotz dominant that drives the small-height
limit, so the chamber law rests on the dominant and the non-atom hypothesis alone.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset

noncomputable section

open scoped Classical ComplexOrder

/-- **The scaled Pick Gram is eventually corrected to positive semidefinite by its negative
atoms.**  The dominant makes every atom kernel integrable at small heights, hence every product of
two scaled Cauchy kernels integrable, hence the measure Gram positive semidefinite. -/
theorem eventually_totalGram_add_negAtomWitness_posSemidef {d : ℕ} (ν : Measure ℝ)
    (a c : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν) :
    ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), (totalGram ν a c y
      + ∑ i, Matrix.of fun j k => negAtomWitness a c y i j
          * star (negAtomWitness a c y i k)).PosSemidef := by
  have hall : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), ∀ j : Fin d,
      Integrable (fun t : ℝ => atomKernel (a j) y t) ν := by
    rw [Filter.eventually_all]
    exact fun j => eventually_integrable_atomKernel ν (a j) R hR (hdom j)
  filter_upwards [hall, self_mem_nhdsWithin] with y hy hy0
  exact totalGram_add_negAtomWitness_posSemidef ν a c y
    fun l m => integrable_scaledCauchy_product hy0 (hy l) (hy m)

/-- **The chamber law for the scaled Pick Gram.**  At all small heights the negative index is the
Hamming distance of the coefficient sign pattern from the positive chamber.  Nothing about the
matrix is assumed: the rank-one correction is the one built from the negative atoms, and its count
is the chamber grading by construction.  The inputs are the injectivity of the nodes, the margin at
the negative coefficients, the Herglotz dominant, and that no node carries mass. -/
theorem chamberLaw_totalGram_pick {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c)
            = hammingDist (signPattern c) (positiveChamber d) :=
  chamberLaw_totalGram_general ν a c ha hδ hc R hR hdom hatom
    (fun y => negAtomWitness a c y)
    (eventually_totalGram_add_negAtomWitness_posSemidef ν a c R hR hdom)

end

end GaloisForLFunctions.HTGeometry
