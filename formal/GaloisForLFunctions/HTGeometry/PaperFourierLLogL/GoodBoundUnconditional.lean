import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Main
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Endpoint
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Weak.Quantile
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Weak.Signed

/-!
# Good-set consequences with the maximal good-set bound discharged

The dyadic grid bound `Dyadic.gridProof : GridBound` lifts through three layers, each stated as a
conditional implication: `GridBound → UnitTreeBound → AffineTreeBound → RealGoodBound`.  The
intermediate interfaces are recorded below as theorems.  `maximal_good_sets : GoodBound` (the last
layer) discharges the `GoodBound` premise of the endpoint and weak-type lemmas.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

namespace FourierLLogL

/-! ## The lifted dyadic bounds -/

/-- The cut dyadic bound on one top holds (lifted from the grid bound). -/
theorem Period.unitTreeBound_holds : Period.UnitTreeBound :=
  Dyadic.gridProof.unitTreeBound

/-- The affine (periodic, shifted-density) tree bound holds. -/
theorem Period.affineTreeBound_holds : Period.AffineTreeBound :=
  Period.unitTreeBound_holds.affine

/-- The real good-set bound for periodic nonnegative densities holds. -/
theorem Period.realGoodBound_holds : Period.RealGoodBound :=
  Period.affineTreeBound_holds.realGoodBound

/-! ## Good-set consequences -/

/-- Summable pointwise majorants of all symmetric partial sums along a sequence `F j` whose `L¹`
masses `w j` are summable against `2^j` and whose sup norms are at most `w j e^{2^{j+L}}`. -/
theorem ae_tail_majorant (F : ℕ → Torus → ℂ) (w : ℕ → ℝ) (L : ℕ)
    (hF : ∀ j, Integrable (F j) circleMeasure)
    (hw : ∀ j, 0 < w j)
    (hsum : Summable (fun j => (2:ℝ)^j * w j))
    (hm : ∀ j, (∫ x, ‖F j x‖ ∂circleMeasure) ≤ w j)
    (hh : ∀ j, ∀ᵐ x ∂circleMeasure, ‖F j x‖ ≤ w j * Real.exp ((2:ℝ)^(j+L))) :
    ∀ᵐ x ∂circleMeasure, ∃ b : ℕ → ℝ, Summable b ∧ ∀ᶠ j : ℕ in atTop,
      ∀ N, ‖symmetricPartialSum (F j) N x‖ + ‖F j x‖ ≤ b j :=
  maximal_good_sets.ae_tail_majorant F w L hF hw hsum hm hh

/-- Symmetric Fourier partial sums of an essentially bounded function converge almost
everywhere. -/
theorem ae_convergence_of_bounded (f : Torus → ℂ)
    (hf : Integrable f circleMeasure) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂circleMeasure, Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) :=
  maximal_good_sets.ae_convergence_bounded f hf B hB hb

namespace Weak

/-- One threshold `L > 0` has `|{M f > L}| ≤ 1/16` for every `f` in the modular unit ball. -/
theorem median_budget_unconditional :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : Torus → ℂ), inside f → circleMeasure.real (cloudSet f L) ≤ 1/16 :=
  median_budget maximal_good_sets

/-- Uniform weak-type bound `p · |{M f > p}| ≤ v` over the modular unit ball. -/
theorem circle_bill_unconditional :
    ∃ v : ℝ, 0 < v ∧ ∀ f : Torus→ℂ, inside f →
      ∀ p : ℝ, 0 < p → p*law.real (cloudSet f p) ≤ v :=
  circle_bill maximal_good_sets

end Weak

end FourierLLogL

end GaloisForLFunctions.HTGeometry
