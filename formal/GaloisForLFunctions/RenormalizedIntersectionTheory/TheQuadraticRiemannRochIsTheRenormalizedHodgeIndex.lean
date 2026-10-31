import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRenormalizedHodgeIndex
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SerreDualScalingCohomologyAndLargeSieveSections

/-!
# The quadratic Riemann–Roch is the renormalized Hodge index

On a curve over `𝔽_q` the Hodge index on `C × C` follows from Riemann–Roch on the surface: `h⁰` grows
quadratically and is Serre dual to `h²`. On the scaling surface of `ℤ` the corpus has the linear
Riemann–Roch of the base (`ArithmeticOrientationGeometry.TheThetaH0OfSpecZ`) and the axiomatic
surface of ArithmeticCastelnuovoSeveri. This file places the missing quadratic Riemann–Roch in the
renormalized pairing.

* **Dictionary** (`renormalizedHodgeIndex_ratCorr_iff_scalingSurface_hodgeIndex`): the renormalized
  Hodge index of Weil's correlation is the Hodge index of the scaling surface.
* **`h⁰` on the scaling surface** (`renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0`): a
  sign-free `h⁰` with Serre-dual `h¹ = h⁰(K − ·)`, the Riemann–Roch lower bound
  `χ(nD) − εn² ≤ h⁰(nD) + h¹(nD)` along every ray, and subquadratic growth in degree zero exists iff
  the renormalized Hodge index holds
  (`SelectivePositivityAndThresholdLaws.serreDual_section_growth_iff_riemannHypothesis`).

So the quadratic Riemann–Roch on the scaling surface is not an independent input: an `h⁰` of the
required shape is the same datum as positivity of the renormalized pairing on the pole-orthogonal
hyperplane. Constructing it unconditionally would prove RH.
-/

open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws
open GaloisForLFunctions.ArithmeticEffectivityTheory

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- **The renormalized Hodge index is the Hodge index of the scaling surface.** -/
theorem renormalizedHodgeIndex_ratCorr_iff_scalingSurface_hodgeIndex :
    RenormalizedHodgeIndex ratCorr ↔ scalingSurface.HodgeIndex := by
  rw [← riemannHypothesis_iff_renormalizedHodgeIndex]
  exact (serreDual_section_growth_iff_riemannHypothesis 0 0).out 0 1

/-- **A sign-free Serre-dual `h⁰` with quadratic Riemann–Roch growth exists iff the renormalized
Hodge index holds.** -/
theorem renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0 (K : ScalingCycle) (χ₀ : ℝ) :
    RenormalizedHodgeIndex ratCorr ↔
      ∃ h0_fn h1_fn : ScalingCycle → ℝ,
        (∀ D, 0 ≤ h0_fn D) ∧
        (∀ D, h1_fn D = h0_fn (K - D)) ∧
        (∀ D : ScalingCycle, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
          eulerChar scalingSurface K χ₀ ((n : ℝ) • D) - ε * (n : ℝ) ^ 2 ≤
            h0_fn ((n : ℝ) • D) + h1_fn ((n : ℝ) • D)) ∧
        DegreeZeroSubquadratic scalingSurface K h0_fn := by
  rw [← riemannHypothesis_iff_renormalizedHodgeIndex]
  exact (serreDual_section_growth_iff_riemannHypothesis K χ₀).out 0 2

end GaloisForLFunctions.RenormalizedIntersectionTheory
