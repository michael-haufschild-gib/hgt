import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Absolute continuity of finite product measures

A coordinatewise absolutely continuous family of sigma-finite measures on a finite index has
absolutely continuous product.  The proof splits off one coordinate with the measure-preserving
product decomposition of `Measure.pi` and applies the two-factor law, then transports back along
the measurable equivalence.

The immediate consequence recorded here is that a nondegenerate product Gaussian on `Fin N → ℝ`
is absolutely continuous with respect to Lebesgue measure, so every almost-sure statement proved
for full-density parameter laws applies verbatim to a Gaussian ensemble.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

universe u

/-- Coordinatewise absolute continuity of sigma-finite measures passes to the finite product. -/
theorem pi_absolutelyContinuous_pi :
    ∀ (n : ℕ) {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
      (μ ν : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
  | zero =>
    intro α _ μ ν _ _ _
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ m ih =>
    intro α _ μ ν _ _ h
    set e := MeasurableEquiv.piFinSuccAbove α 0 with he
    have hμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    have hprod :
        (μ 0).prod (Measure.pi fun j => μ ((0 : Fin (m + 1)).succAbove j)) ≪
          (ν 0).prod (Measure.pi fun j => ν ((0 : Fin (m + 1)).succAbove j)) :=
      Measure.AbsolutelyContinuous.prod (h 0)
        (ih (fun j => μ ((0 : Fin (m + 1)).succAbove j))
          (fun j => ν ((0 : Fin (m + 1)).succAbove j)) (fun j => h _))
    have hmap := hprod.map (MeasurableEquiv.measurable e.symm)
    rw [← hμ, ← hν, e.map_symm_map, e.map_symm_map] at hmap
    exact hmap

/-- A nondegenerate product Gaussian on a finite-dimensional real coordinate space is absolutely
continuous with respect to Lebesgue measure. -/
theorem productGaussian_absolutelyContinuous (N : ℕ) {v : NNReal} (hv : v ≠ 0)
    (m : Fin N → ℝ) :
    Measure.pi (fun i => ProbabilityTheory.gaussianReal (m i) v) ≪
      (volume : Measure (Fin N → ℝ)) := by
  rw [volume_pi]
  exact pi_absolutelyContinuous_pi N _ _
    (fun i => ProbabilityTheory.gaussianReal_absolutelyContinuous (m i) hv)

end GaloisForLFunctions.HTGeometry
