import GaloisForLFunctions.RHTower.RadialLeakageArcsineMeasure
import GaloisForLFunctions.HTGeometry.ScheffeLemma

/-!
# Weak convergence of the finite-aperture radial leakage measures

The limiting radial leakage measure has density `(8/11π)·1/(x√(x²−1))` on `(1, ∞)` and total mass
exactly `4/11`.  The finite-aperture measures are given by their own densities, and the question
is whether they converge to it weakly.

Mass carried by a family of densities can escape to infinity even when the densities converge
pointwise, so pointwise convergence alone is not enough.  But if the total masses are also known
to converge to the right value, then no mass escapes, and Scheffé's lemma upgrades pointwise
convergence to `L¹` convergence of the densities — which is stronger than weak convergence: it
gives convergence of the integrals against *every* bounded weight, uniformly in the weight's
bound.

This module pins down the limiting object exactly: its density, its integrability, and its total
mass `4/11`.  These are the targets any convergence proof must hit.  The convergence itself is not
proved here and no conditional form of it is recorded — the general reduction lives in
`HTGeometry/ScheffeLemma.lean` and can be applied once the density asymptotics exist.
-/

open MeasureTheory Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The limiting measure -/

/-- The density of the limiting radial leakage measure `ν∞`, normalized so that its total mass on
`(1, ∞)` is the constrained leakage fraction `4/11`. -/
def nuInfinityDensity (x : ℝ) : ℝ := (8 / (11 * Real.pi)) * radialLeakageDensity x

theorem nuInfinityDensity_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ nuInfinityDensity x := by
  rw [nuInfinityDensity]
  have h1 : (0 : ℝ) ≤ 8 / (11 * Real.pi) := by positivity
  exact mul_nonneg h1 (radialLeakageDensity_nonneg hx)

theorem nuInfinityDensity_nonneg_ae :
    0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] nuInfinityDensity := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact nuInfinityDensity_nonneg (le_trans zero_le_one (le_of_lt hx))

theorem integrableOn_Ioi_one_nuInfinityDensity :
    IntegrableOn nuInfinityDensity (Ioi (1 : ℝ)) volume :=
  (integrableOn_Ioi_radialLeakageDensity (le_refl 1)).const_mul _

/-- **The limiting measure has total mass `4/11`.** -/
theorem integral_Ioi_one_nuInfinityDensity :
    ∫ x in Ioi (1 : ℝ), nuInfinityDensity x = 4 / 11 := by
  simp only [nuInfinityDensity]
  rw [integral_const_mul]
  exact radialLeakageMeasure_total_mass

end RHTower

end
