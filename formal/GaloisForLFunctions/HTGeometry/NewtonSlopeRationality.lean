import Mathlib

/-!
# Newton polygon slopes are rational

The Newton polygon of an analytic algebraic differential equation along a formal solution is built
from derivative orders and orders of vanishing of analytic coefficients, so its vertices are lattice
points.  Every finite slope between two of them is a ratio of integers, hence rational, and so is
every reciprocal of a nonzero slope.

The exact Gevrey order of a divergent formal solution is, by the Sibuya–Ramis theorem, the
reciprocal of one of those slopes.  An irrational Gevrey order therefore excludes every analytic
algebraic differential equation — which is the rigidity used against the irrational-power canonical
products.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The reciprocal of a lattice slope is rational.** -/
theorem exists_rat_inv_lattice_slope (x₁ y₁ x₂ y₂ : ℤ) :
    ∃ r : ℚ, ((x₂ - x₁ : ℤ) : ℝ) / ((y₂ - y₁ : ℤ) : ℝ) = (r : ℝ) := by
  refine ⟨((x₂ - x₁ : ℤ) : ℚ) / ((y₂ - y₁ : ℤ) : ℚ), ?_⟩
  push_cast
  ring

/-- **An irrational number is not the reciprocal of a lattice slope.** -/
theorem not_irrational_inv_lattice_slope {x₁ y₁ x₂ y₂ : ℤ}
    {s : ℝ} (hs : s = ((x₂ - x₁ : ℤ) : ℝ) / ((y₂ - y₁ : ℤ) : ℝ)) : ¬ Irrational s := by
  obtain ⟨r, hr⟩ := exists_rat_inv_lattice_slope x₁ y₁ x₂ y₂
  rw [hs, hr]
  exact fun h => h ⟨r, rfl⟩

/-- **The Gevrey slope obstruction.**  An irrational number cannot be the reciprocal of a slope of a
lattice polygon, so a formal solution of exact irrational Gevrey order satisfies no analytic
algebraic differential equation. -/
theorem not_lattice_slope_of_irrational {s : ℝ} (hirr : Irrational s)
    (hgev : ∃ x₁ y₁ x₂ y₂ : ℤ, s = ((x₂ - x₁ : ℤ) : ℝ) / ((y₂ - y₁ : ℤ) : ℝ)) : False := by
  obtain ⟨x₁, y₁, x₂, y₂, hs⟩ := hgev
  exact not_irrational_inv_lattice_slope hs hirr

end GaloisForLFunctions.HTGeometry
