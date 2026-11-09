import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimePowerWindowTransfer

/-!
# Prime-gap transfer inside growing observation windows

Once a logarithmic window radius lies between two and its center, the
nearest prime to every point of its interior half-window remains in the
full window. A trace of width `a` loses only exponent `a-1/3`.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Prime lower bounds transfer to half-windows whose radii lie between two and their centers. -/
theorem prime_windows_transfer {Z : ZeroConfig} (hZ : TemperedConfig Z) {a α K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (R : ℝ → ℝ) (hR : ∀ᶠ T in atTop, 2 ≤ R T ∧ R T ≤ T)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ R T →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ R T / 2 →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  apply prime_power_windows_transfer hZ ha (σ := 0) le_rfl hα haα R hR hwidth
  simpa only [Real.rpow_zero, mul_one] using hprime

#print axioms prime_windows_transfer

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
