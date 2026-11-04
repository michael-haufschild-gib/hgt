import GaloisForLFunctions.ZeroConfigurationGeometry.EulerColumnsAreSeenJustAboveTheirPrime

/-!
# The square-root threshold identifies columns of Riemann–von Mangoldt density

Topic 1 of the field asks for the least camera exponent `λ` at which a tilted point has no real
mimic of Riemann–von Mangoldt density at height `T`. The matrix explicit formula of `Zeta23` uses
windows supported in `[−L_Z/2, L_Z/2]`, `L_Z = λ log(T/2π)`, so its aperture is
`a = λ log(T/2π)/2`.

The off-line lattice pair `{½ ± δ + 2πik/L}` has two points per height `2π/L`, i.e. density `L/π`.
It has Riemann–von Mangoldt density `log(T/2π)/2π` exactly when `L = ½ log(T/2π)`
(`rvmLatticeLength`).

* **The threshold** (`rvmLattice_mimic_iff`). For `T > 2π`, every depth `0 < δ ≤ ½` and every
  `λ > 0`, the lattice pair of Riemann–von Mangoldt density at height `T` and the doubled on-line
  lattice are mimics for the camera of exponent `λ` iff `λ ≤ ½`.

So for column mimics the identification threshold is `λ = ½`, uniformly in the depth and the
height: cameras reading primes beyond `√(T/2π)` identify every tilted column of the density of
the zeros of `ζ`, and cameras below cannot. This is the square-root threshold of
`SquareRootThreshold`, obtained here without a sign, from `offLineLattice_mimic_iff`.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower

/-- The lattice length of Riemann–von Mangoldt density at height `T`: `L = ½ log(T/2π)`. -/
def rvmLatticeLength (T : ℝ) : ℝ := Real.log (T / (2 * π)) / 2

theorem rvmLatticeLength_pos {T : ℝ} (hT : 2 * π < T) : 0 < rvmLatticeLength T := by
  unfold rvmLatticeLength
  have : 1 < T / (2 * π) := by rw [one_lt_div (by positivity)]; exact hT
  have := Real.log_pos this
  positivity

/-- The lattice pair of length `L` has density `L/π`; at `L = rvmLatticeLength T` this is the
Riemann–von Mangoldt density `log(T/2π)/2π`. -/
theorem rvmLatticeLength_density (T : ℝ) : rvmLatticeLength T / π = Real.log (T / (2 * π)) / (2 * π) := by
  unfold rvmLatticeLength; field_simp

/-- **The square-root threshold identifies columns.** -/
theorem rvmLattice_mimic_iff {T : ℝ} (hT : 2 * π < T) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {lam : ℝ} :
    (∀ f, ApertureWindow (lam * Real.log (T / (2 * π)) / 2) f →
      (offLineLatticeConfig (rvmLatticeLength_pos hT) hδ hδ').W f f =
        (onLineLatticeConfig (rvmLatticeLength_pos hT)).W f f) ↔ lam ≤ 1 / 2 := by
  rw [offLineLattice_mimic_iff]
  have hl : 0 < Real.log (T / (2 * π)) := by
    have : 1 < T / (2 * π) := by rw [one_lt_div (by positivity)]; exact hT
    exact Real.log_pos this
  unfold rvmLatticeLength
  constructor
  · intro h
    have : lam * Real.log (T / (2 * π)) ≤ 1 / 2 * Real.log (T / (2 * π)) := by linarith
    exact le_of_mul_le_mul_right this hl
  · intro h
    have := mul_le_mul_of_nonneg_right h hl.le
    linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
