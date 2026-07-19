import GaloisForLFunctions.HTGeometry.ChamberNegInertiaBound

/-!
# The scaled Poisson kernel selects an atom

Scaling a Pick kernel at nodes approaching the real axis produces the kernel
`y² / ((t - a)² + y²)`.  It is bounded by one, equals one at `a`, and tends to zero at every other
point as `y → 0`, so it selects exactly the mass of `ν` at `a`.

Away from `a` it is dominated by `y² / (t - a)²`, which is what controls the tail against the
Herglotz growth condition when the measure is infinite.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The scaled Poisson kernel appearing in the Krein index limit. -/
def atomKernel (a y t : ℝ) : ℝ := y ^ 2 / ((t - a) ^ 2 + y ^ 2)

theorem atomKernel_nonneg (a t : ℝ) {y : ℝ} : 0 ≤ atomKernel a y t := by
  rw [atomKernel]
  positivity

/-- The kernel never exceeds one. -/
theorem atomKernel_le_one (a t : ℝ) {y : ℝ} (hy : y ≠ 0) : atomKernel a y t ≤ 1 := by
  rw [atomKernel, div_le_one (by positivity)]
  nlinarith [sq_nonneg (t - a)]

/-- At the node the kernel is one. -/
@[simp]
theorem atomKernel_self (a : ℝ) {y : ℝ} (hy : y ≠ 0) : atomKernel a y a = 1 := by
  rw [atomKernel]
  simp only [sub_self]
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  exact div_self (pow_ne_zero 2 hy)

/-- Away from the node the kernel is dominated by the square ratio, which is the bound used against
the Herglotz tail condition. -/
theorem atomKernel_le_sq_div (a t : ℝ) {y : ℝ} (hta : t ≠ a) :
    atomKernel a y t ≤ y ^ 2 / (t - a) ^ 2 := by
  have hpos : (0 : ℝ) < (t - a) ^ 2 := by
    have : t - a ≠ 0 := sub_ne_zero.2 hta
    positivity
  rw [atomKernel]
  apply div_le_div_of_nonneg_left (by positivity) hpos
  nlinarith [sq_nonneg y]

/-- **The kernel vanishes off the node in the limit.**  At any point other than the node the scaled
kernel tends to zero as the height tends to zero. -/
theorem tendsto_atomKernel_of_ne (a t : ℝ) (hta : t ≠ a) :
    Tendsto (fun y : ℝ => atomKernel a y t) (𝓝 0) (𝓝 0) := by
  have hpos : (0 : ℝ) < (t - a) ^ 2 := by
    have : t - a ≠ 0 := sub_ne_zero.2 hta
    positivity
  have hcont : Tendsto (fun y : ℝ => y ^ 2 / ((t - a) ^ 2 + y ^ 2)) (𝓝 0)
      (𝓝 (0 ^ 2 / ((t - a) ^ 2 + 0 ^ 2))) := by
    apply Tendsto.div
    · exact (continuous_pow 2).tendsto 0
    · exact ((continuous_const.add (continuous_pow 2)).tendsto 0)
    · simp only [ne_eq]
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      exact ne_of_gt hpos
  simpa [atomKernel] using hcont

/-- **The kernel is eventually within any tolerance off the node.**  The quantitative form of the
previous limit, which is what a dominated-convergence argument consumes. -/
theorem eventually_atomKernel_lt (a t : ℝ) (hta : t ≠ a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in 𝓝 0, atomKernel a y t < ε := by
  have h := (tendsto_atomKernel_of_ne a t hta).eventually
    (eventually_lt_nhds (by simpa using hε) : ∀ᶠ z : ℝ in 𝓝 0, z < ε)
  exact h

end

end GaloisForLFunctions.HTGeometry
