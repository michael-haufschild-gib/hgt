import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheJetsAreASumOfHardySquares
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Newtonian axis and the two rulings

The even part of the Newtonian kernel on an axis in three-dimensional
Euclidean space is the jet kernel. Its even radial multipoles are the
Hardy kernels. At weight zero, evaluation at the origin and normalized
evaluation at infinity give the two degree pairings.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart
open AbsoluteGeometryOfSpecZ

/-- A point of the first coordinate axis in Euclidean three-space. -/
def newtonianAxis (r : ℝ) : EuclideanSpace ℝ (Fin 3) := PiLp.single 2 0 r

/-- The Newtonian kernel away from the diagonal, with the usual totalized reciprocal. -/
def newtonianKernel (x y : EuclideanSpace ℝ (Fin 3)) : ℝ := 1 / dist x y

theorem newtonianKernel_axis (r s : ℝ) :
    newtonianKernel (newtonianAxis r) (newtonianAxis s) = 1 / |r - s| := by
  rw [newtonianKernel, newtonianAxis, newtonianAxis,
    PiLp.dist_single_same 2 (fun _ : Fin 3 => ℝ), Real.dist_eq]

/-- Radial coefficient of the Newtonian multipole of degree `ℓ`. -/
def axialMultipole (ℓ : ℕ) (r s : ℝ) : ℝ := min r s ^ ℓ / max r s ^ (ℓ + 1)

/-- The jet of weight `−2j` is exactly the even Newtonian multipole. -/
theorem axialMultipole_even_nat (j m n : ℕ) :
    axialMultipole (2 * j) m n = jetLevel j m n := by
  simp only [axialMultipole, jetLevel, Nat.cast_min, Nat.cast_max]

/-- Averaging the point and its opposite removes the odd Newtonian multipoles. -/
theorem even_newtonianKernel_eq_jetKernel (m n : ℕ) :
    (newtonianKernel (newtonianAxis m) (newtonianAxis n) +
      newtonianKernel (newtonianAxis m) (newtonianAxis (-(n : ℝ)))) / 2 = jetKernel m n := by
  rw [newtonianKernel_axis, newtonianKernel_axis, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))]
  rfl

/-- The convergent even multipole expansion is the actual Newtonian kernel on the axis. -/
theorem hasSum_even_newtonianMultipoles {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    HasSum (fun j => axialMultipole (2 * j) m n)
      ((newtonianKernel (newtonianAxis m) (newtonianAxis n) +
        newtonianKernel (newtonianAxis m) (newtonianAxis (-(n : ℝ)))) / 2) := by
  simp only [axialMultipole_even_nat, even_newtonianKernel_eq_jetKernel]
  exact hasSum_jetLevel hm hn hmn

/-- The weight-zero kernel at the origin is the first ruling's pairing. -/
theorem axialMultipole_zero_at_origin {s : ℝ} (hs : 0 ≤ s) :
    axialMultipole 0 0 s = 1 / s := by
  simp only [axialMultipole, pow_zero, zero_add, pow_one, max_eq_right hs]

/-- Beyond the charge, multiplying the weight-zero kernel by the radius gives one. -/
theorem normalized_axialMultipole_zero_eq_one {r s : ℝ} (hr : 0 < r) (hsr : s ≤ r) :
    r * axialMultipole 0 r s = 1 := by
  simp only [axialMultipole, pow_zero, zero_add, pow_one, max_eq_left hsr]
  field_simp

/-- Normalized evaluation at infinity is the second ruling's pairing. -/
theorem tendsto_normalized_axialMultipole_zero (s : ℝ) :
    Tendsto (fun r : ℝ => r * axialMultipole 0 r s) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop s, eventually_gt_atTop (0 : ℝ)] with r hsr hr
  exact (normalized_axialMultipole_zero_eq_one hr hsr).symm

/-- Evaluation at the origin gives the first degree of every finite divisor. -/
theorem sum_axialMultipole_origin_eq_degOne (S : Finset ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ S, c n * axialMultipole 0 0 n) = degOne S c := by
  apply Finset.sum_congr rfl
  intro n _
  rw [axialMultipole_zero_at_origin (Nat.cast_nonneg n)]
  ring

/-- Beyond every charge, normalized evaluation is exactly the second degree. -/
theorem sum_normalized_axialMultipole_eq_degTwo (S : Finset ℕ) (c : ℕ → ℝ)
    {r : ℝ} (hr : 0 < r) (hS : ∀ n ∈ S, (n : ℝ) ≤ r) :
    (∑ n ∈ S, c n * (r * axialMultipole 0 r n)) = degTwo S c := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalized_axialMultipole_zero_eq_one hr (hS n hn), mul_one]

#print axioms hasSum_even_newtonianMultipoles
#print axioms tendsto_normalized_axialMultipole_zero
#print axioms sum_axialMultipole_origin_eq_degOne
#print axioms sum_normalized_axialMultipole_eq_degTwo

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
