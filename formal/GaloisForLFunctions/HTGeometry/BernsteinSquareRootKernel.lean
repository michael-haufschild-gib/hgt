import GaloisForLFunctions.HTGeometry.CentralBinomialWallisAsymptotic

/-!
# The universal square-root boundary of a diagonal Bernstein kernel

The reflected diagonal Bernstein kernel has two real characteristic radii `B` and `D`.
This file isolates its exact algebraic factorization and proves the nonzero half-order radial
law at the first boundary `t = B⁻²`.  No Xi-specific input is used.
-/

open Filter Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The positive real branch of the factored diagonal Bernstein kernel. -/
def bernsteinSquareRootKernel (B D t : ℝ) : ℝ :=
  1 / (Real.sqrt (1 - B ^ (2 : ℕ) * t) * Real.sqrt (1 - D ^ (2 : ℕ) * t))

/-- The two characteristic Bernstein radii factor the quadratic diagonal denominator. -/
theorem bernstein_diagonal_quadratic_factorization (a b t : ℝ) :
    (1 - (a + b) ^ (2 : ℕ) * t) * (1 - (a - b) ^ (2 : ℕ) * t) =
      1 - 2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) * t + (a ^ (2 : ℕ) - b ^ (2 : ℕ)) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
  ring

/-- Inside the first positive boundary, multiplying by the vanishing square root removes exactly
the first factor and leaves the transverse factor. -/
theorem sqrt_boundary_mul_bernsteinSquareRootKernel
    {B D t : ℝ} (hB : 0 < B) (hD : |D| < B)
    (ht0 : 0 < t) (htB : t < 1 / B ^ (2 : ℕ)) :
    Real.sqrt (1 - B ^ (2 : ℕ) * t) * bernsteinSquareRootKernel B D t =
      1 / Real.sqrt (1 - D ^ (2 : ℕ) * t) := by
  have hBsq : 0 < B ^ (2 : ℕ) := sq_pos_of_pos hB
  have hDinterval := abs_lt.mp hD
  have hDsq : D ^ (2 : ℕ) < B ^ (2 : ℕ) := by nlinarith
  have hBmul : B ^ (2 : ℕ) * t < 1 := by
    have := (lt_div_iff₀ hBsq).mp htB
    nlinarith
  have hDmul : D ^ (2 : ℕ) * t < B ^ (2 : ℕ) * t :=
    mul_lt_mul_of_pos_right hDsq ht0
  have hleft : 0 < 1 - B ^ (2 : ℕ) * t := sub_pos.mpr hBmul
  have hright : 0 < 1 - D ^ (2 : ℕ) * t := sub_pos.mpr (hDmul.trans hBmul)
  have hsleft : Real.sqrt (1 - B ^ (2 : ℕ) * t) ≠ 0 :=
    (Real.sqrt_pos.2 hleft).ne'
  have hsright : Real.sqrt (1 - D ^ (2 : ℕ) * t) ≠ 0 :=
    (Real.sqrt_pos.2 hright).ne'
  rw [bernsteinSquareRootKernel]
  field_simp [hsleft, hsright]

/-- **Universal half-order radial law.**  If `|D| < B`, then the first positive boundary of the
diagonal kernel is a genuine square-root boundary with a finite strictly positive coefficient.
The limit is taken through the physical interval `0 < t < B⁻²`. -/
theorem tendsto_sqrt_boundary_mul_bernsteinSquareRootKernel
    {B D : ℝ} (hB : 0 < B) (hD : |D| < B) :
    Tendsto
      (fun t : ℝ =>
        Real.sqrt (1 - B ^ (2 : ℕ) * t) * bernsteinSquareRootKernel B D t)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ioo 0 (1 / B ^ (2 : ℕ))))
      (nhds (1 / Real.sqrt (1 - D ^ (2 : ℕ) * (1 / B ^ (2 : ℕ))))) := by
  have hBsq : 0 < B ^ (2 : ℕ) := sq_pos_of_pos hB
  have hDinterval := abs_lt.mp hD
  have hDsq : D ^ (2 : ℕ) < B ^ (2 : ℕ) := by nlinarith
  have hlimarg : 0 < 1 - D ^ (2 : ℕ) * (1 / B ^ (2 : ℕ)) := by
    have hfrac : D ^ (2 : ℕ) / B ^ (2 : ℕ) < 1 := (div_lt_one hBsq).2 hDsq
    simpa [div_eq_mul_inv, mul_comm] using sub_pos.mpr hfrac
  have hcontinuous : ContinuousAt
      (fun t : ℝ => 1 / Real.sqrt (1 - D ^ (2 : ℕ) * t)) (1 / B ^ (2 : ℕ)) := by
    fun_prop (disch := positivity)
  have htend : Tendsto
      (fun t : ℝ => 1 / Real.sqrt (1 - D ^ (2 : ℕ) * t))
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ioo 0 (1 / B ^ (2 : ℕ))))
      (nhds (1 / Real.sqrt (1 - D ^ (2 : ℕ) * (1 / B ^ (2 : ℕ))))) :=
    hcontinuous.tendsto.mono_left inf_le_left
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (sqrt_boundary_mul_bernsteinSquareRootKernel hB hD ht.1 ht.2).symm

/-- The half-order coefficient in the preceding radial law is strictly positive. -/
theorem bernsteinSquareRootKernel_boundaryCoefficient_pos
    {B D : ℝ} (hB : 0 < B) (hD : |D| < B) :
    0 < 1 / Real.sqrt (1 - D ^ (2 : ℕ) * (1 / B ^ (2 : ℕ))) := by
  have hBsq : 0 < B ^ (2 : ℕ) := sq_pos_of_pos hB
  have hDinterval := abs_lt.mp hD
  have hDsq : D ^ (2 : ℕ) < B ^ (2 : ℕ) := by nlinarith
  have hfrac : D ^ (2 : ℕ) / B ^ (2 : ℕ) < 1 := (div_lt_one hBsq).2 hDsq
  have harg : 0 < 1 - D ^ (2 : ℕ) * (1 / B ^ (2 : ℕ)) := by
    simpa [div_eq_mul_inv, mul_comm] using sub_pos.mpr hfrac
  exact one_div_pos.mpr (Real.sqrt_pos.2 harg)

/-- Positive diagonal Bernstein weights always satisfy the strict transverse inequality
`|a-b| < a+b`; hence their reflected kernel has the nonzero half-order boundary above. -/
theorem abs_sub_lt_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| < a + b := by
  exact abs_lt.2 ⟨by linarith, by linarith⟩

end

end GaloisForLFunctions.HTGeometry
