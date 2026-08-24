import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurValueKernelRank
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteUpperKernelInertia

/-!
# Finite shifted-Xi inertia after common-factor cancellation

For a finite strict-right Xi divisor, the actual regular shifted-Xi kernel has exact negative
index equal to the restricted-adjoint rank of its full Schur numerator on the finite pole model
space.  This is the intrinsic finite common-divisor convention and requires no nonexceptionality
assumption.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Intrinsic cancellation-aware finite shifted-Xi negative index.  Its rank defect is exactly the
common inner-factor defect between the full shifted numerator and pole denominator. -/
def xiShiftFiniteCancelledNegativeIndex
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] : ℕ :=
  finiteBlaschkeGeneralizedSchurCancelledIndex
    (xiShiftFiniteSchurNumerator omega homega)
    (xiShiftFinitePoleBlaschke omega)

/-- Exact finite shifted-Xi kernel inertia at every nonnegative shift, including exceptional
common-zero shifts. -/
theorem xiShiftRegularUpperKernel_exactNegativeSquares_finite_cancelled
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega)
        (xiShiftFiniteCancelledNegativeIndex omega homega) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (xiShiftRegularUpperKernel omega) r →
        r ≤ xiShiftFiniteCancelledNegativeIndex omega homega := by
  let F := xiShiftFiniteSchurNumerator omega homega
  let B := xiShiftFinitePoleBlaschke omega
  have hdisk := finiteBlaschkeGeneralizedSchurValueKernel_exactNegativeSquares_rank
    F B (by simp [F, xiShiftFiniteSchurNumerator_bd])
  have hext := finiteBlaschkeGeneralizedSchurValueKernel_hasExteriorNegativeDimension_rank
    F B (by simp [F, xiShiftFiniteSchurNumerator_bd])
  constructor
  · have hlower : HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega)
        (finiteBlaschkeGeneralizedSchurCancelledIndex F B) := by
      let e : B.exteriorDisk → XiShiftRegularUpperNode omega :=
        fun u => xiShiftFiniteExteriorToRegularUpper omega u
      let a : B.exteriorDisk → ℂ := fun u =>
        (xiShiftFiniteUpperKernelWeight omega (e u))⁻¹
      have ha : ∀ u, a u ≠ 0 := fun u =>
        inv_ne_zero (xiShiftFiniteUpperKernelWeight_ne_zero omega (e u))
      apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
        (fun u v : B.exteriorDisk =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v)
        (xiShiftRegularUpperKernel omega) e a ha
      · intro u v
        have hcong := xiShiftRegularUpperKernel_eq_finiteDisk_congruence
          homega (e u) (e v)
        have hcu : upperToDiskCayley (e u).1 = u.1 :=
          upperToDiskCayley_xiShiftFiniteExteriorToRegularUpper omega u
        have hcv : upperToDiskCayley (e v).1 = v.1 :=
          upperToDiskCayley_xiShiftFiniteExteriorToRegularUpper omega v
        rw [hcu, hcv] at hcong
        change finiteBlaschkeGeneralizedSchurValueKernel F B u.1 v.1 =
          (xiShiftFiniteUpperKernelWeight omega (e u))⁻¹ *
            xiShiftRegularUpperKernel omega (e u) (e v) *
            (starRingEnd ℂ)
              ((xiShiftFiniteUpperKernelWeight omega (e v))⁻¹)
        rw [hcong]
        simp only [map_inv₀]
        field_simp [xiShiftFiniteUpperKernelWeight_ne_zero omega (e u),
          xiShiftFiniteUpperKernelWeight_ne_zero omega (e v),
          (map_ne_zero (starRingEnd ℂ)).mpr
            (xiShiftFiniteUpperKernelWeight_ne_zero omega (e v))]
        rfl
      · exact hext
    exact hlower
  · intro r hupper
    have hdiskr : HasFiniteKernelNegativeDimension
        (fun u v : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v) r := by
      let e : XiShiftRegularUpperNode omega → Metric.ball (0 : ℂ) 1 :=
        fun z => ⟨upperToDiskCayley z.1,
          by
            rw [Metric.mem_ball, dist_zero_right]
            exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk
              z.1 z.property.1⟩
      let a : XiShiftRegularUpperNode omega → ℂ := fun z =>
        xiShiftFiniteUpperKernelWeight omega z
      have ha : ∀ z, a z ≠ 0 := fun z =>
        xiShiftFiniteUpperKernelWeight_ne_zero omega z
      apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
        (xiShiftRegularUpperKernel omega)
        (fun u v : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v)
        e a ha
      · intro z w
        exact xiShiftRegularUpperKernel_eq_finiteDisk_congruence homega z w
      · exact hupper
    exact hdisk.2 r hdiskr

end

end RHTower
