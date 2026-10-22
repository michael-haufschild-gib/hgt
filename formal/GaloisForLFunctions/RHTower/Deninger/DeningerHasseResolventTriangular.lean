import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseResolvent
import GaloisForLFunctions.HTGeometry.GradedTriangularRegularizedDeterminant

/-! # The actual source inverse has a graded triangular kernel

The original generator recurrence determines its diagonal and excludes
off-diagonal paths of nonincreasing Hasse degree. This retains all Jordan
blocks while making the complete power traces accessible.
-/

noncomputable section
open Complex HilbertSchmidt
open GaloisForLFunctions.HTGeometry

namespace RHTower
open scoped Classical

def deningerMeyerHasseResolventKernel :
    DeningerArithmeticJetCoordinate × DeningerArithmeticJetCoordinate → ℂ :=
  matrixOf deningerMeyerHasseResolvent

theorem deningerMeyerHasseResolventKernel_isHS : IsHS deningerMeyerHasseResolventKernel :=
  isHS_matrixOf deningerMeyerHasseResolvent_isHilbertSchmidt

theorem toOperator_deningerMeyerHasseResolventKernel :
    toOperator deningerMeyerHasseResolventKernel_isHS = deningerMeyerHasseResolvent :=
  toOperator_matrixOf deningerMeyerHasseResolvent_isHilbertSchmidt

private theorem hasse_column_zero (r : DeningerArithmeticJetCoordinate) :
    ∀ (j : ℕ) (rho : XiDivisorSupport) (hj : j < xiSupportMultiplicity rho),
      (⟨rho, ⟨j, hj⟩⟩ : DeningerArithmeticJetCoordinate) ≠ r → j ≤ r.2.val →
      deningerMeyerHasseResolvent (lp.single 2 r (1 : ℂ)) ⟨rho, ⟨j, hj⟩⟩ = 0 := by
  intro j
  induction j with
  | zero =>
    intro rho hj hne _
    have he := deningerMeyerHasseResolvent_equation (lp.single 2 r (1 : ℂ)) ⟨rho, ⟨0, hj⟩⟩
    rw [deningerHasseHilbertShift_zero,
      lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ)
        2 r (1 : ℂ) hne, mul_zero, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (xiSpectralPoint_ne_zero _)
  | succ j ih =>
    intro rho hj hne hle
    have hp : j < xiSupportMultiplicity rho := by omega
    have hprev : (⟨rho, ⟨j, hp⟩⟩ : DeningerArithmeticJetCoordinate) ≠ r := by
      intro h
      have hd := congrArg (fun q : DeningerArithmeticJetCoordinate => q.2.val) h
      change j = r.2.val at hd
      omega
    have hz := ih rho hp hprev (by omega)
    have he := deningerMeyerHasseResolvent_equation (lp.single 2 r (1 : ℂ)) ⟨rho, ⟨j + 1, hj⟩⟩
    rw [deningerHasseHilbertShift_succ, hz,
      lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ)
        2 r (1 : ℂ) hne, mul_zero, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (xiSpectralPoint_ne_zero _)

/-- Every nonzero off-diagonal entry strictly raises the original Hasse degree. -/
theorem deningerMeyerHasseResolventKernel_triangular :
    GradedTriangular (fun q : DeningerArithmeticJetCoordinate => q.2.val)
      deningerMeyerHasseResolventKernel := by
  rintro ⟨rho, j, hj⟩ r hne hle
  exact hasse_column_zero r j rho hj hne hle

/-- Each multiplicity slot contributes its actual reciprocal Xi spectral point. -/
theorem deningerMeyerHasseResolventKernel_diagonal (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseResolventKernel (q, q) = (xiSpectralPoint q)⁻¹ := by
  have he := deningerMeyerHasseResolvent_equation (lp.single 2 q (1 : ℂ)) q
  have hz : deningerHasseHilbertShift (deningerMeyerHasseResolvent (lp.single 2 q (1 : ℂ))) q = 0 := by
    rcases q with ⟨rho, j, hj⟩
    cases j with
    | zero => exact deningerHasseHilbertShift_zero _ rho hj
    | succ j =>
      rw [deningerHasseHilbertShift_succ]
      apply hasse_column_zero _ j rho _
      · intro h
        have hd := congrArg (fun r : DeningerArithmeticJetCoordinate => r.2.val) h
        change j = j + 1 at hd
        omega
      · exact Nat.le_succ j
  rw [hz, mul_zero, sub_zero, lp.single_apply_self] at he
  change deningerMeyerHasseResolvent (lp.single 2 q (1 : ℂ)) q = _
  calc
    _ = (xiSpectralPoint q)⁻¹ *
        (xiSpectralPoint q * deningerMeyerHasseResolvent (lp.single 2 q (1 : ℂ)) q) := by
          rw [← mul_assoc, inv_mul_cancel₀ (xiSpectralPoint_ne_zero q), one_mul]
    _ = _ := by rw [he, mul_one]

theorem deningerMeyerHasseResolventKernel_power_diagonal
    (n : ℕ) (q : DeningerArithmeticJetCoordinate) :
    hsPow deningerMeyerHasseResolventKernel n (q, q) = (xiSpectralPoint q)⁻¹ ^ (n + 1) := by
  rw [deningerMeyerHasseResolventKernel_triangular.hsPow_diagonal,
    deningerMeyerHasseResolventKernel_diagonal]

end RHTower
