import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakNormalizedGibbsForce

/-!
# Exact finite-parameter correction of the aligned physical force

The pulled-back force separates the original odd kernel correction,
the shift of its leading cubic, the inverse-coordinate Jacobian, and
the normalization by the true barrier. Their critical contributions
cancel identically as a polynomial in the aligned radius coordinate.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

abbrev EGBAlignedForceState := EGBGibbsOddState × ℝ × ℝ × ℝ × ℝ

def egbFixedChargeAAlignedForceState (w φ τ l : ℝ) : EGBAlignedForceState :=
  (egbFixedChargeAGibbsOddState w φ τ,
   egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ,
   egbFixedChargeAMiddleGapCoordinate τ φ,
   (egbFixedChargeAGibbsBarrierScale w φ τ l - egbFixedChargeAGibbsBarrierCoefficient w φ) / egbCoexistenceASymmetricRatio τ,
   egbFixedChargeAGibbsBarrierScale w φ τ l)

def egbFixedChargeAAlignedForceCriticalState (w φ : ℝ) : EGBAlignedForceState :=
  (egbFixedChargeAGibbsOddCriticalState w φ, egbFixedChargeAMiddleMeanCorrection φ, 0, 0,
   egbFixedChargeAGibbsBarrierCoefficient w φ)

def egbFixedChargeAAlignedForceRationalFamily (w φ : ℝ) (p : EGBAlignedForceState) (t : ℝ) : ℝ :=
  let k := p.2.1
  let c := p.2.2.1
  let y := (t + c) / (1 + c * t)
  let j := (1 - c ^ (2 : ℕ)) / (1 + c * t) ^ (2 : ℕ)
  let y₁ := k * (1 - t ^ (2 : ℕ)) / (1 + c * t)
  let j₁ := -k * (2 * t + c * (1 + t ^ (2 : ℕ))) / (1 + c * t) ^ (2 : ℕ)
  (egbFixedChargeAGibbsOddRationalFamily w φ p.1 y * j +
    4 * egbFixedChargeAGibbsBarrierCoefficient w φ * y₁ * (y ^ (2 : ℕ) + y * t + t ^ (2 : ℕ) - 1) * j +
    egbFixedChargeAGibbsLeadingKernel w φ t * j₁ -
    egbFixedChargeAGibbsLeadingKernel w φ t / egbFixedChargeAGibbsBarrierCoefficient w φ * p.2.2.2.1) / p.2.2.2.2

theorem egbFixedChargeAAlignedForceState_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAAlignedForceState w φ τ l) atBot
      (𝓝 (egbFixedChargeAAlignedForceCriticalState w φ)) := by
  exact (egbFixedChargeAGibbsOddState_critical_limit w φ).prodMk_nhds
    ((egbFixedChargeAMiddleGapCoordinate_linear_limit φ).prodMk_nhds
    ((egbFixedChargeAMiddleGapCoordinate_critical_limit φ).prodMk_nhds
    ((egbFixedChargeAGibbsBarrier_first_correction_limit w φ l).prodMk_nhds
      (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l))))

theorem egbFixedChargeAAlignedForceRationalFamily_critical (w φ t : ℝ) :
    egbFixedChargeAAlignedForceRationalFamily w φ (egbFixedChargeAAlignedForceCriticalState w φ) t = 0 := by
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  have h := (div_eq_iff (show 4 * egbFixedChargeAGibbsBarrierCoefficient w φ ≠ 0 by positivity)).mp
    (egbFixedChargeAGibbsOddCoefficient_peak_displacement w φ)
  have hC : egbFixedChargeAGibbsOddCoefficient w φ = 4 * egbFixedChargeAGibbsBarrierCoefficient w φ * egbFixedChargeAMiddleMeanCorrection φ := by
    rw [h]
    ring
  dsimp only [egbFixedChargeAAlignedForceRationalFamily, egbFixedChargeAAlignedForceCriticalState]
  simp only [zero_mul, add_zero, sub_zero, one_pow, div_one, mul_one,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  rw [egbFixedChargeAGibbsOddRationalFamily_critical]
  unfold egbFixedChargeAGibbsOddLimitKernel egbFixedChargeAGibbsLeadingKernel
  rw [hC]
  ring

theorem egbFixedChargeAPeakNormalizedGibbsForce_correction_formula (w φ τ l ψ : ℝ) :
    (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l ψ + 4 * sin ψ * cos ψ ^ (3 : ℕ)) / egbCoexistenceASymmetricRatio τ =
      egbFixedChargeAAlignedForceRationalFamily w φ (egbFixedChargeAAlignedForceState w φ τ l) (sin ψ) * cos ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hq := egbFixedChargeAGibbsBarrierScale_pos w φ τ l
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  have hy := egbFixedChargeAPeakInverseCoordinate_formula τ φ ψ
  have hy₁ := egbFixedChargeAPeakInverseCoordinate_linear_formula τ φ ψ
  have hj₁ := egbFixedChargeAPeakInverseJacobian_linear_formula τ φ ψ
  have hs : cos ψ ^ (2 : ℕ) = 1 - sin ψ ^ (2 : ℕ) := by linarith [sin_sq_add_cos_sq ψ]
  rw [hs] at hy₁
  have hk := egbFixedChargeAGibbsOddKernel_rational_family w φ τ
    (egbFixedChargeAPeakInverseCoordinate_bounds τ φ ψ)
  dsimp only [egbFixedChargeAAlignedForceRationalFamily, egbFixedChargeAAlignedForceState]
  rw [← hy, ← hy₁, ← hj₁, ← hk]
  have hlead : 4 * sin ψ * cos ψ ^ (3 : ℕ) =
      -(egbFixedChargeAGibbsLeadingKernel w φ (sin ψ) / egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ) := by
    have ht : sin ψ ^ (2 : ℕ) - 1 = -(cos ψ ^ (2 : ℕ)) := by linarith [sin_sq_add_cos_sq ψ]
    unfold egbFixedChargeAGibbsLeadingKernel
    rw [ht]
    field_simp [hB.ne'] <;> ring
  rw [hlead]
  change (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l ψ -
    egbFixedChargeAGibbsLeadingKernel w φ (sin ψ) / egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ) / egbCoexistenceASymmetricRatio τ =
    (egbFixedChargeAGibbsOddKernel w φ τ (egbFixedChargeAPeakInverseCoordinate τ φ ψ) * egbFixedChargeAPeakInverseJacobian τ φ ψ +
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ *
        ((egbFixedChargeAPeakInverseCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ) *
        (egbFixedChargeAPeakInverseCoordinate τ φ ψ ^ (2 : ℕ) + egbFixedChargeAPeakInverseCoordinate τ φ ψ * sin ψ + sin ψ ^ (2 : ℕ) - 1) *
        egbFixedChargeAPeakInverseJacobian τ φ ψ +
      egbFixedChargeAGibbsLeadingKernel w φ (sin ψ) * ((egbFixedChargeAPeakInverseJacobian τ φ ψ - 1) / egbCoexistenceASymmetricRatio τ) -
      egbFixedChargeAGibbsLeadingKernel w φ (sin ψ) / egbFixedChargeAGibbsBarrierCoefficient w φ *
        ((egbFixedChargeAGibbsBarrierScale w φ τ l - egbFixedChargeAGibbsBarrierCoefficient w φ) / egbCoexistenceASymmetricRatio τ)) /
      egbFixedChargeAGibbsBarrierScale w φ τ l * cos ψ
  unfold egbFixedChargeAPeakNormalizedGibbsForce egbFixedChargeAGibbsOddKernel egbFixedChargeAGibbsLeadingKernel
  field_simp [hd.ne', hq.ne', hB.ne'] <;> ring

end GaloisForLFunctions.HTGeometry
