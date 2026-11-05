import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget

/-!
# Relative variation on an isolated cluster

Multiplication by the isolation radius removes the singularity of the camera
variation rate. A polynomial annulus ratio therefore gives quarter accuracy
even when the outer radius is exponentially small in a cubic logarithm.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Scaling the relative variation by the isolation radius removes its singularity. -/
theorem isolation_mul_slowRate_le_one {H L η ε C0 : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η) (hη1 : η ≤ 1) (hC0 : 0 ≤ C0) :
    η * slowRate H L η ε C0 ≤ slowRate H L 1 ε C0 := by
  have hσ0 : 0 ≤ windowSlack H L := by unfold windowSlack; linarith only [hH, hL]
  have hmin0 : 0 < min η (H / 2) := lt_min hη (by positivity)
  have hmin10 : 0 < min 1 (H / 2) := lt_min zero_lt_one (by positivity)
  have hscaled : η * min 1 (H / 2) ≤ min η (H / 2) := by
    apply le_min
    · calc η * min 1 (H / 2) ≤ η * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hη.le
        _ = η := mul_one _
    · calc η * min 1 (H / 2) ≤ 1 * min 1 (H / 2) :=
          mul_le_mul_of_nonneg_right hη1 hmin10.le
        _ ≤ H / 2 := by rw [one_mul]; exact min_le_right _ _
  have hdiv : η / min η (H / 2) ≤ 1 / min 1 (H / 2) := by
    apply (div_le_div_iff₀ hmin0 hmin10).mpr
    simpa only [one_mul] using hscaled
  have hinside : η * (1 + windowSlack H L / min η (H / 2)) ≤
      1 + windowSlack H L / min 1 (H / 2) := by
    have hh := mul_le_mul_of_nonneg_left hdiv hσ0
    calc η * (1 + windowSlack H L / min η (H / 2)) =
        η + windowSlack H L * (η / min η (H / 2)) := by ring
      _ ≤ 1 + windowSlack H L * (1 / min 1 (H / 2)) := add_le_add hη1 hh
      _ = 1 + windowSlack H L / min 1 (H / 2) := by ring
  have hprod : η * productRate H (windowSlack H L) (min η (H / 2)) ≤
      productRate H (windowSlack H L) (min 1 (H / 2)) := by
    have hf : 0 ≤ 64 * windowSlack H L / H ^ 2 * latticeSumConst :=
      mul_nonneg (div_nonneg (by positivity) (sq_nonneg H)) latticeSumConst_nonneg
    have hh := mul_le_mul_of_nonneg_left hinside hf
    calc η * productRate H (windowSlack H L) (min η (H / 2)) =
        (64 * windowSlack H L / H ^ 2 * latticeSumConst) *
          (η * (1 + windowSlack H L / min η (H / 2))) := by unfold productRate; ring
      _ ≤ (64 * windowSlack H L / H ^ 2 * latticeSumConst) *
          (1 + windowSlack H L / min 1 (H / 2)) := hh
      _ = productRate H (windowSlack H L) (min 1 (H / 2)) := by unfold productRate; ring
  have h1 : η * (2 * (π / H) * Real.exp (π / H)) ≤
      2 * (π / H) * Real.exp (π / H) := by
    have hh := mul_le_mul_of_nonneg_right hη1
      (by positivity : 0 ≤ 2 * (π / H) * Real.exp (π / H))
    simpa only [one_mul] using hh
  have h2 : η * (2 * (C0 * Real.exp (2 * ε))) ≤ 2 * (C0 * Real.exp (2 * ε)) := by
    have hh := mul_le_mul_of_nonneg_right hη1
      (by positivity : 0 ≤ 2 * (C0 * Real.exp (2 * ε)))
    simpa only [one_mul] using hh
  unfold slowRate
  linarith only [h1, h2, hprod]

/-- At polynomially large annulus ratio, the camera is almost constant on the inner cluster,
even when the isolation radius itself is exponentially small in a cubic logarithm. -/
theorem cluster_relative_error_le_quarter {lam β ℓ T u D C₀ ε η r : ℝ}
    (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hlam : 0 < lam)
    (hβlam : β ≤ lam) (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC : |C₀| ≤ ℓ * D)
    (hε : ε = β * u / 8) (hbig : 6 * slowConst lam ℓ 0 ≤ Real.exp u)
    (hT4 : 4 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hr : r ≤ η * T ^ (-(slowExponent lam + 2))) :
    r * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1) ≤ 1 / 4 := by
  have hD0 : 0 < D := by linarith only [hD1]
  have hT0 : 0 < T := by linarith only [hT4]
  have hΛ0 : 0 ≤ slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 :=
    slowRate_nonneg (by positivity : (0 : ℝ) < 2 * D⁻¹)
      (localSlack_nonneg hD0) hη (zero_le_one : (0 : ℝ) ≤ 1)
  have hunit := six_slowRate_le_rpow (M' := 0) (η := 1) hu1 hTu (le_refl 0) hlam hβlam hD1 hDup hC hε
    (by rw [neg_zero, Real.rpow_zero]) hbig
  simp only [zero_add] at hunit
  have hscaled : η * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 ≤
      slowRate (2 * D⁻¹) (localSlack D C₀) 1 ε 1 :=
    isolation_mul_slowRate_le_one
      (by positivity : (0 : ℝ) < 2 * D⁻¹) (localSlack_nonneg hD0) hη hη1 zero_le_one
  have hscale : η * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1) ≤ T ^ slowExponent lam := by
    linarith only [hscaled, hunit]
  have he : T ^ (-(slowExponent lam + 2)) * T ^ slowExponent lam = T ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hT0]; congr 1; ring
  have hsmall : T ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hT0.le, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
    nlinarith only [hT4]
  calc r * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1)
      ≤ (η * T ^ (-(slowExponent lam + 2))) *
          (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ = T ^ (-(slowExponent lam + 2)) *
        (η * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1)) := by ring
    _ ≤ T ^ (-(slowExponent lam + 2)) * T ^ slowExponent lam :=
      mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hT0.le _)
    _ ≤ 1 / 4 := he ▸ hsmall

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.isolation_mul_slowRate_le_one
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cluster_relative_error_le_quarter
