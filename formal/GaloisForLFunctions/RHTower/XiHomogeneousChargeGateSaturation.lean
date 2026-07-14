import GaloisForLFunctions.RHTower.XiThermalOffLineChargeSelfCubicBound

/-!
# Power saturation of homogeneous Xi charge gates

The endpoint charge gate is unchanged by taking a common positive integral power.  Consequently,
every estimate obtained by matching a degree-`k` reciprocal-height observable against the
degree-`k` endpoint-charge budget has exactly the same height content as the linear gate.
-/

open Complex

namespace RHTower

noncomputable section

/-- The degree-`k` homogeneous charge gate at charge budget `C` and squared height `y`. -/
def HomogeneousChargeGate (C y : ℝ) (k : ℕ) : Prop :=
  (4 / (y + 1)) ^ k ≤ C ^ k

/-- A charge gate after applying the same order embedding to the observable and its budget. -/
def OrderReparameterizedChargeGate
    {α : Type*} [Preorder α] (φ : ℝ → α) (C y : ℝ) : Prop :=
  φ (4 / (y + 1)) ≤ φ C

/-- **Order-reparameterization saturation law.** Powers are only one instance: every strictly
increasing reparameterization of the charge coordinate has exactly the same squared-height
content. -/
theorem orderReparameterizedChargeGate_iff_heightFloor
    {α : Type*} [Preorder α] {φ : ℝ → α} {C y : ℝ}
    (hφ : StrictMono φ) (hC : 0 < C) (hy : 0 ≤ y) :
    OrderReparameterizedChargeGate φ C y ↔ (4 - C) / C ≤ y := by
  rw [OrderReparameterizedChargeGate, hφ.le_iff_le]
  have hy1 : 0 < y + 1 := by linarith
  constructor
  · intro h
    have hmul : 4 ≤ C * (y + 1) := (div_le_iff₀ hy1).mp h
    apply (div_le_iff₀ hC).2
    nlinarith
  · intro h
    have hmul : 4 - C ≤ y * C := (div_le_iff₀ hC).mp h
    apply (div_le_iff₀ hy1).2
    nlinarith

/-- Any two order-embedded presentations of the endpoint charge are logically identical. -/
theorem orderReparameterizedChargeGate_invariant
    {α β : Type*} [Preorder α] [Preorder β]
    {φ : ℝ → α} {ψ : ℝ → β} {C y : ℝ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hC : 0 < C) (hy : 0 ≤ y) :
    OrderReparameterizedChargeGate φ C y ↔
      OrderReparameterizedChargeGate ψ C y := by
  rw [orderReparameterizedChargeGate_iff_heightFloor hφ hC hy,
    orderReparameterizedChargeGate_iff_heightFloor hψ hC hy]

/-- **Homogeneous charge-floor law.** Every nonzero power of the endpoint charge gate is exactly
equivalent to the same unpowered squared-height floor. -/
theorem homogeneousChargeGate_iff_heightFloor
    {C y : ℝ} {k : ℕ}
    (hC : 0 < C) (hy : 0 ≤ y) (hk : k ≠ 0) :
    HomogeneousChargeGate C y k ↔ (4 - C) / C ≤ y := by
  rw [HomogeneousChargeGate,
    pow_le_pow_iff_left₀ (by positivity : 0 ≤ 4 / (y + 1)) hC.le hk]
  have hy1 : 0 < y + 1 := by linarith
  constructor
  · intro h
    have hmul : 4 ≤ C * (y + 1) := (div_le_iff₀ hy1).mp h
    apply (div_le_iff₀ hC).2
    nlinarith
  · intro h
    have hmul : 4 - C ≤ y * C := (div_le_iff₀ hC).mp h
    apply (div_le_iff₀ hy1).2
    nlinarith

/-- **Power-invariant saturation law.** Any two positive integral powers of the same charge budget
carry identical squared-height information. -/
theorem homogeneousChargeGate_power_invariant
    {C y : ℝ} {k l : ℕ}
    (hC : 0 < C) (hy : 0 ≤ y) (hk : k ≠ 0) (hl : l ≠ 0) :
    HomogeneousChargeGate C y k ↔ HomogeneousChargeGate C y l := by
  rw [homogeneousChargeGate_iff_heightFloor hC hy hk,
    homogeneousChargeGate_iff_heightFloor hC hy hl]

/-- The exact completed Xi curvature specializes every homogeneous gate to one and the same
source-selected height floor. -/
theorem xiCompletedCurvature_homogeneousChargeGate_iff_heightFloor
    {y : ℝ} {k : ℕ} (hy : 0 ≤ y) (hk : k ≠ 0) :
    HomogeneousChargeGate xiEndpointCompletedCurvature y k ↔
      (4 - xiEndpointCompletedCurvature) / xiEndpointCompletedCurvature ≤ y :=
  homogeneousChargeGate_iff_heightFloor xiEndpointCompletedCurvature_pos hy hk

/-- Every off-line Xi zero satisfies every powered completed-curvature gate, but all of those
gates are merely restatements of its linear quartet charge floor. -/
theorem xiZeroCopy_homogeneousChargeGate_all_powers
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {k : ℕ} (hk : k ≠ 0) :
    HomogeneousChargeGate xiEndpointCompletedCurvature ((q.1 : ℂ).im ^ 2) k := by
  rw [xiCompletedCurvature_homogeneousChargeGate_iff_heightFloor
    (sq_nonneg _) hk]
  have hself := four_le_offLineCharge_mul_one_add_im_sq q hoff
  have hcharge := xiEndpointOffLineCharge_le_curvature
  have hy1 : 0 ≤ (q.1 : ℂ).im ^ 2 + 1 := by positivity
  have hfull :
      4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) := by
    exact hself.trans
      (mul_le_mul_of_nonneg_right hcharge hy1)
  apply (div_le_iff₀ xiEndpointCompletedCurvature_pos).2
  nlinarith

end

end RHTower
