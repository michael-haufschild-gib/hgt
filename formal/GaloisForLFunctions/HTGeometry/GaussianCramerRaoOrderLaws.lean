import Mathlib

/-!
# Gaussian displacement--squeezing Cramer--Rao order laws

This file formalizes the exact real-variable SLD Cramer--Rao formulas in
Das--Gupta--Sen(De)--Dhar, arXiv:2608.25870, Eqs. (5)--(8).  The formulas expose two
sign errors in the prose surrounding those equations: the squeezed--coherent
position/momentum comparison depends on displacement allocation, and the displayed
momentum-squeezing order threshold has the opposite inequality direction.

No numerical ICO claim is imported.  Every result below is an unconditional identity,
an iff classification, or a closed counterfamily.
-/

namespace HTGeometry

noncomputable section

/-- Eq. (5): SLD Cramer--Rao bound for a displaced--squeezed probe.
The signed parameter `xi` is positive for position squeezing and negative for
momentum squeezing. -/
def displacedSqueezedSLDCRB (r xi betaX betaP : ℝ) : ℝ :=
  Real.cosh (r + xi) ^ 2 +
    (Real.exp (2 * r) * betaX ^ 2 + Real.exp (-2 * r) * betaP ^ 2) / 2

/-- Eq. (6): SLD Cramer--Rao bound for a squeezed--coherent probe. -/
def squeezedCoherentSLDCRB (r xi betaX betaP : ℝ) : ℝ :=
  Real.cosh (r + xi) ^ 2 +
    (Real.exp (2 * (r + xi)) * betaX ^ 2 +
      Real.exp (-2 * (r + xi)) * betaP ^ 2) / 2

/-- The displaced--squeezed position-minus-momentum difference is exactly the
hyperbolic product stated after Eqs. (5)--(6). -/
theorem displacedSqueezedSLDCRB_position_sub_momentum
    (r zeta betaX betaP : ℝ) :
    displacedSqueezedSLDCRB r zeta betaX betaP -
        displacedSqueezedSLDCRB r (-zeta) betaX betaP =
      Real.sinh (2 * r) * Real.sinh (2 * zeta) := by
  simp only [displacedSqueezedSLDCRB]
  rw [show r + -zeta = r - zeta by ring, Real.cosh_add, Real.cosh_sub,
    Real.sinh_two_mul, Real.sinh_two_mul]
  ring

/-- For nonnegative encoding and probe squeezing, momentum squeezing is never worse
for the displaced--squeezed order. -/
theorem displacedSqueezedSLDCRB_momentum_le_position
    (r zeta : {x : ℝ // 0 ≤ x}) (betaX betaP : ℝ) :
    displacedSqueezedSLDCRB r (-zeta) betaX betaP ≤
      displacedSqueezedSLDCRB r zeta betaX betaP := by
  rw [← sub_nonneg]
  rw [displacedSqueezedSLDCRB_position_sub_momentum]
  exact mul_nonneg
    (Real.sinh_nonneg_iff.mpr (by nlinarith [r.property]))
    (Real.sinh_nonneg_iff.mpr (by nlinarith [zeta.property]))

/-- Exact correction to the claim following Eqs. (5)--(6): for the reversed
preparation order, displacement anisotropy contributes to the direction comparison. -/
theorem squeezedCoherentSLDCRB_position_sub_momentum
    (r zeta betaX betaP : ℝ) :
    squeezedCoherentSLDCRB r zeta betaX betaP -
        squeezedCoherentSLDCRB r (-zeta) betaX betaP =
      Real.sinh (2 * zeta) *
        (Real.sinh (2 * r) + Real.exp (2 * r) * betaX ^ 2 -
          Real.exp (-2 * r) * betaP ^ 2) := by
  have hcosh :
      Real.cosh (r + zeta) ^ 2 - Real.cosh (r - zeta) ^ 2 =
        Real.sinh (2 * r) * Real.sinh (2 * zeta) := by
    rw [Real.cosh_add, Real.cosh_sub, Real.sinh_two_mul, Real.sinh_two_mul]
    ring
  have hdisp :
      (Real.exp (2 * (r + zeta)) * betaX ^ 2 +
          Real.exp (-2 * (r + zeta)) * betaP ^ 2) / 2 -
        (Real.exp (2 * (r - zeta)) * betaX ^ 2 +
          Real.exp (-2 * (r - zeta)) * betaP ^ 2) / 2 =
      Real.sinh (2 * zeta) *
        (Real.exp (2 * r) * betaX ^ 2 - Real.exp (-2 * r) * betaP ^ 2) := by
    rw [show 2 * (r + zeta) = 2 * r + 2 * zeta by ring,
      show -2 * (r + zeta) = -2 * r + -(2 * zeta) by ring,
      show 2 * (r - zeta) = 2 * r + -(2 * zeta) by ring,
      show -2 * (r - zeta) = -2 * r + 2 * zeta by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.sinh_eq, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  simp only [squeezedCoherentSLDCRB]
  rw [show r + -zeta = r - zeta by ring]
  linarith

/-- Closed counterfamily to the paper's assertion that momentum squeezing is always
better also for squeezed--coherent probes. -/
theorem squeezedCoherent_position_lt_momentum_counterfamily
    (zeta : {x : ℝ // 0 < x}) :
    squeezedCoherentSLDCRB 0 zeta 0 1 <
      squeezedCoherentSLDCRB 0 (-zeta) 0 1 := by
  rw [← sub_neg]
  rw [squeezedCoherentSLDCRB_position_sub_momentum]
  have hs : 0 < Real.sinh (2 * (zeta : ℝ)) :=
    Real.sinh_pos_iff.mpr (by nlinarith [zeta.property])
  simpa using (neg_lt_zero.mpr hs)

/-- Exact additive difference between the two probe-preparation orders. -/
theorem squeezedCoherentSLDCRB_sub_displacedSqueezedSLDCRB
    (r xi betaX betaP : ℝ) :
    squeezedCoherentSLDCRB r xi betaX betaP -
        displacedSqueezedSLDCRB r xi betaX betaP =
      (Real.exp (2 * (r + xi)) * betaX ^ 2 +
          Real.exp (-2 * (r + xi)) * betaP ^ 2 -
        (Real.exp (2 * r) * betaX ^ 2 +
          Real.exp (-2 * r) * betaP ^ 2)) / 2 := by
  simp [squeezedCoherentSLDCRB, displacedSqueezedSLDCRB]
  ring

/-- Scale-coordinate form of the position-squeezed order difference.  It is the
algebraic content of Eq. (7), without divisions by possibly zero displacements. -/
def positionOrderBoundary (R Z betaX betaP : ℝ) : ℝ :=
  R ^ 2 * Z * betaX ^ 2 - betaP ^ 2

/-- Scale-coordinate form of the momentum-squeezed order difference. -/
def momentumOrderBoundary (R Z betaX betaP : ℝ) : ℝ :=
  Z * betaP ^ 2 - R ^ 2 * betaX ^ 2

/-- Corrected Eq. (7): for positive squeezing, the squeezed--coherent position branch
beats the displaced--squeezed branch exactly below the squared displacement threshold. -/
theorem squeezedCoherent_position_le_displacedSqueezed_iff
    (r betaX betaP : ℝ) (zeta : {x : ℝ // 0 < x}) :
    squeezedCoherentSLDCRB r zeta betaX betaP ≤
        displacedSqueezedSLDCRB r zeta betaX betaP ↔
      positionOrderBoundary (Real.exp (2 * r)) (Real.exp (2 * zeta)) betaX betaP ≤ 0 := by
  rw [← sub_nonpos, squeezedCoherentSLDCRB_sub_displacedSqueezedSLDCRB]
  rw [show 2 * (r + (zeta : ℝ)) = 2 * r + 2 * zeta by ring,
    show -2 * (r + (zeta : ℝ)) = -2 * r + -(2 * zeta) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_neg,
    show -2 * r = -(2 * r) by ring, Real.exp_neg]
  let R := Real.exp (2 * r)
  let Z := Real.exp (2 * (zeta : ℝ))
  have hR : 0 < R := Real.exp_pos _
  have hZ : 1 < Z := Real.one_lt_exp_iff.mpr (by nlinarith [zeta.property])
  have hfactor : 0 < (Z - 1) / (2 * R * Z) := by positivity
  have hidentity :
      (R * Z * betaX ^ 2 + R⁻¹ * Z⁻¹ * betaP ^ 2 -
          (R * betaX ^ 2 + R⁻¹ * betaP ^ 2)) / 2 =
        ((Z - 1) / (2 * R * Z)) *
          positionOrderBoundary R Z betaX betaP := by
    unfold positionOrderBoundary
    field_simp [ne_of_gt hR, ne_of_gt hZ]
    ring
  change
    ((R * Z * betaX ^ 2 + R⁻¹ * Z⁻¹ * betaP ^ 2 -
        (R * betaX ^ 2 + R⁻¹ * betaP ^ 2)) / 2 ≤ 0 ↔
      positionOrderBoundary R Z betaX betaP ≤ 0)
  rw [hidentity]
  constructor
  · intro h
    exact le_of_not_gt fun hb => (not_lt_of_ge h) (mul_pos hfactor hb)
  · intro hb
    exact mul_nonpos_of_nonneg_of_nonpos hfactor.le hb

/-- Corrected Eq. (8): its published `zeta ≥ log(...)` direction is reversed.
For positive squeezing the momentum branch wins exactly when
`exp(2 zeta) betaP² ≤ exp(4 r) betaX²`. -/
theorem squeezedCoherent_momentum_le_displacedSqueezed_iff
    (r betaX betaP : ℝ) (zeta : {x : ℝ // 0 < x}) :
    squeezedCoherentSLDCRB r (-zeta) betaX betaP ≤
        displacedSqueezedSLDCRB r (-zeta) betaX betaP ↔
      momentumOrderBoundary (Real.exp (2 * r)) (Real.exp (2 * zeta)) betaX betaP ≤ 0 := by
  rw [← sub_nonpos, squeezedCoherentSLDCRB_sub_displacedSqueezedSLDCRB]
  rw [show 2 * (r + -(zeta : ℝ)) = 2 * r + -(2 * zeta) by ring,
    show -2 * (r + -(zeta : ℝ)) = -2 * r + 2 * zeta by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_neg,
    show -2 * r = -(2 * r) by ring, Real.exp_neg]
  let R := Real.exp (2 * r)
  let Z := Real.exp (2 * (zeta : ℝ))
  have hR : 0 < R := Real.exp_pos _
  have hZ : 1 < Z := Real.one_lt_exp_iff.mpr (by nlinarith [zeta.property])
  have hfactor : 0 < (Z - 1) / (2 * R * Z) := by positivity
  have hidentity :
      (R * Z⁻¹ * betaX ^ 2 + R⁻¹ * Z * betaP ^ 2 -
          (R * betaX ^ 2 + R⁻¹ * betaP ^ 2)) / 2 =
        ((Z - 1) / (2 * R * Z)) *
          momentumOrderBoundary R Z betaX betaP := by
    unfold momentumOrderBoundary
    field_simp [ne_of_gt hR, ne_of_gt hZ]
    ring
  change
    ((R * Z⁻¹ * betaX ^ 2 + R⁻¹ * Z * betaP ^ 2 -
        (R * betaX ^ 2 + R⁻¹ * betaP ^ 2)) / 2 ≤ 0 ↔
      momentumOrderBoundary R Z betaX betaP ≤ 0)
  rw [hidentity]
  constructor
  · intro h
    exact le_of_not_gt fun hb => (not_lt_of_ge h) (mul_pos hfactor hb)
  · intro hb
    exact mul_nonpos_of_nonneg_of_nonpos hfactor.le hb

/-- Closed counterfamily to the published direction of Eq. (8). -/
theorem published_momentum_order_threshold_counterfamily
    (zeta : {x : ℝ // 0 < x}) :
    displacedSqueezedSLDCRB 0 (-zeta) 1 1 <
      squeezedCoherentSLDCRB 0 (-zeta) 1 1 := by
  have hz : 1 < Real.exp (2 * (zeta : ℝ)) :=
    Real.one_lt_exp_iff.mpr (by nlinarith [zeta.property])
  have hb : 0 < momentumOrderBoundary (Real.exp (2 * (0 : ℝ)))
      (Real.exp (2 * zeta)) 1 1 := by
    simpa [momentumOrderBoundary] using sub_pos.mpr hz
  have hnot : ¬ squeezedCoherentSLDCRB 0 (-zeta) 1 1 ≤
      displacedSqueezedSLDCRB 0 (-zeta) 1 1 := by
    rw [squeezedCoherent_momentum_le_displacedSqueezed_iff]
    linarith
  exact lt_of_not_ge hnot

end

end HTGeometry
