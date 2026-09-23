import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalParabolicConnection
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientSourceEnvelope

/-!
# Projective boundary of the Route-P terminal parabolic connection

The literal terminal parabolic lift has a forced connection height tending to
negative infinity.  This is not a failure of terminal transport: after the
source-defined singular normalization by the product of the physical wall
radius and prime-power mass, it has one fixed projective boundary flag.

The result supplies the terminal boundary datum for an unbounded graph domain.
It neither identifies the ordered two-Julia source pairing with a graph pairing
nor bounds that pairing cofinally; those remain the RH-bearing obstruction.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Physical square-root wall radius used by the terminal projective normalization. -/
def routePTerminalProjectiveWallRadius (K : ℕ) : ℝ :=
  Real.sqrt ((K + 3 : ℕ) : ℝ) - 1

/-- Source-forced singular normalization of the terminal homogeneous lift. -/
def routePTerminalProjectiveScale (K : ℕ) : ℝ :=
  (4 * ccmActualHeadParabolicMass K * routePTerminalProjectiveWallRadius K)⁻¹

/-- The unique vertical null flag reached by the normalized literal terminal orbit. -/
def routePTerminalProjectiveBoundary : Fin 4 → ℝ := ![0, 0, -1, 0]

/-- **Terminal projective-boundary law.** The divergent homogeneous terminal
connection has an unconditional, source-faithful projective limit.  Its
horizontal terminal coordinates and affine coordinate vanish; its connection
height supplies the surviving vertical flag. -/
theorem tendsto_routePTerminalProjectiveScale_smul_homogeneousLift :
    Tendsto (fun K : ℕ => routePTerminalProjectiveScale K •
      routePTerminalHomogeneousLift K) atTop
      (nhds routePTerminalProjectiveBoundary) := by
  let m : ℕ → ℝ := ccmActualHeadParabolicMass
  let s : ℕ → ℝ := routePTerminalProjectiveWallRadius
  have hm : Tendsto m atTop atTop := ccmActualHeadParabolicMass_tendsto_atTop
  have hmInv : Tendsto (fun K => (m K)⁻¹) atTop (nhds 0) := by
    change Tendsto m⁻¹ atTop (nhds 0)
    exact hm.inv_tendsto_atTop
  have hcast : Tendsto (fun K : ℕ => ((K + 3 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
  have hsqrt : Tendsto (fun K : ℕ => Real.sqrt ((K + 3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hs : Tendsto s atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1 : ℝ) hsqrt using 1
    funext K
    simp only [s, routePTerminalProjectiveWallRadius]
    ring
  have hsInv : Tendsto (fun K => (s K)⁻¹) atTop (nhds 0) := by
    change Tendsto s⁻¹ atTop (nhds 0)
    exact hs.inv_tendsto_atTop
  have hmsInv : Tendsto (fun K => (m K * s K)⁻¹) atTop (nhds 0) := by
    simpa [mul_inv, mul_comm] using hmInv.mul hsInv
  have hmpos (K : ℕ) : 0 < m K := by
    exact ccmActualHeadParabolicMass_pos K
  have hspos (K : ℕ) : 0 < s K := by
    dsimp [s, routePTerminalProjectiveWallRadius]
    have hN : (1 : ℝ) < ((K + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < K + 3 by omega)
    have hsq : 1 < Real.sqrt ((K + 3 : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt (by positivity)]
      exact hN
    nlinarith [Real.sqrt_nonneg ((K + 3 : ℕ) : ℝ)]
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · have hid (K : ℕ) :
        (4 * m K * s K)⁻¹ * (m K + 2 * s K) =
          (1 / 4 : ℝ) * (s K)⁻¹ + (1 / 2 : ℝ) * (m K)⁻¹ := by
        field_simp [(hmpos K).ne', (hspos K).ne']
        ring
    have hsPart : Tendsto (fun K : ℕ =>
        (1 / 4 : ℝ) * (s K)⁻¹) atTop (nhds 0) := by
      simpa using hsInv.const_mul (1 / 4 : ℝ)
    have hmPart : Tendsto (fun K : ℕ =>
        (1 / 2 : ℝ) * (m K)⁻¹) atTop (nhds 0) := by
      simpa using hmInv.const_mul (1 / 2 : ℝ)
    have hlim : Tendsto (fun K : ℕ =>
        (1 / 4 : ℝ) * (s K)⁻¹ + (1 / 2 : ℝ) * (m K)⁻¹)
        atTop (nhds 0) := by
      simpa using hsPart.add hmPart
    change Tendsto (fun K : ℕ =>
      routePTerminalProjectiveScale K * routePTerminalBoundary K)
      atTop (nhds (routePTerminalProjectiveBoundary 0))
    simp only [routePTerminalProjectiveBoundary]
    convert hlim using 1
    · funext K
      rw [show routePTerminalBoundary K = m K + 2 * s K by
        simp only [routePTerminalBoundary, m, s, routePTerminalProjectiveWallRadius]
        rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold]]
      exact hid K
    · norm_num [routePTerminalProjectiveBoundary]
  · have hid (K : ℕ) :
        (4 * m K * s K)⁻¹ * (2 * s K - m K) =
          (1 / 2 : ℝ) * (m K)⁻¹ - (1 / 4 : ℝ) * (s K)⁻¹ := by
        field_simp [(hmpos K).ne', (hspos K).ne']
        ring
    have hmPart : Tendsto (fun K : ℕ =>
        (1 / 2 : ℝ) * (m K)⁻¹) atTop (nhds 0) := by
      simpa using hmInv.const_mul (1 / 2 : ℝ)
    have hsPart : Tendsto (fun K : ℕ =>
        (1 / 4 : ℝ) * (s K)⁻¹) atTop (nhds 0) := by
      simpa using hsInv.const_mul (1 / 4 : ℝ)
    have hlim : Tendsto (fun K : ℕ =>
        (1 / 2 : ℝ) * (m K)⁻¹ - (1 / 4 : ℝ) * (s K)⁻¹)
        atTop (nhds 0) := by
      simpa using hmPart.sub hsPart
    change Tendsto (fun K : ℕ =>
      routePTerminalProjectiveScale K * routePTerminalDisplacement K)
      atTop (nhds (routePTerminalProjectiveBoundary 1))
    simp only [routePTerminalProjectiveBoundary]
    convert hlim using 1
    · funext K
      rw [show routePTerminalDisplacement K = 2 * s K - m K by
        simp only [routePTerminalDisplacement, m, s, routePTerminalProjectiveWallRadius]
        rw [speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]]
      exact hid K
    · norm_num [routePTerminalProjectiveBoundary]
  · have hheight (K : ℕ) : routePTerminalConnectionHeight K =
        (routePTerminalBoundary 0 ^ (2 : ℕ) - routePTerminalDisplacement 0 ^ (2 : ℕ) -
          8 * m K * s K) / 2 := by
      unfold routePTerminalConnectionHeight
      rw [show routePTerminalBoundary K ^ (2 : ℕ) - routePTerminalDisplacement K ^ (2 : ℕ) =
          8 * m K * s K by
        simp only [routePTerminalBoundary, routePTerminalDisplacement, m, s,
          routePTerminalProjectiveWallRadius]
        exact ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sq_sub_errorDisplacement_sq K]
    have hid (K : ℕ) :
        (4 * m K * s K)⁻¹ * routePTerminalConnectionHeight K =
          ((routePTerminalBoundary 0 ^ (2 : ℕ) - routePTerminalDisplacement 0 ^ (2 : ℕ)) / 8) *
            (m K * s K)⁻¹ - 1 := by
      rw [hheight K]
      field_simp [(hmpos K).ne', (hspos K).ne']
      ring
    have hmain : Tendsto (fun K : ℕ =>
        ((routePTerminalBoundary 0 ^ (2 : ℕ) - routePTerminalDisplacement 0 ^ (2 : ℕ)) / 8) *
          (m K * s K)⁻¹) atTop (nhds 0) := by
      simpa using hmsInv.const_mul
        ((routePTerminalBoundary 0 ^ (2 : ℕ) - routePTerminalDisplacement 0 ^ (2 : ℕ)) / 8)
    have hlim : Tendsto (fun K : ℕ =>
        ((routePTerminalBoundary 0 ^ (2 : ℕ) - routePTerminalDisplacement 0 ^ (2 : ℕ)) / 8) *
          (m K * s K)⁻¹ - 1) atTop (nhds (-1)) := by
      simpa using hmain.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    change Tendsto (fun K : ℕ =>
      routePTerminalProjectiveScale K * routePTerminalConnectionHeight K)
      atTop (nhds (-1))
    convert hlim using 1
    · funext K
      exact hid K
  · have hlim : Tendsto (fun K : ℕ =>
        (1 / 4 : ℝ) * (m K * s K)⁻¹) atTop (nhds 0) := by
      simpa using hmsInv.const_mul (1 / 4 : ℝ)
    change Tendsto (fun K : ℕ => routePTerminalProjectiveScale K * 1)
      atTop (nhds 0)
    convert hlim using 1
    · funext K
      simp only [routePTerminalProjectiveScale, m, s]
      field_simp [(hmpos K).ne', (hspos K).ne']

end

end RHTower
