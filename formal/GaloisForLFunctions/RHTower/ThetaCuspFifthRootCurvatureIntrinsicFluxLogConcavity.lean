import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicBalance
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredNormalizedFluxLogConvexNoGo

/-!
# Intrinsic C5 minima force normalized-flux log-concavity

This module closes C5-FLC1.  Normalize a hypothetical negative intrinsic-C5 minimum by

`x = tD/A`, `y = tJ/D`, `z = t²K/D`,

where `A` is accumulated source drop and `D,J,K` are the first three flux jets.  Projective
decrease gives `0 < x ≤ 2`, while intrinsic stationarity gives one exact affine relation.  If
`d > 0` is the normalized C5 deficit, elimination yields

`125 x² (z-y²-y+2)
  = -20(x-2)²(x²+36) - 5d(5x²-24x+48) - 5d² < 0`.

The left factor is exactly the division-free second logarithmic derivative of the normalized
positive flux `D(√s)/√s` in squared displacement.  Thus every negative intrinsic-C5 minimum is
strictly flux-log-concave.  This kills stationary local flux-log-convexity as an independent
consequence of the existing projective chamber: establishing nonnegative curvature there is
already equivalent to global modular-center C5.  A surviving proof must exclude this explicit
strict-negative chamber using genuinely nonlocal earlier-flux information.

The RH chain served is: nonlocal exclusion of this chamber -> modular-center C5 -> off-center
direct-J/rank-four wall -> higher-packet/no-escape transport -> CLG/TTF or Weil positivity -> RH.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact stationary-C5 certificate.  If `d` is the positive deficit of normalized C5, then the
normalized squared-flux log-curvature numerator is a sum of three nonpositive terms. -/
theorem stationary_c5_fluxLogCurvature_certificate
    {x y z : ℝ}
    (hstationary :
      39 + y - 17 * x + 5 * z - 3 * x * y =
        2 * (24 - 9 * x + 5 * x * y - 4 * x ^ 2)) :
    let d := -(24 - 9 * x + 5 * x * y - 4 * x ^ 2)
    125 * x ^ 2 * (z - y ^ 2 - y + 2) =
      -20 * (x - 2) ^ 2 * (x ^ 2 + 36) -
        5 * d * (5 * x ^ 2 - 24 * x + 48) - 5 * d ^ 2 := by
  dsimp only
  have hz :
      5 * z = 9 - x + 13 * x * y - 8 * x ^ 2 - y := by
    linarith
  linear_combination 25 * x ^ 2 * hz

private theorem stationary_negative_c5_forces_flux_logCurvature_neg
    {x y z : ℝ}
    (hx : 0 < x) (hxle : x ≤ 2)
    (hneg : 24 - 9 * x + 5 * x * y - 4 * x ^ 2 < 0)
    (hstationary :
      39 + y - 17 * x + 5 * z - 3 * x * y =
        2 * (24 - 9 * x + 5 * x * y - 4 * x ^ 2)) :
    z - y ^ 2 - y + 2 < 0 := by
  let d := -(24 - 9 * x + 5 * x * y - 4 * x ^ 2)
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hc : 0 < 5 * x ^ 2 - 24 * x + 48 := by
    nlinarith [sq_nonneg (x - 2)]
  have hcertificate :
      125 * x ^ 2 * (z - y ^ 2 - y + 2) =
        -20 * (x - 2) ^ 2 * (x ^ 2 + 36) -
          5 * d * (5 * x ^ 2 - 24 * x + 48) - 5 * d ^ 2 := by
    simpa only [d] using stationary_c5_fluxLogCurvature_certificate hstationary
  have hright :
      -20 * (x - 2) ^ 2 * (x ^ 2 + 36) -
          5 * d * (5 * x ^ 2 - 24 * x + 48) - 5 * d ^ 2 < 0 := by
    have hfirst :
        0 ≤ 20 * (x - 2) ^ 2 * (x ^ 2 + 36) := by positivity
    have hmiddle :
        0 < 5 * d * (5 * x ^ 2 - 24 * x + 48) := by positivity
    have hlast : 0 ≤ 5 * d ^ 2 := by positivity
    linarith
  have hleft :
      125 * x ^ 2 * (z - y ^ 2 - y + 2) < 0 := by
    rw [hcertificate]
    exact hright
  have hfactor : 0 < 125 * x ^ 2 := by positivity
  by_contra hnot
  have hnonneg : 0 ≤ z - y ^ 2 - y + 2 := le_of_not_gt hnot
  have hprod : 0 ≤ 125 * x ^ 2 * (z - y ^ 2 - y + 2) :=
    mul_nonneg hfactor.le hnonneg
  linarith

private theorem stationary_negative_c5_raw_forces_flux_logCurvature_neg
    {t A D J K : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hD : 0 < D)
    (hprojective : t * D ≤ 2 * A)
    (hneg :
      24 * A ^ 2 - 9 * t * A * D +
          t ^ 2 * (5 * A * J - 4 * D ^ 2) < 0)
    (hstationary :
      (39 * A * D + t * A * J - 17 * t * D ^ 2 +
          t ^ 2 * (5 * A * K - 3 * D * J)) * A =
        2 * (24 * A ^ 2 - 9 * t * A * D +
          t ^ 2 * (5 * A * J - 4 * D ^ 2)) * D) :
    t ^ 2 * (D * K - J ^ 2) - t * D * J + 2 * D ^ 2 < 0 := by
  let x := t * D / A
  let y := t * J / D
  let z := t ^ 2 * K / D
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hxle : x ≤ 2 := by
    dsimp only [x]
    exact (div_le_iff₀ hA).2 (by linarith)
  have hscaledNeg :
      (24 * A ^ 2 - 9 * t * A * D +
          t ^ 2 * (5 * A * J - 4 * D ^ 2)) / A ^ 2 < 0 :=
    div_neg_of_neg_of_pos hneg (sq_pos_of_pos hA)
  have hdimNeg : 24 - 9 * x + 5 * x * y - 4 * x ^ 2 < 0 := by
    dsimp only [x, y]
    convert hscaledNeg using 1
    field_simp [hA.ne', hD.ne']
    ring
  have hdimStationary :
      39 + y - 17 * x + 5 * z - 3 * x * y =
        2 * (24 - 9 * x + 5 * x * y - 4 * x ^ 2) := by
    dsimp only [x, y, z]
    field_simp [hA.ne', hD.ne']
    nlinarith [hstationary]
  have hdim := stationary_negative_c5_forces_flux_logCurvature_neg
    hx hxle hdimNeg hdimStationary
  have hrawScaled :
      D ^ 2 * (z - y ^ 2 - y + 2) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hD) hdim
  dsimp only [y, z] at hrawScaled
  convert hrawScaled using 1
  field_simp [hD.ne']

/-- Division-free logarithmic curvature numerator of the normalized positive flux in squared
displacement. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator
    (u t : ℝ) : ℝ :=
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let K := thetaCuspReflectedSourceDecayFluxThirdJet u t
  t ^ 2 * (D * K - J ^ 2) - t * D * J + 2 * D ^ 2

/-- First squared-coordinate derivative of normalized positive source flux. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope (u x : ℝ) : ℝ :=
  let t := Real.sqrt x
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  (t * J - D) / (2 * t ^ 3)

/-- Second squared-coordinate derivative of normalized positive source flux. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature (u x : ℝ) : ℝ :=
  let t := Real.sqrt x
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let K := thetaCuspReflectedSourceDecayFluxThirdJet u t
  (t ^ 2 * K - 3 * t * J + 3 * D) / (4 * t ^ 5)

theorem hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFlux
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u)
      (thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u x) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hspos := Real.sqrt_pos.2 hx
  have hD :=
    (hasDerivAt_thetaCuspReflectedSourceDecayFlux u (Real.sqrt x)).comp x hs
  have hraw := hD.div hs hspos.ne'
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFlux
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp [hspos.ne']

theorem hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u)
      (thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature u x) x := by
  let s : ℝ → ℝ := Real.sqrt
  have hs : HasDerivAt s (1 / (2 * Real.sqrt x)) x := by
    simpa only [s] using Real.hasDerivAt_sqrt hx.ne'
  have hspos := Real.sqrt_pos.2 hx
  have hD :=
    (hasDerivAt_thetaCuspReflectedSourceDecayFlux u (Real.sqrt x)).comp x hs
  have hJ :=
    (hasDerivAt_thetaCuspReflectedSourceDecayFluxCurvature u (Real.sqrt x)).comp x hs
  have hnum := hs.mul hJ |>.sub hD
  have hden := (hs.pow 3).const_mul 2
  have hraw := hnum.div hden (by positivity : 2 * s x ^ 3 ≠ 0)
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature
  dsimp only [s] at hraw
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp [hspos.ne']
  ring

/-- Squared-coordinate logarithmic slope of normalized positive source flux. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u x /
    thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x

/-- Squared-coordinate logarithmic curvature of normalized positive source flux. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature
    (u x : ℝ) : ℝ :=
  (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x *
        thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature u x -
      thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u x ^ 2) /
    thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x ^ 2

theorem hasDerivAt_log_thetaCuspReflectedSourceSquaredNormalizedDecayFlux
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y => Real.log
        (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u y))
      (thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope u x) x := by
  have hflux :=
    hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFlux u hx
  have hpos := thetaCuspReflectedSourceSquaredNormalizedDecayFlux_pos u hx
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope
  exact hflux.log hpos.ne'

theorem hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope u)
      (thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature u x) x := by
  have hslope :=
    hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u hx
  have hflux :=
    hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFlux u hx
  have hpos := thetaCuspReflectedSourceSquaredNormalizedDecayFlux_pos u hx
  have hraw := hslope.div hflux hpos.ne'
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring

/-- Exact bridge from the intrinsic jet polynomial to the ordinary curvature determinant of
normalized flux in squared displacement. -/
theorem thetaCuspReflectedSourceSquaredNormalizedDecayFlux_curvatureDeterminant_eq
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceSquaredNormalizedDecayFlux u (t ^ 2) *
          thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature u (t ^ 2) -
        thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope u (t ^ 2) ^ 2 =
      thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator u t /
        (4 * t ^ 6) := by
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFlux
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxCurvature
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  field_simp [ht.ne']
  ring

/-- Exact logarithmic-curvature quotient at a positive displacement. -/
theorem thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_sq_eq
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature u (t ^ 2) =
      thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator u t /
        (4 * t ^ 4 * thetaCuspReflectedSourceDecayFlux u t ^ 2) := by
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature
  rw [thetaCuspReflectedSourceSquaredNormalizedDecayFlux_curvatureDeterminant_eq u ht]
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFlux
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  field_simp [ht.ne', (thetaCuspReflectedSourceDecayFlux_pos u ht).ne']

/-- Every negative local minimum of intrinsic C5 has strictly negative local logarithmic
curvature for the normalized source flux in squared displacement. -/
theorem
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator_neg_of_intrinsicBalance_localMin_neg
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t)
    (hneg : thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t < 0) :
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator u t < 0 := by
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hD := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hprojective := thetaCuspReflectedSourceProjectiveDecreaseDefect_nonneg u ht
  have hNneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff u ht).mp hneg
  have hstationary :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
      u ht hmin
  have hraw := stationary_negative_c5_raw_forces_flux_logCurvature_neg
    ht hA hD (by linarith :
      t * thetaCuspReflectedSourceDecayFlux u t ≤
        2 * thetaCuspReflectedSourceFirstDrop u t)
    (by
      simpa only [thetaCuspReflectedSourceFifthRootCurvatureNumerator] using hNneg)
    (by
      simpa only [thetaCuspReflectedSourceFifthRootCurvatureVelocity,
        thetaCuspReflectedSourceFifthRootCurvatureNumerator] using hstationary)
  simpa only [thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator]
    using hraw

/-- Differential form of the obstruction: the second squared-coordinate derivative of the
normalized-flux logarithm is strictly negative at every negative intrinsic-C5 local minimum. -/
theorem
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_neg_of_intrinsicBalance_localMin_neg
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t)
    (hneg : thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t < 0) :
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature u (t ^ 2) < 0 := by
  rw [thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_sq_eq u ht]
  have hden :
      0 < 4 * t ^ 4 * thetaCuspReflectedSourceDecayFlux u t ^ 2 := by
    exact mul_pos (mul_pos (by norm_num) (pow_pos ht 4))
      (sq_pos_of_pos (thetaCuspReflectedSourceDecayFlux_pos u ht))
  exact div_neg_of_neg_of_pos
    (thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvatureNumerator_neg_of_intrinsicBalance_localMin_neg
      u ht hmin hneg)
    hden

/-- A modular-center C5 failure therefore supplies a strict local log-concavity witness for the
normalized theta-source flux in squared displacement. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_normalizedFluxLogCurvature_neg
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t ∧
      thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature 0 (t ^ 2) < 0 := by
  obtain ⟨t, ht, hneg, hmin, _⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicBalance_localMin
      hfail
  exact ⟨t, ht, hneg, hmin,
    thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_neg_of_intrinsicBalance_localMin_neg
      0 ht hmin hneg⟩

/-- Exact C5 burden reduction.  Global modular-center C5 is equivalent to excluding the strict
local flux-log-concavity chamber forced at every hypothetical negative intrinsic minimum. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicMin_normalizedFluxLogCurvature_nonneg :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        IsLocalMin
          (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t →
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 →
        0 ≤ thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature 0 (t ^ 2) := by
  constructor
  · intro hglobal t ht _ hneg
    have hNneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff 0 ht).mp hneg
    exact (not_lt_of_ge (hglobal t ht) hNneg).elim
  · intro hlocal t ht
    by_contra hnot
    obtain ⟨s, hs, hsneg, hsmin, hslogneg⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_normalizedFluxLogCurvature_neg
        ⟨t, ht, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge (hlocal s hs hsmin hsneg)) hslogneg

/-- Closed stationary local-log-convexity no-go: negative intrinsic C5 and nonnegative local
normalized-flux log curvature cannot coexist. -/
theorem
    not_exists_thetaCuspReflectedSource_intrinsicBalance_localMin_neg_and_normalizedFluxLogCurvature_nonneg
    (u : ℝ) :
    ¬ ∃ t : ℝ, 0 < t ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t < 0 ∧
      0 ≤ thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature u (t ^ 2) := by
  rintro ⟨t, ht, hmin, hneg, hnonneg⟩
  exact (not_lt_of_ge hnonneg)
    (thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_neg_of_intrinsicBalance_localMin_neg
      u ht hmin hneg)

end

end RHTower
