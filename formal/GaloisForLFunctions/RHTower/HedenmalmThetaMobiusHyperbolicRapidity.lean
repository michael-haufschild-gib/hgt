import GaloisForLFunctions.RHTower.HedenmalmThetaSourceJuliaPythagoras
import GaloisForLFunctions.RHTower.HedenmalmThetaGreenHyperbolicGaugeNoGo

/-!
# Hyperbolic rapidity of the normalized Möbius source aperture

P-G39 identifies the normalized source Hardy overlap and Xi Ward Cayley
discrepancy as a Pythagorean pair.  This module proves the higher universal
principle behind that identity: the full two-sided source curve is one literal
Route R horizontal-boost orbit.

The forced rapidity is `eta(u)=log sqrt(1+2u)`.  Relative Cayley coordinate is
`tanh(eta(u)-eta(v))`, normalized Hardy overlap is the corresponding hyperbolic
secant, and the shared theta/Route-R split current is constant on the entire
curve.  Thus P's normalized Julia geometry and R's polar-gauge obstruction are
the same object, not analogous mechanisms.

This sharpens the remaining producer requirement.  No predicate using only
the conserved intrinsic current can select the wall; Euler--Gamma data must
break the boost orbit by forcing zero rapidity/Cayley coordinate in the fixed
source-selected positive frame.
-/

open Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Hyperbolic rapidity of a two-sided source aperture. -/
def mobiusCriticalTwoSidedRapidity (u : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + 2 * u))

/-- **P-G40 Cayley rapidity law.** Source Cayley discrepancy is hyperbolic
velocity between aperture rapidities. -/
theorem mobiusCriticalTwoSidedCayleyDiscrepancy_eq_tanh_rapidity_sub
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedCayleyDiscrepancy u v =
      Real.tanh
        (mobiusCriticalTwoSidedRapidity u -
          mobiusCriticalTwoSidedRapidity v) := by
  have hxu : 0 < 1 + 2 * u := by linarith
  have hxv : 0 < 1 + 2 * v := by linarith
  have hsu : 0 < Real.sqrt (1 + 2 * u) := Real.sqrt_pos.2 hxu
  have hsv : 0 < Real.sqrt (1 + 2 * v) := Real.sqrt_pos.2 hxv
  have hsuSq := Real.sq_sqrt hxu.le
  have hsvSq := Real.sq_sqrt hxv.le
  have hratio : 0 < Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v) :=
    div_pos hsu hsv
  have hsum :
      Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v) +
          (Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v))⁻¹ ≠ 0 :=
    (add_pos hratio (inv_pos.mpr hratio)).ne'
  have hsqsum :
      Real.sqrt (1 + 2 * u) ^ 2 + Real.sqrt (1 + 2 * v) ^ 2 ≠ 0 := by
    positivity
  rw [mobiusCriticalTwoSidedRapidity, mobiusCriticalTwoSidedRapidity,
    Real.tanh_eq, Real.exp_sub, Real.exp_neg, Real.exp_sub,
    Real.exp_log hsu, Real.exp_log hsv]
  have hsu0 := hsu.ne'
  have hsv0 := hsv.ne'
  have hratioFormula :
      (Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v) -
          (Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v))⁻¹) /
        (Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v) +
          (Real.sqrt (1 + 2 * u) / Real.sqrt (1 + 2 * v))⁻¹) =
      (Real.sqrt (1 + 2 * u) ^ 2 - Real.sqrt (1 + 2 * v) ^ 2) /
        (Real.sqrt (1 + 2 * u) ^ 2 + Real.sqrt (1 + 2 * v) ^ 2) := by
    field_simp [hsu0, hsv0, hsum, hsqsum]
  rw [hratioFormula, hsuSq, hsvSq]
  rw [mobiusCriticalTwoSidedCayleyDiscrepancy]

/-- **P-G40 Hardy rapidity law.** Normalized source Hardy overlap is the
hyperbolic secant of rapidity separation. -/
theorem mobiusCriticalTwoSidedUnitHardyGram_eq_inv_cosh_rapidity_sub
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedUnitHardyGram u v =
      (Real.cosh
        (mobiusCriticalTwoSidedRapidity u -
          mobiusCriticalTwoSidedRapidity v))⁻¹ := by
  have hxu : 0 < 1 + 2 * u := by linarith
  have hxv : 0 < 1 + 2 * v := by linarith
  have hsu : 0 < Real.sqrt (1 + 2 * u) := Real.sqrt_pos.2 hxu
  have hsv : 0 < Real.sqrt (1 + 2 * v) := Real.sqrt_pos.2 hxv
  have hsuSq := Real.sq_sqrt hxu.le
  have hsvSq := Real.sq_sqrt hxv.le
  rw [mobiusCriticalTwoSidedUnitHardyGram,
    mobiusCriticalTwoSidedRapidity, mobiusCriticalTwoSidedRapidity,
    Real.cosh_eq, Real.exp_sub, Real.exp_neg, Real.exp_sub,
    Real.exp_log hsu, Real.exp_log hsv]
  have hsu0 := hsu.ne'
  have hsv0 := hsv.ne'
  have hden : 1 + u + v ≠ 0 := by linarith
  field_simp [hsu0, hsv0, hden]
  nlinarith

/-- Source rapidity is injective throughout the two-sided Hilbert aperture. -/
theorem mobiusCriticalTwoSidedRapidity_eq_iff
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedRapidity u = mobiusCriticalTwoSidedRapidity v ↔
      u = v := by
  constructor
  · intro h
    have hexp := congrArg Real.exp h
    have hxu : 0 < 1 + 2 * u := by linarith
    have hxv : 0 < 1 + 2 * v := by linarith
    rw [mobiusCriticalTwoSidedRapidity,
      mobiusCriticalTwoSidedRapidity,
      Real.exp_log (Real.sqrt_pos.2 hxu),
      Real.exp_log (Real.sqrt_pos.2 hxv)] at hexp
    have hsquares := congrArg (fun x : ℝ => x ^ 2) hexp
    rw [Real.sq_sqrt hxu.le, Real.sq_sqrt hxv.le] at hsquares
    linarith
  · exact congrArg mobiusCriticalTwoSidedRapidity

/-- Null-frame point of the normalized source aperture in the common P/R
hyperbolic plane. -/
def mobiusCriticalTwoSidedHyperbolicPoint (u : ℝ) :
    RouteRHyperbolicSourcePlane :=
  (((Real.sqrt (1 + 2 * u) : ℝ) : ℂ),
    (((Real.sqrt (1 + 2 * u))⁻¹ : ℝ) : ℂ))

/-- Every normalized Möbius aperture point is literally a Route R horizontal
boost of one fixed source point. -/
theorem mobiusCriticalTwoSidedHyperbolicPoint_eq_routeRGauge
    {u : ℝ} (hu : -(1 / 2 : ℝ) < u) :
    mobiusCriticalTwoSidedHyperbolicPoint u =
      routeRHyperbolicSourceGauge
        (mobiusCriticalTwoSidedRapidity u) (1, 1) := by
  have hx : 0 < 1 + 2 * u := by linarith
  have hs : 0 < Real.sqrt (1 + 2 * u) := Real.sqrt_pos.2 hx
  apply Prod.ext
  · simp [mobiusCriticalTwoSidedHyperbolicPoint,
      routeRHyperbolicSourceGauge_apply,
      mobiusCriticalTwoSidedRapidity, Real.exp_log hs]
  · simp [mobiusCriticalTwoSidedHyperbolicPoint,
      routeRHyperbolicSourceGauge_apply,
      mobiusCriticalTwoSidedRapidity, Real.exp_neg, Real.exp_log hs]

/-- Relative source aperture motion is exactly relative Route R boost. -/
theorem mobiusCriticalTwoSidedHyperbolicPoint_relativeGauge
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedHyperbolicPoint u =
      routeRHyperbolicSourceGauge
        (mobiusCriticalTwoSidedRapidity u -
          mobiusCriticalTwoSidedRapidity v)
        (mobiusCriticalTwoSidedHyperbolicPoint v) := by
  rw [mobiusCriticalTwoSidedHyperbolicPoint_eq_routeRGauge hu,
    mobiusCriticalTwoSidedHyperbolicPoint_eq_routeRGauge hv,
    ← routeRHyperbolicSourceGauge_add]
  congr 2
  ring

/-- The intrinsic theta/Route-R split current is constant on the entire
normalized Möbius aperture curve. -/
theorem thetaGreenHyperbolicCurrent_mobiusCriticalTwoSidedHyperbolicPoint
    {u : ℝ} (hu : -(1 / 2 : ℝ) < u) :
    thetaGreenHyperbolicCurrent
        (mobiusCriticalTwoSidedHyperbolicPoint u) = -2 := by
  rw [mobiusCriticalTwoSidedHyperbolicPoint_eq_routeRGauge hu,
    thetaGreenHyperbolicCurrent_gauge]
  norm_num [thetaGreenHyperbolicCurrent, thetaGreenConjugateMomentPlane,
    routeRSplitPoincarePairing]

end

end RHTower.HedenmalmThetaSource
