import GaloisForLFunctions.HTGeometry.Hypergeometric.LegendreRiccati

/-!
# The symmetric square of the analytic Legendre period

The actual convergent Gauss period, not a presumed solution, satisfies a
third-order equation after squaring. Differentiating its proved
Picard--Fuchs equation supplies the third jet. All identities hold across
the origin and any period zeros inside the unit disk.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Complex HTGeometry HTGeometry.LegendrePeriod

/-- The third derivative supplied by the convergent Gauss power series. -/
def periodThirdJet (z : ℂ) : ℂ :=
  let p := ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) (1 / 2) 1
  (((p.derivSeries.derivSeries.derivSeries.sum z) 1) 1) 1

private theorem hasDerivAt_curvature (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt curvature (periodThirdJet z) z := by
  let p := ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) (1 / 2) 1
  have hzp : ‖z‖ₑ < p.radius := hz.trans_le (hypergeometric_radius_one_le _ _ _)
  have hz₂ := (hzp.trans_le p.radius_le_radius_derivSeries).trans_le
    p.derivSeries.radius_le_radius_derivSeries
  have h := p.derivSeries.derivSeries.hasFDerivAt_sum hz₂
  change HasDerivAt (fun w : ℂ => ((p.derivSeries.derivSeries.sum w) 1) 1)
    ((((p.derivSeries.derivSeries.derivSeries.sum z) 1) 1) 1) z
  simpa using ((h.clm_apply (hasFDerivAt_const (1 : ℂ) z)).clm_apply
    (hasFDerivAt_const (1 : ℂ) z)).hasDerivAt

private theorem differentiated_picardFuchs (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) * periodThirdJet z + 2 * (1 - 2 * z) * curvature z -
      (9 / 4 : ℂ) * slope z = 0 := by
  have ha : HasDerivAt (fun w : ℂ => w * (1 - w)) (1 - 2 * z) z := by
    convert (hasDerivAt_id z).mul
      ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply, id_eq]; ring)
  have hb : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul 2) using 1 <;>
      first | rfl | ring
  have h := ((ha.mul (hasDerivAt_curvature z hz)).add
    (hb.mul (hasDerivAt_slope z hz))).sub ((hasDerivAt_period z hz).div_const 4)
  have he : (fun w : ℂ => w * (1 - w) * curvature w +
      (1 - 2 * w) * slope w - period w / 4) =ᶠ[nhds z] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_enorm continuous_const).mem_nhds hz] with w hw
    exact picardFuchs w hw
  have hzder := h.congr_of_eventuallyEq he.symm
  have heq := hzder.unique (hasDerivAt_const z (0 : ℂ))
  linear_combination heq

def squaredPeriod (z : ℂ) : ℂ := period z ^ 2
def squaredPeriodSlope (z : ℂ) : ℂ := 2 * period z * slope z
def squaredPeriodCurvature (z : ℂ) : ℂ := 2 * slope z ^ 2 + 2 * period z * curvature z
def squaredPeriodThirdJet (z : ℂ) : ℂ :=
  6 * slope z * curvature z + 2 * period z * periodThirdJet z

theorem hasDerivAt_squaredPeriod (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt squaredPeriod (squaredPeriodSlope z) z := by
  convert (hasDerivAt_period z hz).pow 2 using 1 <;>
    simp [squaredPeriod, squaredPeriodSlope]

theorem hasDerivAt_squaredPeriodSlope (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt squaredPeriodSlope (squaredPeriodCurvature z) z := by
  convert ((hasDerivAt_period z hz).const_mul 2).mul (hasDerivAt_slope z hz) using 1 <;>
    first | rfl | (simp only [squaredPeriodCurvature]; ring)

theorem hasDerivAt_squaredPeriodCurvature (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt squaredPeriodCurvature (squaredPeriodThirdJet z) z := by
  convert (((hasDerivAt_slope z hz).pow 2).const_mul 2).add
    (((hasDerivAt_period z hz).const_mul 2).mul (hasDerivAt_curvature z hz)) using 1 <;>
    first | rfl | (simp only [squaredPeriodThirdJet]; ring)

/-- The actual squared period satisfies its symmetric-square equation on the whole unit disk. -/
theorem squaredPeriod_picardFuchs :
    Set.EqOn (fun z : ℂ =>
      (z * (1 - z)) ^ 2 * squaredPeriodThirdJet z +
        3 * z * (1 - z) * (1 - 2 * z) * squaredPeriodCurvature z +
        (1 - 7 * z + 7 * z ^ 2) * squaredPeriodSlope z -
        (1 - 2 * z) / 2 * squaredPeriod z) (fun _ => 0) {z | ‖z‖ₑ < 1} := by
  intro z hz
  dsimp only
  simp only [squaredPeriodThirdJet, squaredPeriodCurvature, squaredPeriodSlope, squaredPeriod]
  linear_combination
    2 * z * (1 - z) * period z * differentiated_picardFuchs z hz +
      (6 * z * (1 - z) * slope z + 2 * (1 - 2 * z) * period z) * picardFuchs z hz

end GaloisForLFunctions.KodairaParshinAbc.Legendre

#print axioms GaloisForLFunctions.KodairaParshinAbc.Legendre.hasDerivAt_squaredPeriod
#print axioms GaloisForLFunctions.KodairaParshinAbc.Legendre.hasDerivAt_squaredPeriodSlope
#print axioms GaloisForLFunctions.KodairaParshinAbc.Legendre.hasDerivAt_squaredPeriodCurvature
#print axioms GaloisForLFunctions.KodairaParshinAbc.Legendre.squaredPeriod_picardFuchs
