import GaloisForLFunctions.RHTower.Suzuki.SuzukiIntervalEdgeData
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewKernelRegularity

/-!
# The shift-cone obstruction assembled for the critical-ordinate screw primitive

The edge-data interface reduces the normalized edge quotient's convergence to the exhibition of
one structure, and the interval construction supplies such a structure with a compact resolvent
coordinate and named pairing weights, for an arbitrary primitive.  This file instantiates that
primitive at the integral of the critical-ordinate screw function `xiLineScrewSeries`, whose
continuity and vanishing at the origin are unconditional corpus theorems.

The resulting normalized edge jet is an explicit function of the shift, its limit at large negative
shift is the screw Cesàro mean of the aperture, and composing with the small-aperture limit and the
strictly negative Xi curvature threshold yields the dyadic shift-cone obstruction with no
hypothesis: at some positive aperture, every sufficiently negative dyadic shift pair puts the
normalized affine intercept strictly above the Xi curvature threshold — the side forbidden by the
Herglotz sign.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

/-- The primitive of the critical-ordinate screw function. -/
def xiLineScrewPrimitive (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, _root_.RHTower.xiLineScrewSeries t

/-- The primitive differentiates back to the screw function, by continuity of the series. -/
theorem hasDerivAt_xiLineScrewPrimitive (x : ℝ) :
    HasDerivAt xiLineScrewPrimitive (_root_.RHTower.xiLineScrewSeries x) x :=
  (_root_.RHTower.xiLineScrewSeries_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

@[simp] theorem xiLineScrewPrimitive_zero : xiLineScrewPrimitive 0 = 0 :=
  intervalIntegral.integral_same

/-- **Edge data at the critical-ordinate screw primitive.**  The resolvent coordinate is the
compact harmonic multiplier along the polynomial Hilbert basis of `L²[-a,a]`, the pairing vectors
are the `L²` elements of the named edge weights, and the primitive is the integral of
`xiLineScrewSeries`. -/
def suzukiScrewIntervalEdgeData (a : ℝ) (ha : 0 < a) :
    @SuzukiEdgeData (IntervalL2 a) _ _ _ (nontrivial_intervalL2 a ha) :=
  letI := nontrivial_intervalL2 a ha
  { B := intervalHarmonicCoordinate a ha
    selfAdjoint := isSelfAdjoint_intervalHarmonicCoordinate a ha
    injective := injective_intervalHarmonicCoordinate a ha
    specBound := ‖_root_.RHTower.diagonalOperator
      (fun n => ((harmonicMultiplier n : ℝ) : ℂ)) norm_harmonicMultiplier_le‖
    spectrum_subset := spectrum_intervalHarmonicCoordinate_subset a ha
    v := oneIntervalL2 a
    gnum := (-Complex.I) • toIntervalL2 a
      (continuous_edgeNumeratorWeightC hasDerivAt_xiLineScrewPrimitive
        _root_.RHTower.xiLineScrewSeries_continuous a)
    gden := toIntervalL2 a continuous_edgeDenominatorWeight
    aperture := a
    aperture_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
    edgeWeight := ((Real.cosh a : ℝ) : ℂ)
    edgeWeight_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos a))
    primitiveValue := ((xiLineScrewPrimitive (2 * a) : ℝ) : ℂ)
    num_value := inner_edgeNumeratorVector_one a ha hasDerivAt_xiLineScrewPrimitive
      _root_.RHTower.xiLineScrewSeries_continuous xiLineScrewPrimitive_zero
    den_value := inner_edgeDenominatorVector_one a ha }

/-- **The normalized edge jet of the screw edge data**, as a real function of the shift `lam`,
read in the resolvent coordinate at base point `rho`. -/
def suzukiScrewEdgeJet (a : ℝ) (ha : 0 < a) (rho lam : ℝ) : ℝ :=
  letI := nontrivial_intervalL2 a ha
  (-Complex.I *
    (inner ℂ (suzukiScrewIntervalEdgeData a ha).gnum
        ((suzukiScrewIntervalEdgeData a ha).family rho (rho - lam)) /
      inner ℂ (suzukiScrewIntervalEdgeData a ha).gden
        ((suzukiScrewIntervalEdgeData a ha).family rho (rho - lam)))).re

/-- **The edge jet's limit at large negative shift is the screw Cesàro mean of the aperture.**
This is the passage `(2) ⇒ (10)` evaluated on the concrete screw edge data: the normalized
quotient converges to `H(2a)/(2a)` and the real part identifies it with the Cesàro mean. -/
theorem tendsto_suzukiScrewEdgeJet_atBot (a : ℝ) (ha : 0 < a) (rho : ℝ) :
    Tendsto (suzukiScrewEdgeJet a ha rho) atBot
      (𝓝 (_root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * a))) := by
  haveI := nontrivial_intervalL2 a ha
  have hq := (suzukiScrewIntervalEdgeData a ha).tendsto_normalizedQuotient rho
  have hshift : Tendsto (fun lam : ℝ => rho - lam) atBot atTop := by
    have h1 : Tendsto (fun lam : ℝ => -lam) atBot atTop := tendsto_neg_atBot_atTop
    exact (Filter.tendsto_atTop_add_const_left atBot rho h1).congr
      (fun lam => by ring)
  have hcomp := hq.comp hshift
  have hre := (Complex.continuous_re.tendsto _).comp hcomp
  have hval : (((xiLineScrewPrimitive (2 * a) : ℝ) : ℂ) / (2 * (a : ℂ))).re
      = _root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * a) := by
    rw [show (2 : ℂ) * (a : ℂ) = ((2 * a : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, Complex.ofReal_re]
    rfl
  rw [← hval]
  exact hre.congr (fun lam => rfl)

/-- The jet family over all apertures: the concrete edge jet at positive aperture, and the
constant Cesàro mean otherwise. -/
def suzukiScrewShiftJet (rho A : ℝ) : ℝ → ℝ :=
  if hA : 0 < A then suzukiScrewEdgeJet A hA rho
  else fun _ => _root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A)

theorem tendsto_suzukiScrewShiftJet (rho A : ℝ) :
    Tendsto (suzukiScrewShiftJet rho A) atBot
      (𝓝 (_root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A))) := by
  unfold suzukiScrewShiftJet
  split_ifs with hA
  · exact tendsto_suzukiScrewEdgeJet_atBot A hA rho
  · exact tendsto_const_nhds

/-- **The dyadic shift-cone obstruction, with no hypothesis.**  For the normalized edge jet of the
compact-coordinate interval edge data at the critical-ordinate screw primitive, some positive
aperture makes every sufficiently negative dyadic shift pair put the affine intercept strictly
above the Xi curvature threshold — the side forbidden by the central Herglotz sign. -/
theorem suzukiScrewShiftCone_obstruction (rho : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ L in atTop,
      (deriv (deriv _root_.RHTower.XiC) 0 / _root_.RHTower.XiC 0).re
        < _root_.RHTower.suzukiDyadicNegativeShiftIntercept (suzukiScrewShiftJet rho A) L :=
  exists_aperture_eventually_XiC_curvature_lt_intercept_cesaro
    (fun A => tendsto_suzukiScrewShiftJet rho A)

end GaloisForLFunctions.RHTower
