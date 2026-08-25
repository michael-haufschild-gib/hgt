import GaloisForLFunctions.HTGeometry.SmallGrowthMeromorphicField
import GaloisForLFunctions.HTGeometry.LogMaxSublinear
import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence

/-!
# Rational coordinate inside Nagoshi's small-growth field

The global coordinate has characteristic `log⁺ r = o(r)`.  Hence the full rational coordinate
field is literally contained in `F_s`, and its upper-end realization is the existing coordinate
carrier.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance upperEndAnalyticSubringDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance smallGrowthCoordinateUpperEndMeroComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- The global entire coordinate. -/
def smallGrowthCoordinateEntire : entireSubring ℂ :=
  ⟨fun z => z, analyticOnNhd_id⟩

/-- The global meromorphic coordinate. -/
def smallGrowthCoordinateField : EntireField ℂ :=
  algebraMap (entireSubring ℂ) (EntireField ℂ) smallGrowthCoordinateEntire

/-- The coordinate characteristic is sublinear. -/
theorem characteristic_id_isLittleO :
    characteristic (fun z : ℂ => z) ⊤ =o[atTop] id := by
  let v : ℝ → ℝ := fun r => Real.posLog |r|
  have hv : v =o[atTop] id := by
    apply Real.isLittleO_log_id_atTop.congr'
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      simp only [v, abs_of_nonneg (zero_le_one.trans hr), Real.posLog]
      rw [max_eq_right (Real.log_nonneg hr)]
    · exact EventuallyEq.rfl
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_nonneg hr
  · filter_upwards with r
    exact GaloisForLFunctions.Nevanlinna.characteristic_top_le_posLog_of_bound
      analyticOnNhd_id fun z hz => by
        have hz' : ‖z‖ = |r| := by simpa [Metric.mem_sphere] using hz
        exact hz'.le

/-- The global coordinate belongs to Nagoshi's coefficient field. -/
theorem hasSmallGrowth_coordinateField : HasSmallGrowth smallGrowthCoordinateField := by
  let p : EntireFractionPresentation smallGrowthCoordinateField :=
    { numerator := smallGrowthCoordinateEntire
      denominator := 1
      denominator_ne_zero := one_ne_zero
      eq_div := by simp [smallGrowthCoordinateField] }
  refine ⟨p, ?_⟩
  have hfun : p.function = fun z : ℂ => z := by
    funext z
    simp [p, EntireFractionPresentation.function, smallGrowthCoordinateEntire]
  rw [hfun]
  exact characteristic_id_isLittleO

/-- The coordinate as an element of `F_s`. -/
def smallGrowthCoordinate : SmallGrowthMeromorphicField :=
  ⟨smallGrowthCoordinateField, hasSmallGrowth_coordinateField⟩

/-- The global coordinate realizes as the genuine upper-end coordinate. -/
@[simp]
theorem smallGrowthCoordinate_algebraMap :
    algebraMap SmallGrowthMeromorphicField upperEndMeroField smallGrowthCoordinate =
      upperEndCoordinateMero := by
  rw [show algebraMap SmallGrowthMeromorphicField upperEndMeroField =
      smallGrowthMeromorphicToUpperEnd by rfl]
  change entireFieldToUpperEndMero smallGrowthCoordinateField = upperEndCoordinateMero
  rw [smallGrowthCoordinateField, entireFieldToUpperEndMero_algebraMap,
    upperEndCoordinateMero_eq_algebraMap]
  congr 1
  apply Subtype.ext
  rw [upperEndCoordinateAnalytic_coe]
  rfl

/-- The faithful `ℂ`-algebra realization of `F_s` at the upper end. -/
def smallGrowthToUpperEndAlgHom :
    SmallGrowthMeromorphicField →ₐ[ℂ] upperEndMeroField :=
  { smallGrowthMeromorphicToUpperEnd with
    commutes' := fun z => by
      change entireFieldToUpperEndMero (constEntire ℂ z) =
        algebraMap ℂ upperEndMeroField z
      rw [constEntire, RingHom.comp_apply, entireFieldToUpperEndMero_algebraMap]
      change algebraMap upperEndAnalyticSubring upperEndMeroField
          (entireToUpperEndAnalytic (constEntireRing ℂ z)) =
        upperEndPolyToMero (Polynomial.C z)
      change algebraMap upperEndAnalyticSubring upperEndMeroField
          (entireToUpperEndAnalytic (constEntireRing ℂ z)) =
        algebraMap upperEndAnalyticSubring upperEndMeroField
          (upperEndPolyToAnalytic (Polynomial.C z))
      congr 1
      apply Subtype.ext
      change ((fun _ : ℂ => z) : Germ upperEndFilter ℂ) =
        ((fun w : ℂ => (Polynomial.C z).eval w) : Germ upperEndFilter ℂ)
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun w => by simp }

/-- Every rational-coordinate carrier is realized by an element of `F_s`. -/
theorem upperEndRationalCoordinateField_le_smallGrowth_fieldRange :
    upperEndRationalCoordinateField ≤ smallGrowthToUpperEndAlgHom.fieldRange := by
  rw [IntermediateField.adjoin_le_iff]
  rintro z (rfl : z = upperEndCoordinateMero)
  exact ⟨smallGrowthCoordinate, smallGrowthCoordinate_algebraMap⟩

/-- Existential form used to pull concrete rational correction jets back to `F_s`. -/
theorem exists_smallGrowth_preimage_of_mem_upperEndRationalCoordinateField
    {z : upperEndMeroField} (hz : z ∈ upperEndRationalCoordinateField) :
    ∃ c : SmallGrowthMeromorphicField,
      algebraMap SmallGrowthMeromorphicField upperEndMeroField c = z := by
  exact upperEndRationalCoordinateField_le_smallGrowth_fieldRange hz

end

end GaloisForLFunctions.HTGeometry
