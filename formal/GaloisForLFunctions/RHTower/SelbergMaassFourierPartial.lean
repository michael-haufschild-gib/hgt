import GaloisForLFunctions.RHTower.SelbergMaassCharacterGradient
import GaloisForLFunctions.HTGeometry.UnitIntervalFourierProjection

/-!
# Unit-interval partial Fourier transport for Maass source slices

Rescaling the literal congruence period to the unit interval identifies the unit Fourier
coefficient with the existing normalized Maass coefficient exactly.  The same identity applies
to every continuous source readout and its two real chart derivatives.  Thus the unit-interval
mean-square partial-Fourier theorem applies directly to the physical source, horizontal, and
height fields; no pointwise Fourier-series convergence or unproved regularity upgrade is used.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassFourierPartial
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
open SelbergMaassUnipotentFourier SelbergMaassCharacterGradient SelbergMaassFourier SelbergMaassMean
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- A horizontal slice, rescaled from a positive period to the unit interval. -/
def unitRescaledSlice (w : ℝ) (F : ℂ → ℂ) (y : ℝ) (t : ℝ) : ℂ :=
  F (SelbergMaassMean.point (t * w) y)

/-- The unit-interval coefficient of a rescaled slice is the literal normalized Maass
coefficient on its original period. -/
theorem l2Pair_fourierChar_unitRescaled_eq_coefficient
    (w : ℝ) (hw : 0 < w) (n : ℤ) (F : ℂ → ℂ) (y : ℝ) :
    l2Pair (fourierChar n) (unitRescaledSlice w F y) =
      coefficient w n F y := by
  have hkernel (t : ℝ) :
      (starRingEnd ℂ) (fourierChar n t) = RHTower.deningerFourierKernel w n (t * w) := by
    rw [fourierChar_conj]
    unfold fourierChar RHTower.deningerFourierKernel
    congr 1
    push_cast
    have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    field_simp [hwc]
  have hsub := intervalIntegral.integral_comp_mul_right
    (a := 0) (b := 1)
    (fun x : ℝ => RHTower.deningerFourierKernel w n x *
      F (SelbergMaassMean.point x y)) hw.ne'
  unfold l2Pair coefficient RHTower.deningerFourierCoeff unitRescaledSlice
  rw [intervalIntegral.integral_congr (fun t _ => by rw [hkernel])]
  rw [hsub]
  simp only [zero_mul, one_mul]
  rw [Complex.real_smul]
  congr 1
  exact_mod_cast inv_eq_one_div w

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The rescaled unit-interval source observation. -/
def unitRescaledSourceReadout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (y : ℝ) : ℝ → ℂ :=
  unitRescaledSlice (N + 1 : ℕ)
    (fun z => L (sourceVector N f (ofComplex z))) y

/-- The rescaled source observation is continuous on the unit interval. -/
theorem continuous_unitRescaledSourceReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Continuous (unitRescaledSourceReadout N f L y) := by
  unfold unitRescaledSourceReadout unitRescaledSlice
  exact (slice_continuous (readout_contDiffOn N f L).continuousOn hy).comp
    (continuous_id.mul continuous_const)

/-- The unit-interval source partial sums converge in mean square. -/
theorem tendsto_l2NormSq_sub_fourierPartialSum_unitRescaledSourceReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun M : ℕ => l2NormSq (fun t =>
      unitRescaledSourceReadout N f L y t -
        fourierPartialSum (unitRescaledSourceReadout N f L y) M t)) atTop (𝓝 0) :=
  tendsto_l2NormSq_sub_fourierPartialSum
    (continuous_unitRescaledSourceReadout N f L hy)

/-- The unit coefficient of a source observation is its existing literal coefficient readout. -/
theorem l2Pair_fourierChar_unitRescaledSourceReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    l2Pair (fourierChar n) (unitRescaledSourceReadout N f L y) =
      L (coefficientVector N f n y) := by
  rw [unitRescaledSourceReadout,
    l2Pair_fourierChar_unitRescaled_eq_coefficient (N + 1 : ℕ) (by positivity)]
  exact coefficient_readout N f L n hy

/-- The rescaled unit-interval horizontal derivative observation. -/
def unitRescaledHorizontalReadout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (y : ℝ) : ℝ → ℂ :=
  unitRescaledSlice (N + 1 : ℕ)
    (directional 1 (fun z => L (sourceVector N f (ofComplex z)))) y

/-- The rescaled horizontal derivative observation is continuous on the unit interval. -/
theorem continuous_unitRescaledHorizontalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Continuous (unitRescaledHorizontalReadout N f L y) := by
  unfold unitRescaledHorizontalReadout unitRescaledSlice
  have hd := directional_contDiffOn (readout_contDiffOn N f L)
    (m := 1) le_rfl (1 : ℂ)
  exact (slice_continuous hd.continuousOn hy).comp
    (continuous_id.mul continuous_const)

/-- The unit-interval horizontal derivative partial sums converge in mean square. -/
theorem tendsto_l2NormSq_sub_fourierPartialSum_unitRescaledHorizontalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun M : ℕ => l2NormSq (fun t =>
      unitRescaledHorizontalReadout N f L y t -
        fourierPartialSum (unitRescaledHorizontalReadout N f L y) M t)) atTop (𝓝 0) :=
  tendsto_l2NormSq_sub_fourierPartialSum
    (continuous_unitRescaledHorizontalReadout N f L hy)

/-- The horizontal derivative coefficient is its physical signed frequency times the source
coefficient. -/
theorem l2Pair_fourierChar_unitRescaledHorizontalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    l2Pair (fourierChar n) (unitRescaledHorizontalReadout N f L y) =
      ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I *
        L (coefficientVector N f n y) := by
  rw [unitRescaledHorizontalReadout,
    l2Pair_fourierChar_unitRescaled_eq_coefficient (N + 1 : ℕ) (by positivity)]
  rw [SelbergMaassParseval.coefficient_horizontal (N + 1 : ℕ) (by positivity) n
    ((readout_contDiffOn N f L).of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy
    (fun x => readout_periodic N f L x hy), coefficient_readout N f L n hy]

/-- The rescaled unit-interval height derivative observation. -/
def unitRescaledVerticalReadout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (y : ℝ) : ℝ → ℂ :=
  unitRescaledSlice (N + 1 : ℕ)
    (directional Complex.I (fun z => L (sourceVector N f (ofComplex z)))) y

/-- The rescaled height derivative observation is continuous on the unit interval. -/
theorem continuous_unitRescaledVerticalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Continuous (unitRescaledVerticalReadout N f L y) := by
  unfold unitRescaledVerticalReadout unitRescaledSlice
  have hd := directional_contDiffOn (readout_contDiffOn N f L)
    (m := 1) le_rfl Complex.I
  exact (slice_continuous hd.continuousOn hy).comp
    (continuous_id.mul continuous_const)

/-- The unit-interval height derivative partial sums converge in mean square. -/
theorem tendsto_l2NormSq_sub_fourierPartialSum_unitRescaledVerticalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun M : ℕ => l2NormSq (fun t =>
      unitRescaledVerticalReadout N f L y t -
        fourierPartialSum (unitRescaledVerticalReadout N f L y) M t)) atTop (𝓝 0) :=
  tendsto_l2NormSq_sub_fourierPartialSum
    (continuous_unitRescaledVerticalReadout N f L hy)

/-- The vertical derivative coefficient is the existing source height coefficient readout. -/
theorem l2Pair_fourierChar_unitRescaledVerticalReadout
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    l2Pair (fourierChar n) (unitRescaledVerticalReadout N f L y) =
      L (coefficientHeightVector N f n y) := by
  rw [unitRescaledVerticalReadout,
    l2Pair_fourierChar_unitRescaled_eq_coefficient (N + 1 : ℕ) (by positivity)]
  exact coefficient_readout_vertical N f L n hy

end
end GaloisForLFunctions.RHTower.SelbergMaassFourierPartial
