import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftArithmeticCovariance

/-!
# Shift-averaged positive covariance recovers exact Xi multiplicity

A fixed positive shift can miss a Xi zero when another zero is its exact translated predecessor.
This module removes that obstruction without selecting a divisor-dependent shift.  Multiply the
pre-divisor positive-shift covariance by its displacement and average over any fixed compact
interval of positive displacements.  On the arithmetic side the quotient disappears, leaving an
average of completed pole--Gamma--von-Mangoldt current increments.

After meromorphic continuation, the weighted residue is the current multiplicity minus predecessor
multiplicity.  Every fixed ordinate contains only finitely many Xi zeros, so predecessor
multiplicity is supported on finitely many displacement values and vanishes almost everywhere.
The normalized averaged residue is therefore exactly analytic multiplicity, uniformly through
submicroscopic horizontal collisions.

This closes diagonal extraction and fixed-shift collision loss.  It does not prove the remaining
height-local `4 / 25` upper bound for the averaged arithmetic current.
-/

open Complex Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- Normalized shift-weighted average of the source-first arithmetic covariance. -/
def xiWardCubicShiftWeightedArithmeticAverage
    (z : ℂ) (a b : ℝ) : ℂ :=
  ((((b - a)⁻¹ : ℝ) : ℂ)) *
    ∫ eps : ℝ in a..b,
      (eps : ℂ) * xiWardCubicPositiveRealShiftArithmeticCovariance z eps

/-- Weighting by displacement removes the divided-difference denominator pointwise. -/
theorem ofReal_mul_xiWardCubicPositiveRealShiftArithmeticCovariance
    (z : ℂ) {eps : ℝ} (heps : eps ≠ 0) :
    (eps : ℂ) * xiWardCubicPositiveRealShiftArithmeticCovariance z eps =
      xiWardCubicCompletedArithmeticCurrent (z + (eps : ℂ)) -
        xiWardCubicCompletedArithmeticCurrent z := by
  unfold xiWardCubicPositiveRealShiftArithmeticCovariance
  have hepsC : (eps : ℂ) ≠ 0 := ofReal_ne_zero.mpr heps
  field_simp [hepsC]

/-- Exact pre-divisor normal form: an average of completed arithmetic-current increments. -/
theorem xiWardCubicShiftWeightedArithmeticAverage_eq_incrementAverage
    (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftWeightedArithmeticAverage z a b =
      ((((b - a)⁻¹ : ℝ) : ℂ)) *
        ∫ eps : ℝ in a..b,
          (xiWardCubicCompletedArithmeticCurrent (z + (eps : ℂ)) -
            xiWardCubicCompletedArithmeticCurrent z) := by
  rw [xiWardCubicShiftWeightedArithmeticAverage]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with eps hepsmem
  have hepspos : 0 < eps := by
    rw [uIoc_of_le hab.le] at hepsmem
    exact ha.trans_lt hepsmem.1
  exact ofReal_mul_xiWardCubicPositiveRealShiftArithmeticCovariance
    z hepspos.ne'

/-- Source-only endpoint average.  The right arithmetic endpoint stays fixed while the left
endpoint ranges through positive real predecessors; `W` is any source-defined weight. -/
def xiWardCubicShiftEndpointWeightedArithmeticAverage
    (z : ℂ) (a b : ℝ) (W : ℝ → ℂ) : ℂ :=
  ((((b - a)⁻¹ : ℝ) : ℂ)) *
    ∫ eps : ℝ in a..b,
      (eps : ℂ) *
        xiWardCubicPositiveRealShiftArithmeticCovariance
          (z - (eps : ℂ)) eps * W eps

/-- Exact pole--Gamma--von-Mangoldt normal form of the endpoint average. -/
theorem xiWardCubicShiftEndpointWeightedArithmeticAverage_eq_incrementAverage
    (z : ℂ) {a b : ℝ} (W : ℝ → ℂ) (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftEndpointWeightedArithmeticAverage z a b W =
      ((((b - a)⁻¹ : ℝ) : ℂ)) *
        ∫ eps : ℝ in a..b,
          (xiWardCubicCompletedArithmeticCurrent z -
            xiWardCubicCompletedArithmeticCurrent (z - (eps : ℂ))) * W eps := by
  rw [xiWardCubicShiftEndpointWeightedArithmeticAverage]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with eps hepsmem
  have hepspos : 0 < eps := by
    rw [uIoc_of_le hab.le] at hepsmem
    exact ha.trans_lt hepsmem.1
  rw [ofReal_mul_xiWardCubicPositiveRealShiftArithmeticCovariance
    (z - (eps : ℂ)) hepspos.ne']
  congr 2
  ring_nf

/-- The same endpoint average after source formation and meromorphic continuation. -/
def xiWardCubicShiftEndpointWeightedContinuedAverage
    (z : ℂ) (a b : ℝ) (W : ℝ → ℂ) : ℂ :=
  ((((b - a)⁻¹ : ℝ) : ℂ)) *
    ∫ eps : ℝ in a..b,
      (eps : ℂ) * xiWardCubicPositiveShiftDivisorTransgression z eps * W eps

/-- On a source-safe endpoint interval, arithmetic average and continued average are literally
equal.  Source covariance, displacement weighting, and averaging all precede divisor access. -/
theorem xiWardCubicShiftEndpointWeightedArithmeticAverage_eq_continued
    {z : ℂ} {a b : ℝ} (W : ℝ → ℂ) (ha : 0 ≤ a) (hab : a < b)
    (hz : 1 < (z - (b : ℂ)).re) :
    xiWardCubicShiftEndpointWeightedArithmeticAverage z a b W =
      xiWardCubicShiftEndpointWeightedContinuedAverage z a b W := by
  rw [xiWardCubicShiftEndpointWeightedArithmeticAverage,
    xiWardCubicShiftEndpointWeightedContinuedAverage]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with eps hepsmem
  rw [uIoc_of_le hab.le] at hepsmem
  have hepspos : 0 < eps := ha.trans_lt hepsmem.1
  have hzsafe : 1 < (z - (eps : ℂ)).re := by
    norm_num at hz ⊢
    linarith [hepsmem.2]
  rw [xiWardCubicPositiveShiftDivisorTransgression_eq_arithmeticCovariance
    hzsafe hepspos]

/-- Multiplicity carried by the real translated predecessor of `rho`. -/
def xiWardCubicShiftPredecessorMultiplicity
    (rho : ℂ) (eps : ℝ) : ℂ :=
  (((analyticOrderAt xi (rho - (eps : ℂ))).toNat : ℕ) : ℂ)

/-- Predecessor collisions at one ordinate occur at only finitely many real displacements. -/
theorem finite_support_xiWardCubicShiftPredecessorMultiplicity (rho : ℂ) :
    (Function.support (xiWardCubicShiftPredecessorMultiplicity rho)).Finite := by
  let f : ℝ → ℂ := fun eps => rho - (eps : ℂ)
  let Z : Set ℂ := {z | xi z = 0 ∧ |z.im| ≤ |rho.im|}
  have hZ : Z.Finite := by
    refine (xi_zeros_finite_ball 0 (2 + |rho.im|)).subset ?_
    intro z hz
    refine ⟨?_, hz.1⟩
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im z) ?_
    have hstrip := xi_zero_re_mem_open_unit hz.1
    have hre : |z.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    linarith [hz.2]
  have hf : Function.Injective f := by
    intro x y hxy
    have hre := congrArg Complex.re hxy
    simp only [f, sub_re, ofReal_re] at hre
    linarith
  apply (hZ.preimage hf.injOn).subset
  intro eps heps
  have horder : (analyticOrderAt xi (f eps)).toNat ≠ 0 := by
    simpa only [Function.mem_support, ne_eq,
      xiWardCubicShiftPredecessorMultiplicity, Nat.cast_eq_zero] using heps
  have hxi : xi (f eps) = 0 := by
    by_contra hne
    have hzero : analyticOrderAt xi (f eps) = 0 :=
      (xi_analyticOnNhd_univ (f eps) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    rw [hzero] at horder
    exact horder rfl
  refine ⟨hxi, ?_⟩
  simp only [f, sub_im, ofReal_im, sub_zero, le_refl]

/-- Translated-predecessor multiplicity vanishes for almost every real displacement. -/
theorem xiWardCubicShiftPredecessorMultiplicity_ae_zero (rho : ℂ) :
    xiWardCubicShiftPredecessorMultiplicity rho =ᵐ[volume]
      (fun _ => (0 : ℂ)) := by
  change ∀ᵐ eps ∂volume, xiWardCubicShiftPredecessorMultiplicity rho eps = 0
  rw [MeasureTheory.ae_iff]
  simpa only [Function.support, ne_eq] using
    (finite_support_xiWardCubicShiftPredecessorMultiplicity rho).measure_zero volume

/-- The weighted continued germ is multiplicity minus translated-predecessor multiplicity. -/
theorem ofReal_mul_xiWardCubicPositiveShiftDivisorTransgressionGerm_zero
    (rho : ℂ) {eps : ℝ} (heps : eps ≠ 0) :
    (eps : ℂ) * xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0 =
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) -
        xiWardCubicShiftPredecessorMultiplicity rho eps := by
  rw [xiWardCubicPositiveShiftDivisorTransgressionGerm_zero heps]
  unfold xiWardCubicShiftPredecessorMultiplicity
  have hepsC : (eps : ℂ) ≠ 0 := ofReal_ne_zero.mpr heps
  field_simp [hepsC]

/-- Normalized shift average of the weighted divisor transgression germ. -/
def xiWardCubicShiftAveragedDivisorMultiplicity
    (rho : ℂ) (a b : ℝ) : ℂ :=
  ((((b - a)⁻¹ : ℝ) : ℂ)) *
    ∫ eps : ℝ in a..b,
      (eps : ℂ) *
        xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0

/-- **Averaged positive-shift multiplicity law.**  Every positive displacement interval recovers
the exact Xi multiplicity; fixed-shift predecessor collisions contribute on a null set. -/
theorem xiWardCubicShiftAveragedDivisorMultiplicity_eq
    (rho : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftAveragedDivisorMultiplicity rho a b =
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) := by
  let m : ℂ := (((analyticOrderAt xi rho).toNat : ℕ) : ℂ)
  have hint :
      (∫ eps : ℝ in a..b,
          (eps : ℂ) *
            xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0) =
        ∫ _eps : ℝ in a..b, m := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [xiWardCubicShiftPredecessorMultiplicity_ae_zero rho]
      with eps hpred hepsmem
    have hepspos : 0 < eps := by
      rw [uIoc_of_le hab.le] at hepsmem
      exact ha.trans_lt hepsmem.1
    rw [ofReal_mul_xiWardCubicPositiveShiftDivisorTransgressionGerm_zero
      rho hepspos.ne', hpred, sub_zero]
  rw [xiWardCubicShiftAveragedDivisorMultiplicity, hint,
    intervalIntegral.integral_const]
  change (((b - a)⁻¹ : ℝ) : ℂ) * (((b - a : ℝ) : ℂ) * m) = _
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hcast : (((b - a)⁻¹ : ℝ) : ℂ) = (((b - a : ℝ) : ℂ))⁻¹ := by
    norm_cast
  rw [hcast, ← mul_assoc, inv_mul_cancel₀ (ofReal_ne_zero.mpr hba), one_mul]

/-! ## Holomorphic bichamber weighting after source-first averaging -/

/-- Normalized shifted divisor landing with an arbitrary displacement-dependent complex weight.
The weight is inserted only after the source covariance has been multiplied by its displacement. -/
def xiWardCubicShiftWeightedDivisorLanding
    (rho : ℂ) (a b : ℝ) (W : ℝ → ℂ) : ℂ :=
  ((((b - a)⁻¹ : ℝ) : ℂ)) *
    ∫ eps : ℝ in a..b,
      (eps : ℂ) *
        xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0 * W eps

/-- Null predecessor collisions remain null under every displacement weight.  Thus weighted
positive-shift landing factors exactly as multiplicity times the normalized weight average. -/
theorem xiWardCubicShiftWeightedDivisorLanding_eq
    (rho : ℂ) {a b : ℝ} (W : ℝ → ℂ) (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftWeightedDivisorLanding rho a b W =
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) *
        (((((b - a)⁻¹ : ℝ) : ℂ)) * ∫ eps : ℝ in a..b, W eps) := by
  let m : ℂ := (((analyticOrderAt xi rho).toNat : ℕ) : ℂ)
  have hint :
      (∫ eps : ℝ in a..b,
          (eps : ℂ) *
            xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0 * W eps) =
        ∫ eps : ℝ in a..b, m * W eps := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [xiWardCubicShiftPredecessorMultiplicity_ae_zero rho]
      with eps hpred hepsmem
    have hepspos : 0 < eps := by
      rw [uIoc_of_le hab.le] at hepsmem
      exact ha.trans_lt hepsmem.1
    rw [ofReal_mul_xiWardCubicPositiveShiftDivisorTransgressionGerm_zero
      rho hepspos.ne', hpred, sub_zero]
  rw [xiWardCubicShiftWeightedDivisorLanding, hint,
    intervalIntegral.integral_const_mul]
  dsimp only [m]
  ring

/-- Bichamber weight along a positive horizontal displacement ending at `rho`. -/
def xiWardCubicPositiveShiftBichamberWeight
    (rho : ℂ) (eps r : ℝ) : ℂ :=
  xiWardCubicBichamberFeatureProduct
    (1 - rho + (eps : ℂ)) (star rho) r

/-- At zero displacement the shifted bichamber weight is the exact cubic tensor norm square. -/
theorem xiWardCubicPositiveShiftBichamberWeight_zero (rho : ℂ) (r : ℝ) :
    xiWardCubicPositiveShiftBichamberWeight rho 0 r =
      (Complex.normSq (xiWardCubicTensorConormalFeature (star rho) r) : ℂ) := by
  rw [xiWardCubicPositiveShiftBichamberWeight,
    xiWardCubicBichamberFeatureProduct]
  simpa using xiWardCubicBichamberFeatureProduct_reflectionGraph (star rho) r

/-- Source-first shift average carrying the holomorphic bichamber separator. -/
def xiWardCubicShiftAveragedBichamberLanding
    (rho : ℂ) (a b r : ℝ) : ℂ :=
  xiWardCubicShiftWeightedDivisorLanding rho a b
    (fun eps => xiWardCubicPositiveShiftBichamberWeight rho eps r)

/-- Exact finite-aperture landing: multiplicity times averaged holomorphic bichamber weight. -/
theorem xiWardCubicShiftAveragedBichamberLanding_eq
    (rho : ℂ) {a b : ℝ} (r : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftAveragedBichamberLanding rho a b r =
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) *
        (((((b - a)⁻¹ : ℝ) : ℂ)) *
          ∫ eps : ℝ in a..b,
            xiWardCubicPositiveShiftBichamberWeight rho eps r) := by
  exact xiWardCubicShiftWeightedDivisorLanding_eq rho
    (fun eps => xiWardCubicPositiveShiftBichamberWeight rho eps r) ha hab

/-- Shrinking a source displacement interval recovers the reflection-graph cubic norm square. -/
theorem tendsto_xiWardCubicPositiveShiftBichamberWeight_average_zero
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun h : ℝ => (((h⁻¹ : ℝ) : ℂ)) *
        ∫ eps : ℝ in 0..h,
          xiWardCubicPositiveShiftBichamberWeight rho eps r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.normSq
        (xiWardCubicTensorConormalFeature (star rho) r) : ℂ)) := by
  let W : ℝ → ℂ := fun eps =>
    xiWardCubicPositiveShiftBichamberWeight rho eps r
  have hW : Continuous W := by
    dsimp only [W]
    unfold xiWardCubicPositiveShiftBichamberWeight
      xiWardCubicBichamberFeatureProduct
      xiWardCubicBichamberLeftFeature
      xiWardCubicBichamberRightFeature
    fun_prop
  have hderiv : HasDerivAt (fun h : ℝ => ∫ eps : ℝ in 0..h, W eps) (W 0) 0 := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hW.intervalIntegrable 0 0)
      (hW.stronglyMeasurableAtFilter volume (𝓝 0)) hW.continuousAt
  have hslope := hderiv.tendsto_slope_zero_right
  have hlimit :
      Tendsto
        (fun h : ℝ => ((algebraMap ℝ ℂ) h)⁻¹ * ∫ eps : ℝ in 0..h, W eps)
        (𝓝[>] (0 : ℝ)) (𝓝 (W 0)) := by
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero,
      Algebra.smul_def, map_inv₀] using hslope
  rw [show (Complex.normSq
      (xiWardCubicTensorConormalFeature (star rho) r) : ℂ) = W 0 by
    exact (xiWardCubicPositiveShiftBichamberWeight_zero rho r).symm]
  convert hlimit using 1
  funext h
  norm_cast

/-- **Source-first cubic diagonal landing.**  Shrinking the positive displacement aperture after
source averaging lands on Xi multiplicity times exact cubic tensor norm square.  No divisor was
used to choose the displacement and no fixed-shift collision survives. -/
theorem tendsto_xiWardCubicShiftAveragedBichamberLanding_zero
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun h : ℝ => xiWardCubicShiftAveragedBichamberLanding rho 0 h r)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) *
        (Complex.normSq
          (xiWardCubicTensorConormalFeature (star rho) r) : ℂ))) := by
  have hlimit :=
    (tendsto_xiWardCubicPositiveShiftBichamberWeight_average_zero rho r).const_mul
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ)
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  symm
  simpa using xiWardCubicShiftAveragedBichamberLanding_eq
    rho r (a := 0) (b := h) (le_refl 0) hhpos

end

end RHTower
