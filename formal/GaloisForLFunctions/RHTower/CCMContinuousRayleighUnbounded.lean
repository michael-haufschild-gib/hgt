import GaloisForLFunctions.RHTower.CCMContinuousNegativeSmoothSources

/-!
# No aperture-independent continuous lower bound per unit mass

Negativity of the continuous arithmetic is not an amplitude scaling effect.
Its value divided by physical mass is unbounded below on actual compact
smooth sources as the aperture varies. A finite localization can nevertheless
put every piece inside the already proved uniformly positive local regime.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped InnerProduct SchwartzMap

namespace RHTower

theorem exists_ccmOddPole_continuous_below_mass (R : ℝ) :
    ∃ a : SuzukiPositiveAperture,
      ccmContinuousFormQuadratic a (ccmPolarParityFormVector a (-1)) <
        R * ‖ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))‖ ^ 2 := by
  obtain ⟨A, hA, htail⟩ := exists_ccmOddPoleGammaPolarBalance_negative_tail
  obtain ⟨x, hxA, hxE⟩ := ((eventually_ge_atTop A).and
    (Real.tendsto_exp_atTop.eventually_ge_atTop (8 * (|R| + 1)))).exists
  let a : SuzukiPositiveAperture := ⟨x, hA.trans_le hxA⟩
  have h := htail a hxA
  have hmass : ‖ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))‖ ^ 2 ≤
      2 * Real.exp x := by
    rw [norm_sq_ccmPolarParityFormVector_physical a (Or.inr rfl), Real.sinh_eq]
    change 2 * (2 * ((Real.exp x - Real.exp (-x)) / 2) + 2 * x * (-1)) ≤ 2 * Real.exp x
    linarith [Real.exp_pos (-x), a.2]
  have h₁ := mul_le_mul_of_nonneg_left hmass (abs_nonneg R)
  have h₂ := mul_le_mul_of_nonneg_right (neg_abs_le R)
    (sq_nonneg ‖ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))‖)
  have hE := Real.exp_pos x
  have h₃ := mul_le_mul_of_nonneg_right hxE hE.le
  refine ⟨a, ?_⟩
  rw [ccmContinuousFormQuadratic_oddPole]
  change ccmOddPoleGammaPolarBalance a ≤ -(Real.exp x) ^ 2 / 4 at h
  nlinarith only [h, h₁, h₂, h₃, hE]

/-- A nonzero compact smooth witness beats every proposed uniform mass lower bound. -/
theorem exists_ccmSmoothSource_continuous_below_mass (R : ℝ) :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      0 < ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 ∧
      ccmContinuousArithmeticQuadratic u <
        R * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
  obtain ⟨a, ha⟩ := exists_ccmOddPole_continuous_below_mass R
  let F : CCMArchimedeanFormDomain a → ℝ := fun v =>
    ccmContinuousFormQuadratic a v - R * ‖ccmArchimedeanFormToAperture a v‖ ^ 2
  have hc : Continuous F :=
    (continuous_ccmContinuousFormQuadratic a).sub
      (continuous_const.mul ((ccmArchimedeanFormToAperture a).continuous.norm.pow 2))
  have hi : Iio (0 : ℝ) ∈ nhds (F (ccmPolarParityFormVector a (-1))) :=
    Iio_mem_nhds (sub_neg.mpr ha)
  have he : {v | F v < 0} ∈ nhds (ccmPolarParityFormVector a (-1)) := hc.continuousAt hi
  obtain ⟨u, hu⟩ := (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds he
  change F u.toCCMFormVector < 0 at hu
  have hne : ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0 := by
    intro hz
    have hv : u.toCCMFormVector = 0 :=
      ccmArchimedeanFormToAperture_injective a (by simpa only [map_zero] using hz)
    simp only [F, hv, ccmContinuousFormQuadratic, ccmRestrictedWeilSourceQuadratic_zero,
      map_zero, inner_zero_left, Complex.zero_re, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, sub_zero, lt_self_iff_false] at hu
  refine ⟨a, u, sq_pos_of_pos (norm_pos_iff.mpr hne), ?_⟩
  have h := sub_neg.mp hu
  rwa [ccmContinuousFormQuadratic_ccmSmooth] at h

/-- Fine, individually positive pieces can have a negative compensated continuous invariant.
Every source, compact angle, local gap, and mass identity is constructed in the conclusion. -/
theorem exists_ccmPositivePieces_continuous_below_mass (R : ℝ) :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (angles : List 𝓢(ℝ, ℝ)) (C : ℝ),
      0 < C ∧ 0 < ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 ∧
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (∀ x, ccmLocalizationRemainder u angles x = 0) ∧
      (∀ v ∈ ccmLocalizationPieces u angles,
        C * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector) ∧
      (((ccmLocalizationPieces u angles).map
        (fun v => ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2) ∧
      ccmLocalizationCompensatedEnergy u angles = ccmContinuousArithmeticQuadratic u ∧
      ccmLocalizationCompensatedEnergy u angles <
        R * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
  obtain ⟨a, u, hm, hu⟩ := exists_ccmSmoothSource_continuous_below_mass R
  obtain ⟨d, C, hd, hC, hgap⟩ := exists_ccmSmoothSource_center_independent_gap
  let delta := min d (Real.log 2 / 4)
  have hdelta : 0 < delta := lt_min hd (by positivity)
  obtain ⟨angles, hc, hs, hz⟩ := exists_ccmFiniteLocalization_cover delta hdelta u
  have he := ccmLocalizationCompensatedEnergy_stabilized u angles delta hs hz
    (by dsimp only [delta]; linarith [min_le_right d (Real.log 2 / 4)])
  have hmass := ccmLocalization_mass_conservation u angles
  rw [ccmSmoothSourcePhysicalMass_eq_zero_of_pointwise _ hz, zero_add] at hmass
  refine ⟨a, u, angles, C, hC, hm, hc, hz, ?_, hmass, he, he.trans_lt hu⟩
  intro v hv
  obtain ⟨c, hvc⟩ := hs v hv
  exact hgap a v c (hvc.trans (Metric.ball_subset_ball (min_le_left _ _)))

end RHTower
