import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielScalarCore

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Moving Gabriel interpolation for the concrete dual scalar integral. -/
theorem inghamUniformGabrielCenterMoment_interpolate_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ}
    (hvertical : ∀ z : ℂ, 1 / 2 ≤ z.re →
      Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamUniformGabrielScalarFamily sigma f T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamUniformGabrielRightEdge sigma →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    (inghamUniformGabrielCenterMoment sigma f T) ^
        inghamUniformGabrielReciprocalPower sigma ≤
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) := by
  by_cases hIzero : inghamUniformGabrielCenterMoment sigma f T = 0
  · rw [hIzero, Real.zero_rpow
      (inghamUniformGabrielReciprocalPower_pos hsigma0 hsigma1).ne']
    positivity
  · have hI : 0 < inghamUniformGabrielCenterMoment sigma f T :=
      lt_of_le_of_ne
        (inghamUniformGabrielCenterMoment_nonneg sigma f T) (Ne.symm hIzero)
    apply inghamUniformGabriel_of_scalarFamily hsigma0 hsigma1 hL hR hI hd hB
    · intro z hz
      have hzre : z.re = 1 / 2 := by simpa using hz
      have hhold :=
        norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
          hsigma0 hsigma1 T
          (hvertical z hzre.ge)
          (hvertical (inghamUniformGabrielCenter sigma : ℂ)
            (inghamUniformGabrielCenter_ge_half hsigma0)) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
              (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hm0 (hleftMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg
          (inghamUniformGabrielCenterMoment_nonneg sigma f T) _))
    · intro z hz
      have hzre : z.re = inghamUniformGabrielRightEdge sigma := by simpa using hz
      have hhold :=
        norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
          hsigma0 hsigma1 T
          (hvertical z (by
            rw [hzre]
            exact (inghamUniformGabrielRightEdge_gt_half hsigma1).le))
          (hvertical (inghamUniformGabrielCenter sigma : ℂ)
            (inghamUniformGabrielCenter_ge_half hsigma0)) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hm0 (hrightMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg
          (inghamUniformGabrielCenterMoment_nonneg sigma f T) _))
    · exact norm_inghamUniformGabrielScalarFamily_center hsigma0 hsigma1 f T

/-- Raising the reciprocal-power estimate recovers the exact critical/right shares used by the
uniform Route-T exponent budget. -/
theorem inghamUniformGabrielCenterMoment_le_shares_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ}
    (hvertical : ∀ z : ℂ, 1 / 2 ≤ z.re →
      Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamUniformGabrielScalarFamily sigma f T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamUniformGabrielRightEdge sigma →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    inghamUniformGabrielCenterMoment sigma f T ≤
      L ^ inghamUniformGabrielCriticalShare sigma *
        R ^ inghamUniformGabrielRightShare sigma := by
  have hbase :=
    inghamUniformGabrielCenterMoment_interpolate_of_vertical_continuous
      hsigma0 hsigma1 hvertical T L R hL hR hd hB hleftMoment hrightMoment
  have hp : 0 < inghamUniformGabrielInteriorPower sigma :=
    inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1
  have hI0 := inghamUniformGabrielCenterMoment_nonneg sigma f T
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg hI0 _) hbase hp.le
  rw [← Real.rpow_mul hI0] at hpow
  rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hR.le _)] at hpow
  rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hR.le] at hpow
  have hrecip : inghamUniformGabrielReciprocalPower sigma *
      inghamUniformGabrielInteriorPower sigma = 1 := by
    rw [inghamUniformGabrielReciprocalPower_eq hsigma1]
    exact one_div_mul_cancel hp.ne'
  rw [hrecip, Real.rpow_one,
    show ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        inghamUniformGabrielInteriorPower sigma =
      inghamUniformGabrielCriticalShare sigma by
        rw [mul_comm]
        exact inghamUniformGabriel_left_share_identity hsigma1,
    show ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) *
        inghamUniformGabrielInteriorPower sigma =
      inghamUniformGabrielRightShare sigma by
        rw [mul_comm]
        exact inghamUniformGabriel_right_share_identity hsigma1] at hpow
  exact hpow

private theorem rpow_le_max_one_of_le
    {x C e : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    x ^ e ≤ max 1 C := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 he0).trans (le_max_left _ _)
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    exact (Real.rpow_le_self_of_one_le h1x he1).trans
      (hxC.trans (le_max_right _ _))

private theorem norm_uniformGabrielDual_seed_le_max
    {sigma C : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {w z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma))
    (hw : ‖w‖ ≤ C) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ≤ max 1 C := by
  have hA0 : 0 < (inghamUniformGabrielDualExponent sigma z).re :=
    inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1 hz.1
  have hA1 : (inghamUniformGabrielDualExponent sigma z).re ≤
      2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma := by
    rw [inghamUniformGabrielDualExponent_re]
    rw [div_le_div_iff_of_pos_right (uniformGabrielSeedDenominator_pos hsigma0)]
    linarith [hz.2]
  rw [norm_inghamUniformGabrielDualPower_of_pos_re sigma z _ hA0,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1,
    ← Real.rpow_mul (norm_nonneg w)]
  apply rpow_le_max_one_of_le (norm_nonneg w) hw
  · exact mul_nonneg
      (inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1).le hA0.le
  · have hseed := inghamUniformGabriel_seed_right_identity hsigma0 hsigma1
    have hbound := inghamUniformGabrielInteriorPower_le_two hsigma1
    have hseednonneg :=
      (inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1).le
    have hmul : inghamUniformGabrielSeedExponent sigma *
        (inghamUniformGabrielDualExponent sigma z).re ≤
      inghamUniformGabrielSeedExponent sigma *
        (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) :=
      mul_le_mul_of_nonneg_left hA1 hseednonneg
    nlinarith

/-- A bounded field on the moving closed strip produces a bounded scalar family. -/
theorem bddAbove_inghamUniformGabrielScalarFamily_of_bound
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma), ‖f z‖ ≤ C) :
    BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  refine ⟨∫ _ : ℝ, C * max 1 C ∂mu, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  change ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤ _
  rw [inghamUniformGabrielScalarFamily]
  apply norm_integral_le_of_norm_le (integrable_const _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  have hzshift : z + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have hcenter : (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using
      inghamUniformGabrielCenter_mem_closedStrip hsigma0 hsigma1
  exact mul_le_mul (hf _ hzshift)
    (norm_uniformGabrielDual_seed_le_max hsigma0 hsigma1 (z := z)
      (w := f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
      hz (hf _ hcenter))
    (norm_nonneg _) hC

end

end RHTower.Sieve
