import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielScalarFamily

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Fixed Gabriel interpolation for the concrete dual scalar integral. The only remaining inputs are
strip regularity/boundedness and uniform translated endpoint moments. -/
theorem inghamFixedGabrielCenterMoment_interpolate_of_vertical_continuous
    {f : ℂ → ℂ}
    (hvertical : ∀ z : ℂ, 1 / 2 ≤ z.re →
      Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamFixedGabrielScalarFamily f T)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) inghamPowerSavingRightEdge))
    (hB : BddAbove ((norm ∘ inghamFixedGabrielScalarFamily f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) inghamPowerSavingRightEdge))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamPowerSavingRightEdge →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    (inghamFixedGabrielCenterMoment f T) ^ (11859 / 18200 : ℝ) ≤
      L ^ (8277 / 18200 : ℝ) * R ^ (3582 / 18200 : ℝ) := by
  by_cases hIzero : inghamFixedGabrielCenterMoment f T = 0
  · rw [hIzero, Real.zero_rpow (by norm_num : (11859 / 18200 : ℝ) ≠ 0)]
    positivity
  · have hI : 0 < inghamFixedGabrielCenterMoment f T :=
      lt_of_le_of_ne (inghamFixedGabrielCenterMoment_nonneg f T) (Ne.symm hIzero)
    apply inghamFixedGabriel_of_scalarFamily hL hR hI hd hB
    · intro z hz
      have hzre : z.re = 1 / 2 := by simpa using hz
      have hhold :=
        norm_inghamFixedGabrielScalarFamily_left_le_of_vertical_continuous T
          (hvertical z hzre.ge)
          (hvertical (inghamFixedGabrielSigma : ℂ) (by
            norm_num [inghamFixedGabrielSigma])) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
              (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hm0 (hleftMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (inghamFixedGabrielCenterMoment_nonneg f T) _))
    · intro z hz
      have hzre : z.re = inghamPowerSavingRightEdge := by simpa using hz
      have hhold :=
        norm_inghamFixedGabrielScalarFamily_right_le_of_vertical_continuous T
          (hvertical z (by
            rw [hzre]
            norm_num [inghamPowerSavingRightEdge]))
          (hvertical (inghamFixedGabrielSigma : ℂ) (by
            norm_num [inghamFixedGabrielSigma])) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hm0 (hrightMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (inghamFixedGabrielCenterMoment_nonneg f T) _))
    · exact norm_inghamFixedGabrielScalarFamily_center f T

/-- Global continuity is a convenient sufficient condition for the sharper vertical-path
interpolation theorem. -/
theorem inghamFixedGabrielCenterMoment_interpolate
    {f : ℂ → ℂ} (hf : Continuous f) (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamFixedGabrielScalarFamily f T)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) inghamPowerSavingRightEdge))
    (hB : BddAbove ((norm ∘ inghamFixedGabrielScalarFamily f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) inghamPowerSavingRightEdge))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamPowerSavingRightEdge →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    (inghamFixedGabrielCenterMoment f T) ^ (11859 / 18200 : ℝ) ≤
      L ^ (8277 / 18200 : ℝ) * R ^ (3582 / 18200 : ℝ) := by
  apply inghamFixedGabrielCenterMoment_interpolate_of_vertical_continuous
    (fun z _ => hf.comp (by fun_prop)) T L R hL hR hd hB hleftMoment hrightMoment

private theorem rpow_le_max_one_of_le
    {x C e : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    x ^ e ≤ max 1 C := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 he0).trans (le_max_left _ _)
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    exact (Real.rpow_le_self_of_one_le h1x he1).trans (hxC.trans (le_max_right _ _))

private theorem norm_fixedGabrielDual_seed_le_max
    {C : ℝ} {w z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge)
    (hw : ‖w‖ ≤ C) :
    ‖inghamFixedGabrielDualPower (inghamFixedGabrielDualSeed w) z‖ ≤ max 1 C := by
  have hA0 : 0 < (inghamFixedGabrielDualExponent z).re := by
    rw [inghamFixedGabrielDualExponent_re]
    have := hz.1
    norm_num at this ⊢
    nlinarith
  have hA1 : (inghamFixedGabrielDualExponent z).re ≤ 9100 / 6341 := by
    rw [inghamFixedGabrielDualExponent_re]
    have := hz.2
    norm_num [inghamPowerSavingRightEdge] at this ⊢
    nlinarith
  rw [norm_inghamFixedGabrielDualPower_of_pos_re z _ hA0,
    norm_inghamFixedGabrielDualSeed, ← Real.rpow_mul (norm_nonneg w)]
  apply rpow_le_max_one_of_le (norm_nonneg w) hw
  · positivity
  · have : (inghamFixedGabrielDualExponent z).re ≤ 9100 / 6341 := hA1
    nlinarith [hA0]

/-- A bounded field on the closed Gabriel strip produces a bounded concrete scalar family. -/
theorem bddAbove_inghamFixedGabrielScalarFamily_of_bound
    {f : ℂ → ℂ} (T C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge, ‖f z‖ ≤ C) :
    BddAbove ((norm ∘ inghamFixedGabrielScalarFamily f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  refine ⟨∫ _ : ℝ, C * max 1 C ∂mu, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  change ‖inghamFixedGabrielScalarFamily f T z‖ ≤ _
  rw [inghamFixedGabrielScalarFamily]
  apply norm_integral_le_of_norm_le (integrable_const _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  have hzshift : z + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have hcenter : (inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge := by
    constructor <;> norm_num [inghamFixedGabrielSigma, inghamPowerSavingRightEdge]
  exact mul_le_mul (hf _ hzshift)
    (norm_fixedGabrielDual_seed_le_max (z := z)
      (w := f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)) hz (hf _ hcenter))
    (norm_nonneg _) hC


end

end RHTower.Sieve
