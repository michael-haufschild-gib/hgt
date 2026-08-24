import GaloisForLFunctions.RHTower.ReflectedBiHeatCompletedChannels
import GaloisForLFunctions.RHTower.ReflectedBiHeatFixedRegulatorIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regulator continuity of the reflected Jonquière remainder

After all four principal channels are subtracted, the reflected boundary source has an integrable
majorant uniform down to regulator zero.  This module proves continuity along the positive real
regulator ray, the missing endpoint needed to identify phase and row finite parts.
-/

open Complex Filter Set Topology MeasureTheory Metric
open HurwitzZeta

namespace RHTower

noncomputable section

theorem continuousAt_jonquiereLead_of_openStrip
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    ContinuousAt jonquiereLead s := by
  have hgamma : ContinuousAt (fun u : ℂ => Complex.Gamma (1 - u)) s := by
    apply (Complex.continuousAt_Gamma (1 - s) ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [hs₁, Nat.cast_nonneg (α := ℝ) m]
  rw [show jonquiereLead = fun u : ℂ =>
      Complex.Gamma (1 - u) *
        Complex.exp ((Real.pi : ℂ) * I * (1 - u) / 2) by rfl]
  exact hgamma.mul (by fun_prop)

theorem continuousAt_jonquiereLeadNeg_of_openStrip
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    ContinuousAt jonquiereLeadNeg s := by
  have hgamma : ContinuousAt (fun u : ℂ => Complex.Gamma (1 - u)) s := by
    apply (Complex.continuousAt_Gamma (1 - s) ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [hs₁, Nat.cast_nonneg (α := ℝ) m]
  rw [show jonquiereLeadNeg = fun u : ℂ =>
      Complex.Gamma (1 - u) *
        Complex.exp (-(Real.pi : ℂ) * I * (1 - u) / 2) by rfl]
  exact hgamma.mul (by fun_prop)

/-- At a nonzero phase, the boundary germ is entire in its order. -/
theorem continuousAt_phaseGerm_order {s : ℂ} {theta : ℝ}
    (htheta : theta ∈ Ioc (-Real.pi) Real.pi) (htheta0 : theta ≠ 0) :
    ContinuousAt (fun u : ℂ => phaseGerm u theta) s := by
  have hcircle := phaseCircle_ne_zero htheta htheta0
  have hentire : Differentiable ℂ
      (expZeta ((((theta / (2 * Real.pi) : ℝ)) : UnitAddCircle))) :=
    (differentiable_expZeta_iff _).mpr hcircle
  exact (hentire.continuous.continuousAt :
    ContinuousAt (fun u : ℂ => phaseGerm u theta) s)

/-- At a nonzero phase, the explicit principal germ is continuous in its order throughout the
open unit strip. -/
theorem continuousAt_germPrincipal_order {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) {theta : ℝ} (htheta0 : theta ≠ 0) :
    ContinuousAt (fun u : ℂ => germPrincipal u theta) s := by
  have hleadAt : ContinuousAt (fun u : ℂ => jonquiereLeadAt u theta) s := by
    rw [show (fun u : ℂ => jonquiereLeadAt u theta) =
        if 0 < theta then jonquiereLead else jonquiereLeadNeg by
      split
      · funext u
        simp [jonquiereLeadAt, *]
      · funext u
        simp [jonquiereLeadAt, *]]
    split
    · exact continuousAt_jonquiereLead_of_openStrip hs₀ hs₁
    · exact continuousAt_jonquiereLeadNeg_of_openStrip hs₀ hs₁
  have hbase : (((|theta| : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr htheta0)
  have hpow : ContinuousAt (fun u : ℂ => (((|theta| : ℝ)) : ℂ) ^ (u - 1)) s :=
    (continuousAt_const_cpow hbase).comp (by fun_prop)
  have hzeta : ContinuousAt riemannZeta s :=
    (differentiableAt_riemannZeta (by
      intro hs
      have hre := congrArg Complex.re hs
      norm_num at hre
      linarith)).continuousAt
  rw [show (fun u : ℂ => germPrincipal u theta) = fun u : ℂ =>
      jonquiereLeadAt u theta * (((|theta| : ℝ)) : ℂ) ^ (u - 1) +
        riemannZeta u by rfl]
  exact (hleadAt.mul hpow).add hzeta

/-- The explicit error constant is controlled by the product of the two one-germ profile
constants. -/
theorem polarizedHeatErrorConst_le_two_mul_profile (s w : ℂ) :
    polarizedHeatErrorConst s w ≤
      2 * phaseGermProfileCoeff s * phaseGermProfileCoeff w := by
  let As : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
  let Aw : ℝ := ‖jonquiereLead w‖ + ‖jonquiereLeadNeg w‖ + ‖riemannZeta w‖
  let Js : ℝ := jonquiereConst s
  let Jw : ℝ := jonquiereConst w
  have hAs : 0 ≤ As := by dsimp [As]; positivity
  have hAw : 0 ≤ Aw := by dsimp [Aw]; positivity
  have hJs : 0 ≤ Js := by exact jonquiereConst_nonneg s
  have hJw : 0 ≤ Jw := by exact jonquiereConst_nonneg w
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hPs : phaseGermProfileCoeff s = As + Js * Real.pi := by
    rfl
  have hPw : phaseGermProfileCoeff w = Aw + Jw * Real.pi := by
    rfl
  have hPs0 : 0 ≤ phaseGermProfileCoeff s := phaseGermProfileCoeff_nonneg s
  have hPw0 : 0 ≤ phaseGermProfileCoeff w := phaseGermProfileCoeff_nonneg w
  have hJsPs : Js ≤ phaseGermProfileCoeff s := by
    rw [hPs]
    have := mul_le_mul_of_nonneg_left hpi hJs
    linarith
  have hAsPs : As ≤ phaseGermProfileCoeff s := by
    rw [hPs]
    exact le_add_of_nonneg_right (mul_nonneg hJs Real.pi_pos.le)
  have hJwPw : Jw ≤ phaseGermProfileCoeff w := by
    rw [hPw]
    have := mul_le_mul_of_nonneg_left hpi hJw
    linarith
  rw [polarizedHeatErrorConst]
  change Js * (Aw + Jw * Real.pi) + As * Jw ≤ _
  rw [← hPw]
  calc
    Js * phaseGermProfileCoeff w + As * Jw
        ≤ phaseGermProfileCoeff s * phaseGermProfileCoeff w +
            phaseGermProfileCoeff s * phaseGermProfileCoeff w :=
      add_le_add
        (mul_le_mul_of_nonneg_right hJsPs hPw0)
        (mul_le_mul hAsPs hJwPw hJw hPs0)
    _ = _ := by ring

theorem rpow_real_half_shift_le_two_power
    {a epsilon theta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (htheta0 : theta ≠ 0) :
    |theta| ^ (a + epsilon / 2) ≤
      |theta| ^ a + |theta| ^ (a + 1 / 2) := by
  have hpos : 0 < |theta| := abs_pos.mpr htheta0
  by_cases hunit : |theta| ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hpos hunit (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hpos.le _))
  · have hone : 1 ≤ |theta| := le_of_not_ge hunit
    exact (Real.rpow_le_rpow_of_exponent_le hone (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hpos.le _))

/-- The sharp reflected remainder is continuous as the symmetric regulator decreases to zero. -/
theorem tendsto_reflectedBiHeatSharpRemainder_realRegulator
    (P : ReflectedBiHeatRegulator) :
    Tendsto (fun epsilon : ℝ =>
      polarizedHeatSharpRemainder
        (P.z + (epsilon : ℂ) / 2)
        ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x)
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatSharpRemainder P P.x)) := by
  let w₀ : ℂ := (starRingEnd ℂ) (1 - P.z)
  let R : ℝ := min (P.z.re / 4) ((1 - P.z.re) / 4)
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min (by linarith [P.z_re_pos]) (by linarith [P.z_re_lt_one])
  have hRzLower : R < P.z.re := by
    exact (min_le_left _ _).trans_lt (by linarith [P.z_re_pos])
  have hRzUpper : P.z.re + R < 1 := by
    dsimp [R]
    have hmin := min_le_right (P.z.re / 4) ((1 - P.z.re) / 4)
    linarith [P.z_re_lt_one]
  have hw₀re : w₀.re = 1 - P.z.re := by simp [w₀]
  have hRwLower : R < w₀.re := by
    rw [hw₀re]
    exact (min_le_right _ _).trans_lt (by linarith [P.z_re_lt_one])
  have hRwUpper : w₀.re + R < 1 := by
    rw [hw₀re]
    dsimp [R]
    have hmin := min_le_left (P.z.re / 4) ((1 - P.z.re) / 4)
    linarith [P.z_re_pos]
  obtain ⟨Cs, hCs0, hCs⟩ :=
    exists_phaseGermProfileCoeff_bound_closedBall hR hRzLower hRzUpper
  obtain ⟨Cw, hCw0, hCw⟩ :=
    exists_phaseGermProfileCoeff_bound_closedBall hR hRwLower hRwUpper
  obtain ⟨H, hH⟩ :=
    (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn
      (continuous_heatMultiplier P.x_pos).continuousOn
  have hH0 : 0 ≤ H := by
    exact (norm_nonneg (heatMultiplier P.x 0)).trans
      (hH 0 (by constructor <;> linarith [Real.pi_pos]))
  let K : ℝ := 2 * Cs * Cw
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  let bound : ℝ → ℝ := fun theta =>
    K * ((|theta| ^ P.z.re + |theta| ^ (P.z.re + 1 / 2)) +
      (|theta| ^ (1 - P.z.re) + |theta| ^ (1 - P.z.re + 1 / 2)) + |theta|) * H
  have hboundInt : Integrable bound
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    have hz₀ := integrableOn_abs_rpow_window (show -1 < P.z.re by linarith [P.z_re_pos])
    have hz₁ := integrableOn_abs_rpow_window
      (show -1 < P.z.re + 1 / 2 by linarith [P.z_re_pos])
    have hw₀ := integrableOn_abs_rpow_window
      (show -1 < 1 - P.z.re by linarith [P.z_re_lt_one])
    have hw₁ := integrableOn_abs_rpow_window
      (show -1 < 1 - P.z.re + 1 / 2 by linarith [P.z_re_lt_one])
    have hone := integrableOn_abs_rpow_window (show -1 < (1 : ℝ) by norm_num)
    have hsum := ((hz₀.add hz₁).add (hw₀.add hw₁)).add hone
    convert (hsum.const_mul K).const_mul H using 1
    funext theta
    dsimp [bound]
    simp only [Pi.add_apply, Pi.mul_apply, Real.rpow_one]
    ring
  have hmeas : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun theta : ℝ =>
        ((phaseGerm (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (phaseGerm
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta)) -
          germPrincipal (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (germPrincipal
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta)) *
            heatMultiplier P.x theta)
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (by linarith [P.z_re_lt_one] : (0 : ℝ) < 2 * (1 - P.z.re)),
      Ioo_mem_nhdsGT (by linarith [P.z_re_pos] : (0 : ℝ) < 2 * P.z.re)]
        with epsilon hepsilon hsUpper hwUpper
    have hepsilon0 : 0 < epsilon := hepsilon
    have hs₀ : 0 < (P.z + (epsilon : ℂ) / 2).re := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith
    have hs₁ : (P.z + (epsilon : ℂ) / 2).re < 1 := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith [hsUpper.2]
    have hw₀ : 0 < ((starRingEnd ℂ)
        (1 - P.z + (epsilon : ℂ) / 2)).re := by
      simp only [map_sub, map_one, map_add, map_div₀, map_ofNat, Complex.conj_re]
      norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
      linarith
    have hw₁ : ((starRingEnd ℂ)
        (1 - P.z + (epsilon : ℂ) / 2)).re < 1 := by
      simp only [map_sub, map_one, map_add, map_div₀, map_ofNat, Complex.conj_re]
      norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
      linarith [hwUpper.2]
    exact (integrableOn_polarizedHeatSharpRemainderSource
      hs₀ hs₁ hw₀ hw₁ P.x_pos).aestronglyMeasurable
  have hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᵐ theta : ℝ ∂(volume.restrict (Ioc (-Real.pi) Real.pi)),
        ‖((phaseGerm (P.z + (epsilon : ℂ) / 2) theta *
              (starRingEnd ℂ) (phaseGerm
                ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta) -
            germPrincipal (P.z + (epsilon : ℂ) / 2) theta *
              (starRingEnd ℂ) (germPrincipal
                ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta)) *
              heatMultiplier P.x theta)‖ ≤ bound theta := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
      Ioo_mem_nhdsGT (by linarith [P.z_re_lt_one] : (0 : ℝ) < 2 * (1 - P.z.re)),
      Ioo_mem_nhdsGT (by linarith [P.z_re_pos] : (0 : ℝ) < 2 * P.z.re),
      Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 2 * R)]
        with epsilon hepsilon hepsilonOne hsUpper hwUpper hball
    have hepsilon0 : 0 < epsilon := hepsilon
    have hs₀ : 0 < (P.z + (epsilon : ℂ) / 2).re := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith
    have hs₁ : (P.z + (epsilon : ℂ) / 2).re < 1 := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith [hsUpper.2]
    have hw₀ : 0 < ((starRingEnd ℂ)
        (1 - P.z + (epsilon : ℂ) / 2)).re := by
      simp only [map_sub, map_one, map_add, map_div₀, map_ofNat, Complex.conj_re]
      norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
      linarith
    have hw₁ : ((starRingEnd ℂ)
        (1 - P.z + (epsilon : ℂ) / 2)).re < 1 := by
      simp only [map_sub, map_one, map_add, map_div₀, map_ofNat, Complex.conj_re]
      norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
      linarith [hwUpper.2]
    have hsBall : P.z + (epsilon : ℂ) / 2 ∈ closedBall P.z R := by
      rw [mem_closedBall, dist_eq, add_sub_cancel_left, norm_div, norm_real,
        Real.norm_eq_abs, abs_of_pos hepsilon0, norm_ofNat]
      linarith [hball.2]
    have hwBall : (starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2) ∈
        closedBall w₀ R := by
      rw [mem_closedBall, dist_eq]
      simp only [w₀, map_sub, map_one, map_add, map_div₀, map_ofNat]
      rw [show 1 - (starRingEnd ℂ) P.z + (starRingEnd ℂ) (epsilon : ℂ) / 2 -
          (1 - (starRingEnd ℂ) P.z) =
          (starRingEnd ℂ) ((epsilon : ℂ) / 2) by
            rw [map_div₀, map_ofNat]
            ring,
        RCLike.norm_conj, norm_div, norm_real, Real.norm_eq_abs,
        abs_of_pos hepsilon0, norm_ofNat]
      linarith [hball.2]
    have herror : polarizedHeatErrorConst
        (P.z + (epsilon : ℂ) / 2)
        ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) ≤ K := by
      apply (polarizedHeatErrorConst_le_two_mul_profile _ _).trans
      dsimp [K]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hCs _ hsBall) (by norm_num))
        (hCw _ hwBall)
        (phaseGermProfileCoeff_nonneg _)
        (mul_nonneg (by norm_num) hCs0)
    have hneZero : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ 0 :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hneZero] with theta htheta htheta0
    have hsRpow : |theta| ^ (P.z + (epsilon : ℂ) / 2).re ≤
        |theta| ^ P.z.re + |theta| ^ (P.z.re + 1 / 2) := by
      norm_num [Complex.add_re, Complex.div_re]
      exact rpow_real_half_shift_le_two_power hepsilon0.le hepsilonOne.2.le htheta0
    have hwRpow : |theta| ^ ((starRingEnd ℂ)
          (1 - P.z + (epsilon : ℂ) / 2)).re ≤
        |theta| ^ (1 - P.z.re) + |theta| ^ (1 - P.z.re + 1 / 2) := by
      simp only [map_sub, map_one, map_add, map_div₀, map_ofNat, Complex.conj_re]
      norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
      exact rpow_real_half_shift_le_two_power hepsilon0.le hepsilonOne.2.le htheta0
    have hsource := norm_polarizedGerm_sub_principal_le
      hs₀ hs₁ hw₀ hw₁ theta htheta htheta0
    rw [norm_mul]
    calc
      ‖phaseGerm (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (phaseGerm
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta) -
          germPrincipal (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (germPrincipal
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta)‖ *
          ‖heatMultiplier P.x theta‖
          ≤ (polarizedHeatErrorConst
              (P.z + (epsilon : ℂ) / 2)
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) *
                (|theta| ^ (P.z + (epsilon : ℂ) / 2).re +
                  |theta| ^ ((starRingEnd ℂ)
                    (1 - P.z + (epsilon : ℂ) / 2)).re + |theta|)) * H :=
        mul_le_mul hsource (hH theta ⟨htheta.1.le, htheta.2⟩)
          (norm_nonneg _)
          (mul_nonneg (polarizedHeatErrorConst_nonneg _ _) (by positivity))
      _ ≤ K * ((|theta| ^ P.z.re + |theta| ^ (P.z.re + 1 / 2)) +
            (|theta| ^ (1 - P.z.re) + |theta| ^ (1 - P.z.re + 1 / 2)) +
              |theta|) * H := by
        apply mul_le_mul_of_nonneg_right _ hH0
        apply mul_le_mul herror _ (by positivity) hK0
        linarith
  have hlim : ∀ᵐ theta : ℝ ∂(volume.restrict (Ioc (-Real.pi) Real.pi)),
      Tendsto
        (fun epsilon : ℝ =>
          (phaseGerm (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (phaseGerm
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta) -
          germPrincipal (P.z + (epsilon : ℂ) / 2) theta *
            (starRingEnd ℂ) (germPrincipal
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) theta)) *
            heatMultiplier P.x theta)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((phaseGerm P.z theta *
              (starRingEnd ℂ) (phaseGerm w₀ theta) -
            germPrincipal P.z theta *
              (starRingEnd ℂ) (germPrincipal w₀ theta)) *
                heatMultiplier P.x theta)) := by
    have hneZero : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ 0 :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hneZero] with theta htheta htheta0
    have hsOrder : Tendsto (fun epsilon : ℝ => P.z + (epsilon : ℂ) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 P.z) := by
      have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.add (hepsilon.div_const 2)
    have hwOrder : Tendsto (fun epsilon : ℝ =>
        (starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 w₀) := by
      have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      have hinner : Tendsto (fun epsilon : ℝ =>
          1 - P.z + (epsilon : ℂ) / 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 - P.z)) := by
        simpa using (tendsto_const_nhds.add (hepsilon.div_const 2) :
          Tendsto (fun epsilon : ℝ => (1 - P.z) + (epsilon : ℂ) / 2)
            (𝓝[>] (0 : ℝ)) (𝓝 ((1 - P.z) + 0 / 2)))
      have h := (Complex.continuous_conj.tendsto (1 - P.z)).comp hinner
      change Tendsto ((starRingEnd ℂ) ∘ fun epsilon : ℝ =>
          1 - P.z + (epsilon : ℂ) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((starRingEnd ℂ) (1 - P.z)))
      exact h
    have hw₀pos : 0 < w₀.re := by simp [w₀]; linarith [P.z_re_lt_one]
    have hw₀one : w₀.re < 1 := by simp [w₀]; linarith [P.z_re_pos]
    have hsPhase := (continuousAt_phaseGerm_order htheta htheta0).tendsto.comp hsOrder
    have hwPhase := (continuousAt_phaseGerm_order htheta htheta0).tendsto.comp hwOrder
    have hsPrincipal :=
      (continuousAt_germPrincipal_order P.z_re_pos P.z_re_lt_one htheta0).tendsto.comp
        hsOrder
    have hwPrincipal :=
      (continuousAt_germPrincipal_order hw₀pos hw₀one htheta0).tendsto.comp hwOrder
    exact ((hsPhase.mul ((Complex.continuous_conj.tendsto _).comp hwPhase)).sub
      (hsPrincipal.mul ((Complex.continuous_conj.tendsto _).comp hwPrincipal))).mul_const _
  have hintegral := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundInt hlim
  have hscaled := hintegral.const_mul (1 / (2 * (Real.pi : ℂ)))
  simpa [polarizedHeatSharpRemainder, reflectedBiHeatSharpRemainder, w₀] using hscaled

end

end RHTower
