import GaloisForLFunctions.RHTower.EisensteinRowSumMajorant
import GaloisForLFunctions.RHTower.EisensteinFundamentalDomainIntegrability
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-!
# Unfolding the truncated row sum against the line model

For `Re u > Re v > 1/2`, `Im v > 0`, `Y ≥ 1` and `s = ½ + u`, the unfolded integrand
`φ(ζ) = [Im ζ ≤ Y] (Im ζ)^s E_v(ζ)` is `T`-periodic and integrable on the translation strip: on the
fundamental domain `Σ_w ‖φ(γ_w z)‖ = R_{Re s}(z) ‖E_v(z)‖` is dominated by a constant plus
`y^{1 − Re u + Re v}` (exponent `< 1`).  The corpus unfolding theorem then gives

`∫_𝒟 (Σ_w [Im γ_w z ≤ Y] Im(γ_w z)^s) E_v(z) dμ = 2 ∫_{strip, Im ≤ Y} y^s E_v dμ`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open scoped MatrixGroups Pointwise

namespace RHTower

noncomputable section

/-- The slab weight `[Im ζ ≤ Y] (Im ζ)^s`. -/
def slabWeight (s : ℂ) (Y : ℝ) (ζ : ℍ) : ℂ := if ζ.im ≤ Y then (ζ.im : ℂ) ^ s else 0

/-- The unfolded integrand `φ(ζ) = [Im ζ ≤ Y] (Im ζ)^s E_v(ζ)`. -/
def unfoldedIntegrand (s : ℂ) (Y : ℝ) (v : ℂ) (ζ : ℍ) : ℂ :=
  slabWeight s Y ζ * eisensteinLineModel v ζ

theorem slabWeight_T (s : ℂ) (Y : ℝ) (n : ℤ) (ζ : ℍ) :
    slabWeight s Y (ModularGroup.T ^ n • ζ) = slabWeight s Y ζ := by
  unfold slabWeight
  rw [ModularGroup.im_T_zpow_smul]

theorem unfoldedIntegrand_T (s : ℂ) (Y : ℝ) {v : ℂ} (hv : v ∈ eisensteinLineDomain) (n : ℤ)
    (ζ : ℍ) : unfoldedIntegrand s Y v (ModularGroup.T ^ n • ζ) = unfoldedIntegrand s Y v ζ := by
  unfold unfoldedIntegrand
  rw [slabWeight_T, eisensteinLineModel_smul hv]

theorem unfoldedIntegrand_row (s : ℂ) (Y : ℝ) {v : ℂ} (hv : v ∈ eisensteinLineDomain)
    (w : gammaSet 1 1 0) (z : ℍ) :
    unfoldedIntegrand s Y v (gammaSetMatrix w • z) =
      (if rowHeight w z ≤ Y then (rowHeight w z : ℂ) ^ s else 0) * eisensteinLineModel v z := by
  unfold unfoldedIntegrand slabWeight rowHeight
  rw [eisensteinLineModel_smul hv]

theorem norm_unfoldedIntegrand_row (s : ℂ) (Y : ℝ) {v : ℂ} (hv : v ∈ eisensteinLineDomain)
    (w : gammaSet 1 1 0) (z : ℍ) :
    ‖unfoldedIntegrand s Y v (gammaSetMatrix w • z)‖ =
      (if rowHeight w z ≤ Y then rowHeight w z ^ s.re else 0) * ‖eisensteinLineModel v z‖ := by
  rw [unfoldedIntegrand_row s Y hv, norm_mul]
  congr 1
  split_ifs
  · exact Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos w z) s
  · simp

/-! ## Measurability -/

theorem measurable_slabWeight (s : ℂ) (Y : ℝ) : Measurable (slabWeight s Y) := by
  unfold slabWeight
  refine Measurable.ite (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)
    ?_ measurable_const
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable.pow_const s

theorem measurable_unfoldedIntegrand (s : ℂ) (Y : ℝ) (v : ℂ) :
    Measurable (unfoldedIntegrand s Y v) :=
  (measurable_slabWeight s Y).mul (continuous_eisensteinLineModel v).measurable

theorem measurable_unfoldedIntegrand_row (s : ℂ) (Y : ℝ) (v : ℂ) (w : gammaSet 1 1 0) :
    Measurable (fun z : ℍ => unfoldedIntegrand s Y v (gammaSetMatrix w • z)) :=
  (measurable_unfoldedIntegrand s Y v).comp (measurable_const_smul (gammaSetMatrix w))

/-! ## The majorant on the fundamental domain -/

/-- The polynomial bound of the line model on `y ≥ 1/2`. -/
def lineBoundConst (v : ℂ) : ℝ :=
  ‖msB v‖ * (1 / 2 : ℝ) ^ (1 / 2 - v.re) + ‖msA v‖ + tailConst v

theorem lineBoundConst_nonneg (v : ℂ) : 0 ≤ lineBoundConst v := by
  unfold lineBoundConst
  have h1 := tailConst_nonneg v
  have h2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - v.re) := Real.rpow_nonneg (by norm_num) _
  have h3 := norm_nonneg (msB v)
  have h4 := norm_nonneg (msA v)
  nlinarith [mul_nonneg h3 h2]

theorem norm_eisensteinLineModel_le' {v : ℂ} (hv : 1 / 2 ≤ v.re) {z : ℍ} (hz : 1 / 2 ≤ z.im) :
    ‖eisensteinLineModel v z‖ ≤ lineBoundConst v * (1 + z.im ^ (1 / 2 + v.re)) := by
  refine (norm_eisensteinLineModel_le v hz).trans ?_
  unfold lineBoundConst
  have hy : 0 < z.im := z.im_pos
  have h1 : z.im ^ (1 / 2 - v.re) ≤ (1 / 2 : ℝ) ^ (1 / 2 - v.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by linarith)
  have h2 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hp : 0 ≤ z.im ^ (1 / 2 + v.re) := Real.rpow_nonneg hy.le _
  have hB := norm_nonneg (msB v)
  have hA := norm_nonneg (msA v)
  have hT := tailConst_nonneg v
  have hh : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - v.re) := Real.rpow_nonneg (by norm_num) _
  nlinarith [mul_le_mul_of_nonneg_left h1 hB, mul_le_mul_of_nonneg_left h2 hT,
    mul_nonneg (mul_nonneg hB hh) hp, mul_nonneg hA hp, mul_nonneg hT hp]

/-- The majorant `Cb + Cd · y^{1 − Re u + Re v}`. -/
def unfoldedMajorant (u v : ℂ) (Y : ℝ) (z : ℍ) : ℝ :=
  (2 * rowBoundedConst u.re Y / ‖msA (u.re : ℂ)‖) * lineBoundConst v * (1 + Y ^ (1 / 2 + v.re)) +
    2 * rowDecayConst u.re * lineBoundConst v * z.im ^ (1 - u.re + v.re)

theorem tsum_norm_unfoldedIntegrand_row (s : ℂ) (Y : ℝ) {v : ℂ} (hv : v ∈ eisensteinLineDomain)
    (z : ℍ) :
    (∑' w : gammaSet 1 1 0, ‖unfoldedIntegrand s Y v (gammaSetMatrix w • z)‖) =
      realTruncatedRowSum s.re Y z * ‖eisensteinLineModel v z‖ := by
  simp_rw [norm_unfoldedIntegrand_row s Y hv]
  rw [tsum_mul_right]
  rfl

theorem summable_norm_unfoldedIntegrand_row {s : ℂ} (hs : 1 < s.re) (Y : ℝ) {v : ℂ}
    (hv : v ∈ eisensteinLineDomain) (z : ℍ) :
    Summable (fun w : gammaSet 1 1 0 => ‖unfoldedIntegrand s Y v (gammaSetMatrix w • z)‖) := by
  simp_rw [norm_unfoldedIntegrand_row s Y hv]
  exact (summable_realTruncated_term hs Y z).mul_right _

/-- **The unfolded norms are dominated on `𝒟`.** -/
theorem tsum_norm_unfoldedIntegrand_le {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    (∑' w : gammaSet 1 1 0, ‖unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z)‖) ≤
      unfoldedMajorant u v Y z := by
  rw [tsum_norm_unfoldedIntegrand_row _ Y hv, re_half_add]
  have hyhalf : 1 / 2 ≤ z.im := (half_lt_im_of_mem_fd' hz).le
  have hE := norm_eisensteinLineModel_le' hv1.le hyhalf
  have hL := lineBoundConst_nonneg v
  have hEnn := norm_nonneg (eisensteinLineModel v z)
  have hRnn := realTruncatedRowSum_nonneg (1 / 2 + u.re) Y z
  have hA : 0 < ‖msA (u.re : ℂ)‖ := norm_pos_iff.mpr (msA_ofReal_ne_zero hu)
  have hCb : 0 ≤ 2 * rowBoundedConst u.re Y / ‖msA (u.re : ℂ)‖ := by
    have := rowBoundedConst_nonneg u.re (by linarith : (0 : ℝ) ≤ Y)
    positivity
  have hCd : 0 ≤ 2 * rowDecayConst u.re := by have := rowDecayConst_nonneg u.re; positivity
  have hpow : 0 ≤ z.im ^ (1 - u.re + v.re) := Real.rpow_nonneg z.im_pos.le _
  have hYp : 0 ≤ Y ^ (1 / 2 + v.re) := Real.rpow_nonneg (by linarith) _
  unfold unfoldedMajorant
  rcases le_or_gt z.im Y with hzY | hzY
  · have hR := realTruncatedRowSum_le_of_le hu hY hz hzY
    have hyY : z.im ^ (1 / 2 + v.re) ≤ Y ^ (1 / 2 + v.re) :=
      Real.rpow_le_rpow z.im_pos.le hzY (by linarith)
    have h1 : realTruncatedRowSum (1 / 2 + u.re) Y z * ‖eisensteinLineModel v z‖ ≤
        (2 * rowBoundedConst u.re Y / ‖msA (u.re : ℂ)‖) *
          (lineBoundConst v * (1 + Y ^ (1 / 2 + v.re))) := by
      apply mul_le_mul hR _ hEnn hCb
      refine hE.trans ?_
      apply mul_le_mul_of_nonneg_left _ hL
      linarith
    nlinarith [mul_nonneg (mul_nonneg hCd hL) hpow]
  · have hR := realTruncatedRowSum_le_of_gt hu hY hz hzY
    have hy1 : 1 ≤ z.im := by linarith
    have hone : (1 : ℝ) ≤ z.im ^ (1 / 2 + v.re) := Real.one_le_rpow hy1 (by linarith)
    have hE2 : ‖eisensteinLineModel v z‖ ≤ 2 * lineBoundConst v * z.im ^ (1 / 2 + v.re) := by
      refine hE.trans ?_
      have : (1 : ℝ) + z.im ^ (1 / 2 + v.re) ≤ 2 * z.im ^ (1 / 2 + v.re) := by linarith
      calc lineBoundConst v * (1 + z.im ^ (1 / 2 + v.re))
          ≤ lineBoundConst v * (2 * z.im ^ (1 / 2 + v.re)) := mul_le_mul_of_nonneg_left this hL
        _ = 2 * lineBoundConst v * z.im ^ (1 / 2 + v.re) := by ring
    have hprod : realTruncatedRowSum (1 / 2 + u.re) Y z * ‖eisensteinLineModel v z‖ ≤
        (rowDecayConst u.re * z.im ^ (1 / 2 - u.re)) *
          (2 * lineBoundConst v * z.im ^ (1 / 2 + v.re)) :=
      mul_le_mul hR hE2 hEnn (mul_nonneg (rowDecayConst_nonneg _) (Real.rpow_nonneg z.im_pos.le _))
    have hexp : z.im ^ (1 / 2 - u.re) * z.im ^ (1 / 2 + v.re) = z.im ^ (1 - u.re + v.re) := by
      rw [← Real.rpow_add z.im_pos]; ring_nf
    have hCb' : 0 ≤ (2 * rowBoundedConst u.re Y / ‖msA (u.re : ℂ)‖) * lineBoundConst v *
        (1 + Y ^ (1 / 2 + v.re)) := by positivity
    calc realTruncatedRowSum (1 / 2 + u.re) Y z * ‖eisensteinLineModel v z‖
        ≤ (rowDecayConst u.re * z.im ^ (1 / 2 - u.re)) *
            (2 * lineBoundConst v * z.im ^ (1 / 2 + v.re)) := hprod
      _ = 2 * rowDecayConst u.re * lineBoundConst v * z.im ^ (1 - u.re + v.re) := by
          rw [← hexp]; ring
      _ ≤ _ := by linarith

/-- The majorant is integrable on `𝒟`. -/
theorem integrableOn_unfoldedMajorant {u v : ℂ} (huv : v.re < u.re) (Y : ℝ) :
    IntegrableOn (unfoldedMajorant u v Y) fd volume := by
  unfold unfoldedMajorant
  have hβ : 1 - u.re + v.re < 1 := by linarith
  have h1 : IntegrableOn (fun z : ℍ => z.im ^ (1 - u.re + v.re)) fd volume := by
    have h : IntegrableOn (fun z : ℍ => ‖((z.im ^ (1 - u.re + v.re) : ℝ) : ℂ)‖) fd volume :=
      (integrableOn_fd_rpow hβ).norm
    refine h.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le _)]
  have h2 : IntegrableOn (fun _ : ℍ =>
      (2 * rowBoundedConst u.re Y / ‖msA (u.re : ℂ)‖) * lineBoundConst v *
        (1 + Y ^ (1 / 2 + v.re))) fd volume :=
    integrableOn_const (by simp [volume_fd_ne_top])
  exact h2.add (h1.const_mul _)

/-! ## Integrability of each unfolded term and of the norm series -/

theorem integrableOn_unfoldedIntegrand_row {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) (w : gammaSet 1 1 0) :
    IntegrableOn (fun z : ℍ => unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z))
      fd volume := by
  have hs : 1 < (1 / 2 + u).re := by rw [re_half_add]; linarith
  refine Integrable.mono' (integrableOn_unfoldedMajorant huv Y)
    (measurable_unfoldedIntegrand_row _ Y v w).aestronglyMeasurable ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz => ?_)
  refine le_trans ?_ (tsum_norm_unfoldedIntegrand_le hu hv1 hv hY hz)
  exact (summable_norm_unfoldedIntegrand_row hs Y hv z).le_tsum w (fun _ _ => norm_nonneg _)

theorem summable_setIntegral_norm_unfoldedIntegrand_row {u v : ℂ} (hu : 1 / 2 < u.re)
    (hv1 : 1 / 2 < v.re) (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (fun w : gammaSet 1 1 0 =>
      ∫ z in fd, ‖unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z)‖) := by
  have hs : 1 < (1 / 2 + u).re := by rw [re_half_add]; linarith
  refine summable_of_sum_le (fun w => integral_nonneg fun z => norm_nonneg _)
    (c := ∫ z in fd, unfoldedMajorant u v Y z) fun F => ?_
  rw [← integral_finsetSum F (fun w _ =>
    (integrableOn_unfoldedIntegrand_row hu hv1 huv hv hY w).norm)]
  refine setIntegral_mono_on ?_ (integrableOn_unfoldedMajorant huv Y)
    isClosed_fd.measurableSet fun z hz => ?_
  · exact integrable_finsetSum F fun w _ =>
      (integrableOn_unfoldedIntegrand_row hu hv1 huv hv hY w).norm
  · refine le_trans ?_ (tsum_norm_unfoldedIntegrand_le hu hv1 hv hY hz)
    exact (summable_norm_unfoldedIntegrand_row hs Y hv z).sum_le_tsum F
      (fun _ _ => norm_nonneg _)

/-! ## Integrability on the strip -/

theorem setIntegral_norm_halfRep_smul_fd (φ : ℍ → ℂ) (w : gammaSetHalf) :
    ∫ z in halfRep w • fd, ‖φ z‖ = ∫ z in fd, ‖φ (gammaSetMatrix w.1 • z)‖ := by
  have h := setIntegral_halfRep_smul_fd (fun z => ((‖φ z‖ : ℝ) : ℂ)) w
  unfold fdUnfoldTerm at h
  dsimp only at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

/-- **The unfolded integrand is integrable on the translation strip.** -/
theorem integrableOn_unfoldedIntegrand_strip {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (unfoldedIntegrand (1 / 2 + u) Y v) modularStrip volume := by
  have hT := unfoldedIntegrand_T (1 / 2 + u) Y hv
  have hunion : IntegrableOn (unfoldedIntegrand (1 / 2 + u) Y v)
      (⋃ w : gammaSetHalf, halfRep w • fd) volume := by
    refine integrableOn_iUnion_of_summable_integral_norm (fun w => ?_) ?_
    · rw [halfRep_smul_fd, integrableOn_smul_set_iff]
      exact integrableOn_unfoldedIntegrand_row hu hv1 huv hv hY w.1
    · simp_rw [setIntegral_norm_halfRep_smul_fd]
      exact (summable_setIntegral_norm_unfoldedIntegrand_row hu hv1 huv hv hY).subtype _
  exact (isFundamentalDomain_modularStrip.integrableOn_iff isFundamentalDomain_iUnion_halfRep_smul_fd
    (translationSubgroup_invariant_of_periodic hT)).mpr hunion

/-! ## The unfolding identity -/

theorem unfoldedIntegrand_eq_indicator (s : ℂ) (Y : ℝ) (v : ℂ) :
    unfoldedIntegrand s Y v =
      {ζ : ℍ | ζ.im ≤ Y}.indicator (fun ζ => (ζ.im : ℂ) ^ s * eisensteinLineModel v ζ) := by
  funext ζ
  unfold unfoldedIntegrand slabWeight
  by_cases h : ζ.im ≤ Y
  · rw [if_pos h, Set.indicator_of_mem (show ζ ∈ {ζ : ℍ | ζ.im ≤ Y} from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show ζ ∉ {ζ : ℍ | ζ.im ≤ Y} from h), zero_mul]

/-- **Unfolding.**  `∫_𝒟 (Σ_w [Im γ_w z ≤ Y] Im(γ_w z)^s) E_v = 2 ∫_{strip ∩ {Im ≤ Y}} y^s E_v`. -/
theorem setIntegral_truncatedRowSum_mul_eq {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z =
      2 * ∫ z in modularStrip ∩ {z : ℍ | z.im ≤ Y},
        (z.im : ℂ) ^ (1 / 2 + u) * eisensteinLineModel v z := by
  have hT := unfoldedIntegrand_T (1 / 2 + u) Y hv
  have hint := integrableOn_unfoldedIntegrand_strip hu hv1 huv hv hY
  have hunf := tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hT hint
  have hpt : ∀ z : ℍ, truncatedRowSum (1 / 2 + u) Y z * eisensteinLineModel v z =
      ∑' w : gammaSet 1 1 0, unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z) := by
    intro z
    simp_rw [unfoldedIntegrand_row _ Y hv]
    unfold truncatedRowSum
    rw [tsum_mul_right]
  have hswap : ∫ z in fd, ∑' w : gammaSet 1 1 0,
      unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z) =
      ∑' w : gammaSet 1 1 0, ∫ z in fd, unfoldedIntegrand (1 / 2 + u) Y v (gammaSetMatrix w • z) := by
    symm
    exact integral_tsum_of_summable_integral_norm
      (fun w => integrableOn_unfoldedIntegrand_row hu hv1 huv hv hY w)
      (summable_setIntegral_norm_unfoldedIntegrand_row hu hv1 huv hv hY)
  simp_rw [hpt]
  rw [hswap, hunf, unfoldedIntegrand_eq_indicator, setIntegral_indicator
    (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)]

end

end RHTower
