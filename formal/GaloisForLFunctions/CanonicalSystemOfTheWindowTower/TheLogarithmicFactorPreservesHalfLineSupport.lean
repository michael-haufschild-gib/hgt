import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorHasOneNegativeZero
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCauchyTotality
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# The logarithmic factor preserves half-line support

Resolvent regularization turns the actual logarithmic factor into bounded
holomorphic Hardy multipliers. Strong L² convergence proves support preservation
on the full multiplier graph domain; conjugation fixes the Fourier orientation.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The continued factor has a uniform linear growth bound on the closed right half-plane. -/
theorem continuedLogReferenceFactor_norm_sq_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖continuedLogReferenceFactor z‖ ^ 2 ≤
      (logarithmicFactorGrowthConstant + 1) * (1 + ‖z‖ ^ 2) := by
  by_cases hzero : z = 0
  · rw [hzero, continuedLogReferenceFactor_zero]
    norm_num only [norm_one, one_pow, norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, add_zero, mul_one]
    linarith only [logarithmicFactorGrowthConstant_pos]
  have hslit : z ∈ slitPlane := by
    by_cases hr : 0 < z.re
    · exact Or.inl hr
    · right
      intro hi
      apply hzero
      apply Complex.ext
      · exact le_antisymm (le_of_not_gt hr) hz
      · exact hi
  rw [continuedLogReferenceFactor_eq hslit]
  have hK : ‖complexLogReferenceFactor z‖ ^ 2 ≤
      logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ := by
    rcases hslit with hr | hi
    · exact complexLogReferenceFactor_norm_sq_le hr
    · exact complexLogReferenceFactor_norm_sq_le_closed hz hi
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖z‖ ^ 2)
  have hs : positiveLogarithmicSymbol ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by
    unfold positiveLogarithmicSymbol
    nlinarith only [hlog, sq_nonneg ‖z‖]
  calc
    _ ≤ logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ := hK
    _ ≤ logarithmicFactorGrowthConstant * (1 + ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs logarithmicFactorGrowthConstant_pos.le
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private theorem norm_one_add_real_mul_sq {z : ℂ} {e : ℝ} (hz : 0 ≤ z.re) (he : 0 ≤ e) :
    1 + e ^ 2 * ‖z‖ ^ 2 ≤ ‖1 + (e : ℂ) * z‖ ^ 2 := by
  have hformula : ‖1 + (e : ℂ) * z‖ ^ 2 = 1 + 2 * e * z.re + e ^ 2 * ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_im, Complex.one_im, Complex.mul_im, zero_add]
    ring
  rw [hformula]
  nlinarith only [mul_nonneg he hz]

/-- A first-order resolvent regularizes the actual logarithmic factor into a bounded multiplier. -/
theorem norm_regularizedLogReferenceFactor_le {z : ℂ} {e : ℝ}
    (hz : 0 ≤ z.re) (he : 0 < e) :
    ‖continuedLogReferenceFactor z / (1 + (e : ℂ) * z)‖ ≤
      Real.sqrt ((logarithmicFactorGrowthConstant + 1) * (1 + 1 / e ^ 2)) := by
  let M := (logarithmicFactorGrowthConstant + 1) * (1 + 1 / e ^ 2)
  have hC : 0 < logarithmicFactorGrowthConstant + 1 := by
    linarith only [logarithmicFactorGrowthConstant_pos]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hden := norm_one_add_real_mul_sq hz he.le
  have hdenpos : 0 < ‖1 + (e : ℂ) * z‖ := by
    have hn := norm_nonneg (1 + (e : ℂ) * z)
    have hp : 0 ≤ e ^ 2 * ‖z‖ ^ 2 := by positivity
    nlinarith only [hden, hn, hp]
  have haux : 1 + ‖z‖ ^ 2 ≤ (1 + 1 / e ^ 2) * (1 + e ^ 2 * ‖z‖ ^ 2) := by
    have heq : (1 + 1 / e ^ 2) * (1 + e ^ 2 * ‖z‖ ^ 2) - (1 + ‖z‖ ^ 2) =
        e ^ 2 * ‖z‖ ^ 2 + 1 / e ^ 2 := by
      field_simp [he.ne']
      ring
    have hp : 0 ≤ e ^ 2 * ‖z‖ ^ 2 + 1 / e ^ 2 := by positivity
    linarith only [heq, hp]
  have hnum : ‖continuedLogReferenceFactor z‖ ^ 2 ≤ M * ‖1 + (e : ℂ) * z‖ ^ 2 := by
    calc
      _ ≤ (logarithmicFactorGrowthConstant + 1) * (1 + ‖z‖ ^ 2) :=
        continuedLogReferenceFactor_norm_sq_le hz
      _ ≤ (logarithmicFactorGrowthConstant + 1) *
          ((1 + 1 / e ^ 2) * (1 + e ^ 2 * ‖z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left haux hC.le
      _ = M * (1 + e ^ 2 * ‖z‖ ^ 2) := by dsimp only [M]; ring
      _ ≤ M * ‖1 + (e : ℂ) * z‖ ^ 2 := mul_le_mul_of_nonneg_left hden hM
  rw [norm_div]
  have hsq : (‖continuedLogReferenceFactor z‖ / ‖1 + (e : ℂ) * z‖) ^ 2 ≤ M := by
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hdenpos)).mpr hnum
  have hsqrt := Real.sq_sqrt hM
  have hnonneg := Real.sqrt_nonneg M
  change _ ≤ Real.sqrt M
  nlinarith only [hsq, hsqrt, hnonneg]

/-- Rotation puts the logarithmic factor over the upper Hardy half-plane. -/
def logarithmicHardyArgument (q : ℝ) (z : ℂ) : ℂ := -(q : ℂ) * Complex.I * z

theorem logarithmicHardyArgument_re (q : ℝ) (z : ℂ) :
    (logarithmicHardyArgument q z).re = q * z.im := by
  simp only [logarithmicHardyArgument, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_sub, neg_mul, neg_neg]

/-- Each positive resolvent parameter gives a bounded multiplier of the actual Hardy space. -/
def logarithmicHardyRegularizer (q e : ℝ) (hq : 0 ≤ q) (he : 0 < e) :
    HTGeometry.ClosedUpperHalfPlaneMultiplier where
  fn z := continuedLogReferenceFactor (logarithmicHardyArgument q z) /
    (1 + (e : ℂ) * logarithmicHardyArgument q z)
  bound := Real.sqrt ((logarithmicFactorGrowthConstant + 1) * (1 + 1 / e ^ 2))
  bound_nonneg := Real.sqrt_nonneg _
  diff z hz := by
    have hr : 0 ≤ (logarithmicHardyArgument q z).re := by
      rw [logarithmicHardyArgument_re]
      exact mul_nonneg hq hz
    have hd := (analyticOnNhd_continuedLogReferenceFactor _
      (Or.inl (by linarith only [hr]))).differentiableAt
    have harg : DifferentiableAt ℂ (logarithmicHardyArgument q) z := by
      unfold logarithmicHardyArgument
      fun_prop
    have hfn : DifferentiableAt ℂ (fun w => continuedLogReferenceFactor (logarithmicHardyArgument q w)) z := by
      simpa only [Function.comp_def] using! hd.comp z harg
    have hden : 1 + (e : ℂ) * logarithmicHardyArgument q z ≠ 0 := by
      intro hzero
      have h := norm_one_add_real_mul_sq hr he.le
      rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
      have hp : 0 ≤ e ^ 2 * ‖logarithmicHardyArgument q z‖ ^ 2 := by positivity
      linarith only [h, hp]
    exact hfn.div ((harg.const_mul (e : ℂ)).const_add 1) hden
  norm_le z hz := norm_regularizedLogReferenceFactor_le
    (by rw [logarithmicHardyArgument_re]; exact mul_nonneg hq hz) he

/-- The scalar resolvents are contractions on the frequency axis. -/
def logarithmicHardyResolvent (q e x : ℝ) : ℂ :=
  1 / (1 + (e : ℂ) * logarithmicHardyArgument q (x : ℂ))

private theorem logarithmicHardyResolvent_den_re (q e x : ℝ) :
    (1 + (e : ℂ) * logarithmicHardyArgument q (x : ℂ)).re = 1 := by
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, logarithmicHardyArgument_re,
    Complex.ofReal_im, mul_zero, add_zero]

private theorem logarithmicHardyResolvent_den_ne (q e x : ℝ) :
    1 + (e : ℂ) * logarithmicHardyArgument q (x : ℂ) ≠ 0 := by
  intro hzero
  have h := congrArg Complex.re hzero
  rw [logarithmicHardyResolvent_den_re, Complex.zero_re] at h
  exact one_ne_zero h

theorem norm_logarithmicHardyResolvent_le_one (q e x : ℝ) :
    ‖logarithmicHardyResolvent q e x‖ ≤ 1 := by
  have hden : 1 ≤ ‖1 + (e : ℂ) * logarithmicHardyArgument q (x : ℂ)‖ := by
    rw [← logarithmicHardyResolvent_den_re q e x]
    exact Complex.re_le_norm _
  rw [logarithmicHardyResolvent, norm_div, norm_one]
  simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden

theorem continuous_logarithmicHardyResolvent (q e : ℝ) : Continuous (logarithmicHardyResolvent q e) := by
  unfold logarithmicHardyResolvent logarithmicHardyArgument
  exact continuous_const.div (by fun_prop) (logarithmicHardyResolvent_den_ne q e)

/-- Multiplication by the actual unbounded factor preserves upper Hardy support on its full graph domain. -/
theorem logarithmicFactor_mul_mem_hardy {q : ℝ} (hq : 0 ≤ q)
    {u v : HTGeometry.RealLineL2} (hu : u ∈ RHTower.hardyL2)
    (huv : (v : ℝ → ℂ) =ᵐ[volume] fun x =>
      continuedLogReferenceFactor (logarithmicHardyArgument q (x : ℂ)) * (u : ℝ → ℂ) x) :
    v ∈ RHTower.hardyL2 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  let F (n : ℕ) := logarithmicHardyRegularizer q (e n) hq (he n)
  have hφ (n : ℕ) : Measurable (logarithmicHardyResolvent q (e n)) :=
    (continuous_logarithmicHardyResolvent q (e n)).measurable
  have hψ : Measurable (fun _ : ℝ => (1 : ℂ)) := measurable_const
  have hbφ (n : ℕ) (x : ℝ) : ‖logarithmicHardyResolvent q (e n) x‖ ≤ 1 :=
    norm_logarithmicHardyResolvent_le_one _ _ _
  have hbψ (x : ℝ) : ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
  let T (n : ℕ) : HTGeometry.RealLineL2 →L[ℂ] HTGeometry.RealLineL2 :=
    lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (hφ n) (by norm_num) (hbφ n)
  let S : HTGeometry.RealLineL2 →L[ℂ] HTGeometry.RealLineL2 :=
    lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hψ (by norm_num) hbψ
  have hT (n : ℕ) : T n v = (F n).boundaryMul u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (hφ n) (by norm_num) (hbφ n) v, (F n).coe_boundaryMul u, huv] with x ht hf huvx
    rw [ht, hf, huvx]
    change logarithmicHardyResolvent q (e n) x *
        (continuedLogReferenceFactor (logarithmicHardyArgument q (x : ℂ)) * (u : ℝ → ℂ) x) =
      (continuedLogReferenceFactor (logarithmicHardyArgument q (x : ℂ)) /
        (1 + (e n : ℂ) * logarithmicHardyArgument q (x : ℂ))) * (u : ℝ → ℂ) x
    unfold logarithmicHardyResolvent
    ring
  have hS : S v = v := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      hψ (by norm_num) hbψ v] with x hx
    simpa only [one_mul] using hx
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hezero : Tendsto e atTop (nhds (0 : ℝ)) := by
    simpa only [e, one_div, Function.comp_def] using! tendsto_inv_atTop_zero.comp hnat
  have hpoint (x : ℝ) : Tendsto (fun n => logarithmicHardyResolvent q (e n) x) atTop (nhds 1) := by
    have hc : Tendsto (fun n => (e n : ℂ)) atTop (nhds (0 : ℂ)) := by
      simpa only [Complex.ofReal_zero] using! Complex.continuous_ofReal.continuousAt.tendsto.comp hezero
    have hden := (tendsto_const_nhds (x := (1 : ℂ))).add
      (hc.mul_const (logarithmicHardyArgument q (x : ℂ)))
    simp only [zero_mul, add_zero] at hden
    simpa only [logarithmicHardyResolvent, one_div, inv_one] using!
      hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have htend : Tendsto (fun n => T n v) atTop (nhds v) := by
    have h := tendsto_lpBoundedMulCLM_apply hφ hψ (by norm_num : (0 : ℝ) ≤ 1) hbφ hbψ hpoint v
    change Tendsto (fun n => T n v) atTop (nhds (S v)) at h
    rwa [hS] at h
  apply RHTower.isClosed_hardyL2.mem_of_tendsto htend
  filter_upwards with n
  rw [hT]
  exact (F n).boundaryMul_mem_hardy ⟨u, hu⟩

/-- The continuation respects conjugation throughout the closed right half-plane. -/
theorem continuedLogReferenceFactor_conj_right {z : ℂ} (hz : 0 ≤ z.re) :
    continuedLogReferenceFactor (starRingEnd ℂ z) = starRingEnd ℂ (continuedLogReferenceFactor z) := by
  by_cases hzero : z = 0
  · simp only [hzero, map_zero, continuedLogReferenceFactor_zero, map_one]
  have hslit : z ∈ slitPlane := by
    by_cases hr : 0 < z.re
    · exact Or.inl hr
    · right
      intro hi
      exact hzero (Complex.ext (le_antisymm (le_of_not_gt hr) hz) hi)
  have hstar : starRingEnd ℂ z ∈ slitPlane := by
    rcases hslit with hr | hi
    · exact Or.inl (by simpa only [Complex.conj_re] using hr)
    · exact Or.inr (by simpa only [Complex.conj_im, neg_ne_zero] using hi)
  rw [continuedLogReferenceFactor_eq hstar, continuedLogReferenceFactor_eq hslit,
    complexLogReferenceFactor_conj hslit]

private theorem star_logarithmicHardyArgument (q x : ℝ) :
    starRingEnd ℂ (logarithmicHardyArgument q (x : ℂ)) = -logarithmicHardyArgument q (x : ℂ) := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.neg_re, logarithmicHardyArgument_re,
      Complex.ofReal_im, mul_zero, neg_zero]
  · simp only [Complex.conj_im, Complex.neg_im]

/-- Conjugation transports the actual factor graph to lower Hardy space. -/
theorem logarithmicFactor_mul_mem_hardy_orthogonal {q : ℝ} (hq : 0 ≤ q)
    {u v : HTGeometry.RealLineL2} (hu : u ∈ RHTower.hardyL2ᗮ)
    (huv : (v : ℝ → ℂ) =ᵐ[volume] fun x =>
      continuedLogReferenceFactor (-logarithmicHardyArgument q (x : ℂ)) * (u : ℝ → ℂ) x) :
    v ∈ RHTower.hardyL2ᗮ := by
  have hstaru : star u ∈ RHTower.hardyL2 := by
    rw [← RHTower.map_star_hardyL2] at hu
    obtain ⟨w, hw, heq⟩ := hu
    rw [← heq]
    change star (star w) ∈ RHTower.hardyL2
    rwa [RHTower.star_star_lp]
  have hstarv : star v ∈ RHTower.hardyL2 := by
    apply logarithmicFactor_mul_mem_hardy hq hstaru
    filter_upwards [Lp.coeFn_star u, Lp.coeFn_star v, huv] with x hu hv huvx
    rw [hu, hv]
    simp only [Pi.star_apply, RCLike.star_def, huvx, map_mul]
    have hc := continuedLogReferenceFactor_conj_right
      (z := -logarithmicHardyArgument q (x : ℂ))
      (by simp only [Complex.neg_re, logarithmicHardyArgument_re, Complex.ofReal_im,
        mul_zero, neg_zero, le_refl])
    rw [map_neg, star_logarithmicHardyArgument, neg_neg] at hc
    rw [← hc]
  rw [← RHTower.map_star_hardyL2]
  exact ⟨star v, hstarv, RHTower.star_star_lp v⟩

/-- The logarithmic inverse multiplier preserves positive-half-line support on its actual L² domain. -/
theorem logarithmicFactor_preserves_halfLine_support
    {u v : HTGeometry.RealLineL2} (hu : u ∈ RHTower.halfLineL2)
    (huv : ((Lp.fourierTransformₗᵢ ℝ ℂ v : HTGeometry.RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => continuedLogReferenceFactor (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ u : HTGeometry.RealLineL2) : ℝ → ℂ) x) :
    v ∈ RHTower.halfLineL2 := by
  have hFu : Lp.fourierTransformₗᵢ ℝ ℂ u ∈ RHTower.hardyL2ᗮ := by
    rw [RHTower.hardyL2_orthogonal]
    exact ⟨u, hu, rfl⟩
  have hFv : Lp.fourierTransformₗᵢ ℝ ℂ v ∈ RHTower.hardyL2ᗮ := by
    apply logarithmicFactor_mul_mem_hardy_orthogonal (q := 2 * Real.pi)
      (by positivity) hFu
    filter_upwards [huv] with x hx
    have he : -logarithmicHardyArgument (2 * Real.pi) (x : ℂ) =
        ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      simp only [logarithmicHardyArgument, Complex.ofReal_mul]
      ring
    rw [he]
    exact hx
  rw [RHTower.hardyL2_orthogonal] at hFv
  obtain ⟨w, hw, heq⟩ := hFv
  have hwv : w = v := (Lp.fourierTransformₗᵢ ℝ ℂ).injective heq
  exact hwv ▸ hw

#print axioms norm_regularizedLogReferenceFactor_le
#print axioms logarithmicFactor_mul_mem_hardy
#print axioms logarithmicFactor_preserves_halfLine_support

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
