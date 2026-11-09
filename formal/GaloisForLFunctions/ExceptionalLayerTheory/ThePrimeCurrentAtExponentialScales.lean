import GaloisForLFunctions.ExceptionalLayerTheory.TheGaussianObservationBoundary

/-!
# The prime current at exponential scales

The Gaussian pole and the finite exceptional divisor give the complete
expansion of the infinite prime current at damping `exp (-a t)`.
The error vanishes for every positive speed, uniformly in the observation
abscissa on a high strip. In particular, a growing pole cannot be discarded
when comparing different damping regimes.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

open EulerFETransportTheory

/-- Error after retaining the pole and the specified exceptional divisor
in the literal infinite von Mangoldt current. -/
def exceptionalGaussianExpansionError (F : Finset XiZeroCopy) (s : ℂ) (y : ℝ) : ℂ :=
  gaussianDampedPrimeSum s y + (Real.exp (-y) : ℂ) * logDeriv riemannZeta s -
    gaussianMBKernel y (1 - s) + ∑ q ∈ F, gaussianMBKernel y (xiZero q - s)

/-- The pole mode differs from the continuum and its endpoint term by
at most `4y`, uniformly throughout the high positive strip. -/
theorem norm_gaussianContinuum_pole_error_le {s : ℂ} {y : ℝ}
    (hs1 : s.re ≤ 1) (ht : 1 ≤ s.im) (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖(Real.exp (-y) : ℂ) / (1 - s) + gaussianIncompleteMellin y (1 - s) -
      gaussianMBKernel y (1 - s)‖ ≤ 4 * y := by
  have hnorm : 1 ≤ ‖(1 : ℂ) - s‖ := by
    refine ht.trans ?_
    have h := Complex.abs_im_le_norm ((1 : ℂ) - s)
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
      abs_of_nonneg (zero_le_one.trans ht)] using h
  have hnorm₂ : 1 ≤ ‖(1 : ℂ) - s + 2‖ := by
    refine ht.trans ?_
    have h := Complex.abs_im_le_norm ((1 : ℂ) - s + 2)
    simpa [abs_of_nonneg (zero_le_one.trans ht)] using h
  have hne : (1 : ℂ) - s ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hnorm)
  have hb := norm_zeroGerm_sub_gamma_le hy
    (show -2 < ((1 : ℂ) - s).re by simp only [Complex.sub_re, Complex.one_re]; linarith only [hs1]) hne
  change ‖(Real.exp (-y) : ℂ) / (1 - s) + gaussianIncompleteMellin y (1 - s) -
    gaussianMBKernel y (1 - s)‖ ≤ _ at hb
  have hden : 1 ≤ ‖(1 : ℂ) - s‖ * ‖(1 : ℂ) - s + 2‖ := by
    nlinarith only [hnorm, hnorm₂, mul_nonneg (sub_nonneg.mpr hnorm) (sub_nonneg.mpr hnorm₂)]
  calc
    _ ≤ (2 * y + 2 * y ^ 2) / (‖(1 : ℂ) - s‖ * ‖(1 : ℂ) - s + 2‖) := hb
    _ ≤ (2 * y + 2 * y ^ 2) / 1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hden
    _ ≤ 4 * y := by
      rw [div_one]
      nlinarith only [mul_le_mul_of_nonneg_left hy1 hy.le]

private theorem exceptionalGaussianExpansionError_eq (F : Finset XiZeroCopy)
    {s : ℂ} (hs0 : 0 < s.re) (hsne1 : s ≠ 1) (hxi : xi s ≠ 0) (y : ℝ) :
    exceptionalGaussianExpansionError F s y = finiteGaussianFinitePartError F s y +
      ((Real.exp (-y) : ℂ) / (1 - s) + gaussianIncompleteMellin y (1 - s) -
        gaussianMBKernel y (1 - s)) := by
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    apply hxi
    have hsne0 : s ≠ 0 := by intro h; simp [h] at hs0
    rw [xi_eq_xiUnit_mul_zeta hsne0 hsne1 hs0, hz, mul_zero]
  have hdec : gaussianArchimedeanCurrent s - logDeriv xi s =
      -logDeriv riemannZeta s - (s - 1)⁻¹ := by
    rw [logDeriv_zeta_eq_logDeriv_xi hs0 hsne1 hζ, gaussianArchimedeanCurrent]
    ring
  rw [exceptionalGaussianExpansionError, finiteGaussianFinitePartError,
    gaussianPrimeContinuumGap, hdec, show (1 : ℂ) - s = -(s - 1) by ring,
    div_neg, div_eq_mul_inv]
  ring

/-- In the actual finite-layer world, the pole and the finite exceptional
divisor determine the entire current at every exponential damping speed.
The complementary infinite divisor contributes an error tending to zero. -/
theorem not_asymptoticAbscissaLaw_has_full_exponential_expansion :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (θ σ : ℝ),
        1 / 2 ≤ θ ∧ θ < σ ∧ σ < 1 ∧
        (∃ q ∈ F, σ < (xiZero q).re) ∧
        (∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) ∧
        ∀ a : ℝ, 0 < a →
          TendstoUniformlyOn (fun t : ℝ => fun u : ℝ =>
            exceptionalGaussianExpansionError F ((u : ℂ) + t * I) (Real.exp (-a * t)))
            (fun _ => 0) atTop (Set.Icc σ 1) := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, hθ, hgap, hσ1, hq, hrest, hfinite⟩ :=
    not_asymptoticAbscissaLaw_has_exponential_finite_part hnot
  let M : ℝ := ∑ q ∈ F, |(xiZero q).im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ q ∈ F, |(xiZero q).im| ≤ M := fun q hq =>
    Finset.single_le_sum (fun p _ => abs_nonneg (xiZero p).im) hq
  have hregular : ∀ t : ℝ, M + 2 ≤ t → ∀ u : ℝ, σ ≤ u →
      xi ((u : ℂ) + t * I) ≠ 0 := by
    intro t ht u hu hz
    obtain ⟨q, hqs⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
    by_cases hqF : q ∈ F
    · have hm := hM q hqF
      change |(q.1 : ℂ).im| ≤ M at hm
      rw [hqs] at hm
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hm
      linarith only [hm, ht, le_abs_self t]
    · have hr := hrest q hqF
      change (q.1 : ℂ).re ≤ θ at hr
      rw [hqs] at hr
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hr
      linarith only [hr, hu, hgap]
  refine ⟨F, θ, σ, hθ, hgap, hσ1, hq, hrest, fun a ha => ?_⟩
  have hE : Tendsto (fun t : ℝ => 4 * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, mul_zero, neg_mul] using
      (HTGeometry.tendsto_pow_mul_exp_neg_scaled 0 ha).const_mul 4
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hf := Metric.tendstoUniformlyOn_iff.mp (hfinite a ha) (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (M + 2), hf,
    hE.eventually (eventually_lt_nhds (by positivity : 0 < ε / 2))] with t ht hft hEt
  intro u hu
  have ht1 : 1 ≤ t := by linarith only [ht, hM0]
  have hs0 : 0 < ((u : ℂ) + t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hθ, hgap, hu.1]
  have hsne1 : (u : ℂ) + t * I ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at hh
    linarith only [hh, ht1]
  have hy1 : Real.exp (-a * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [ha, ht1])
  have hc := norm_gaussianContinuum_pole_error_le (s := (u : ℂ) + t * I)
    (by simpa using hu.2)
    (by simpa using ht1) (Real.exp_pos (-a * t)) hy1
  rw [dist_zero_left, exceptionalGaussianExpansionError_eq F hs0 hsne1 (hregular t ht u hu.1)]
  have hftu := hft u hu
  rw [dist_zero_left] at hftu
  exact (norm_add_le _ _).trans_lt (by linarith only [hftu, hc, hEt])

private theorem exists_logDeriv_linear_bound (F : Finset XiZeroCopy)
    {θ σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ C * t := by
  classical
  let δ : ℝ := min (σ - θ) 1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hgap) zero_lt_one
  let M : ℝ := ∑ q ∈ F, |(xiZero q).im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ q ∈ F, |(xiZero q).im| ≤ M := fun q hq =>
    Finset.single_le_sum (fun p _ => abs_nonneg (xiZero p).im) hq
  let C : ℝ := |logDerivZetaConstant / δ| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (M + δ + 4)] with t ht
  have ht4 : 4 ≤ t := by linarith only [ht, hM0, hδ]
  have hsep : ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - ((σ : ℂ) + t * I)‖ := by
    intro q
    by_cases hq : q ∈ F
    · have hm := hM q hq
      have him : δ ≤ t - (xiZero q).im := by
        linarith only [hm, ht, le_abs_self (xiZero q).im]
      have hn := Complex.im_le_norm (((σ : ℂ) + t * I) - xiZero q)
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        add_zero, zero_add] at hn
      rw [norm_sub_rev] at hn
      exact him.trans hn
    · have hr := hrest q hq
      have hre : δ ≤ σ - (xiZero q).re := by
        have hd : δ ≤ σ - θ := min_le_left _ _
        linarith only [hr, hd]
      have hn := Complex.re_le_norm (((σ : ℂ) + t * I) - xiZero q)
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero] at hn
      rw [norm_sub_rev] at hn
      exact hre.trans hn
  have hb := norm_logDeriv_zeta_le hσ.le (by linarith only [hσ1] : σ ≤ 2) ht4
    hδ (min_le_right _ _) (fun q => by
      simpa only [norm_sub_rev, xiZero] using hsep q)
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht4])
  have hlogt : Real.log t ≤ t := Real.log_le_self (by linarith only [ht4])
  calc
    _ ≤ logDerivZetaConstant * Real.log t / δ := hb
    _ ≤ C * Real.log t := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_abs_self _) (by dsimp only [C]; linarith)) hlog0
    _ ≤ C * t := mul_le_mul_of_nonneg_left hlogt hC.le

/-- At some exponential observation speeds the full prime current is
asymptotic to its growing pole mode, while every exceptional zero mode
vanishes. Thus passage at inverse height cannot be extrapolated to all
exponential scales, even in the finite-layer world. -/
theorem not_asymptoticAbscissaLaw_has_pole_dominated_prime_current :
    ¬ AsymptoticAbscissaLaw →
      ∃ σ a : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < a ∧
        (∃ q : XiZeroCopy, σ < (xiZero q).re) ∧
        Tendsto (fun t : ℝ =>
          gaussianDampedPrimeSum ((σ : ℂ) + t * I) (Real.exp (-a * t)) /
            gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I)))
          atTop (𝓝 1) ∧
        Tendsto (fun t : ℝ =>
          ‖gaussianDampedPrimeSum ((σ : ℂ) + t * I) (Real.exp (-a * t))‖)
          atTop atTop := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, hθ, hgap, hσ1, ⟨q₁, hq₁F, hq₁⟩, hrest, hexp⟩ :=
    not_asymptoticAbscissaLaw_has_full_exponential_expansion hnot
  have hσ : 1 / 2 < σ := lt_of_le_of_lt hθ hgap
  obtain ⟨q₀, _, hmax⟩ := F.exists_max_image (fun q => (xiZero q).re) ⟨q₁, hq₁F⟩
  have hq₀1 : (xiZero q₀).re < 1 := xiZeroCopy_re_lt_one q₀
  obtain ⟨b, hβb, hb1⟩ := exists_between hq₀1
  have hσb : σ < b := (hq₁.trans_le (hmax q₁ hq₁F)).trans hβb
  let a : ℝ := Real.pi / (2 * (b - σ))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a * (b - σ) = Real.pi / 2 := by
    dsimp only [a]
    field_simp [ne_of_gt (sub_pos.mpr hσb)]
  have hr : ∀ q ∈ F, gaussianObservationRate (xiZero q) σ a < 0 := by
    intro q hq
    have hqb := (hmax q hq).trans_lt hβb
    have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hqb σ) ha
    rw [hab] at hlt
    dsimp only [gaussianObservationRate]
    linarith only [hlt]
  have hp : 0 < gaussianObservationRate 1 σ a := by
    have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hb1 σ) ha
    rw [hab] at hlt
    simp only [gaussianObservationRate, Complex.one_re]
    linarith only [hlt]
  let P : ℝ → ℂ := fun t =>
    gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I))
  let J : ℝ → ℂ := fun t => gaussianDampedPrimeSum ((σ : ℂ) + t * I) (Real.exp (-a * t))
  let L : ℝ → ℂ := fun t =>
    (Real.exp (-(Real.exp (-a * t))) : ℂ) * logDeriv riemannZeta ((σ : ℂ) + t * I)
  have hP : Tendsto (fun t => ‖P t‖) atTop atTop :=
    tendsto_norm_gaussianMode_atTop_of_positive_rate 1 σ a hp
  have hPi : Tendsto (fun t => (P t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_gaussianMode_zero_of_positive_rate 1 σ a hp
  have hsum : Tendsto (fun t : ℝ => ∑ q ∈ F,
      gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((σ : ℂ) + t * I)))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum F
      (fun q hq => tendsto_gaussianMode_zero_of_negative_rate (xiZero q) σ a (hr q hq))
  have herror : Tendsto (fun t => J t + L t - P t) atTop (𝓝 0) := by
    have hh := ((hexp a ha).tendsto_at ⟨le_rfl, hσ1.le⟩).sub hsum
    simpa only [exceptionalGaussianExpansionError, add_sub_cancel_right, sub_zero] using hh
  obtain ⟨B, hB, hlog⟩ := exists_logDeriv_linear_bound F hσ hσ1.le hgap hrest
  obtain ⟨C, D, N, M, _, hD, hbounds⟩ := exists_gaussianMode_exponential_bounds 1 σ
  have hL : Tendsto (fun t => L t / P t) atTop (𝓝 0) := by
    apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp (C := B * D) (N := M + 1) hp
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with t ht ht2
    have ht0 : 0 ≤ t := by linarith only [ht2]
    have he : ‖(Real.exp (-(Real.exp (-a * t))) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
    have hnormL : ‖L t‖ ≤ B * t := by
      dsimp only [L]
      rw [norm_mul]
      exact (mul_le_mul he ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hb := (hbounds t (by simpa only [Complex.one_im, abs_zero, zero_add] using ht2) a).2
    change ‖(P t)⁻¹‖ ≤ D * t ^ M * Real.exp (-(gaussianObservationRate 1 σ a * t)) at hb
    rw [div_eq_mul_inv, norm_mul]
    calc
      _ ≤ (B * t) * (D * t ^ M * Real.exp (-(gaussianObservationRate 1 σ a * t))) :=
        mul_le_mul hnormL hb (norm_nonneg _) (mul_nonneg hB.le ht0)
      _ = _ := by rw [pow_succ]; ring
  have hratio : Tendsto (fun t => J t / P t) atTop (𝓝 1) := by
    have hE := herror.mul hPi
    simp only [mul_zero] at hE
    have hh := (hE.sub hL).add_const 1
    simp only [sub_zero, zero_add] at hh
    refine hh.congr' ?_
    filter_upwards [hP.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    have hne : P t ≠ 0 := norm_pos_iff.mp ht
    simp only [div_eq_mul_inv]
    field_simp [hne]
    ring
  refine ⟨σ, a, hσ, hσ1, ha, ⟨q₁, hq₁⟩, hratio, ?_⟩
  have hnormRatio : Tendsto (fun t => ‖J t / P t‖) atTop (𝓝 1) := by
    simpa only [norm_one] using hratio.norm
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hnormRatio.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hP.eventually (eventually_ge_atTop (2 * b)),
    hP.eventually (eventually_gt_atTop (0 : ℝ))] with t ht hb ht0
  rw [norm_div] at ht
  have hlt := (lt_div_iff₀ ht0).mp ht
  nlinarith only [hlt, hb]

#print axioms norm_gaussianContinuum_pole_error_le
#print axioms not_asymptoticAbscissaLaw_has_full_exponential_expansion
#print axioms not_asymptoticAbscissaLaw_has_pole_dominated_prime_current

end GaloisForLFunctions.ExceptionalLayerTheory
