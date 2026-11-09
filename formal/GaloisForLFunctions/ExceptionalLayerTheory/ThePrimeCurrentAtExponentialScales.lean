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
    simpa only [Complex.add_im, Complex.sub_im, Complex.one_im,
      Complex.ofNat_im, zero_sub, add_zero, abs_neg,
      abs_of_nonneg (zero_le_one.trans ht)] using h
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
    Finset.single_le_sum (fun _ _ => abs_nonneg _) hq
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
  have hc := norm_gaussianContinuum_pole_error_le (by simpa using hu.2)
    (by simpa using ht1) (Real.exp_pos (-a * t)) hy1
  rw [dist_zero_left, exceptionalGaussianExpansionError_eq F hs0 hsne1 (hregular t ht u hu.1)]
  have hftu := hft u hu
  rw [dist_zero_left] at hftu
  exact (norm_add_le _ _).trans_lt (by linarith only [hftu, hc, hEt])

#print axioms norm_gaussianContinuum_pole_error_le
#print axioms not_asymptoticAbscissaLaw_has_full_exponential_expansion

end GaloisForLFunctions.ExceptionalLayerTheory
