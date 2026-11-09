import GaloisForLFunctions.EulerFETransportTheory.OnlyExceptionalGaussianModesRemain
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall

/-!
# Raw-prime passage at inverse-height damping

At damping `1 / im s`, the finitely many exceptional Gamma modes vanish at
high ordinates, and the entire complementary field vanishes by its horizontal
gap. The Gaussian prime current therefore recovers the normalized continued
finite part on a high interior strip, with no divisor counterterm.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Oscillation removes the continuum at inverse-height damping. One Mellin
recursion gains a factor of height before the Gaussian integral is bounded. -/
theorem norm_gaussianContinuum_inverseHeight_le {s : ℂ}
    (hs : 0 < s.re) (ht : 1 ≤ s.im) :
    ‖gaussianIncompleteMellin (1 / s.im) (1 - s)‖ ≤
      1 / s.im + Real.Gamma (3 / 2) * (1 / s.im) ^ (1 / 2 : ℝ) := by
  let y : ℝ := 1 / s.im
  have ht0 : 0 < s.im := by linarith
  have hy : 0 < y := by dsimp [y]; positivity
  have hnorm : s.im ≤ ‖1 - s‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, abs_of_pos ht0] using
      Complex.abs_im_le_norm (1 - s)
  have ha : (1 : ℂ) - s ≠ 0 := norm_pos_iff.mp (ht0.trans_le hnorm)
  have hE := norm_gaussianIncompleteMellin_le hy (r := 2) (by norm_num)
    (b := 1 - s + 2) (by simp; linarith)
  norm_num only at hE
  have he : ‖-(Real.exp (-y) : ℂ) / (1 - s)‖ ≤ 1 / s.im := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 / ‖1 - s‖ := div_le_div_of_nonneg_right
        (Real.exp_le_one_iff.mpr (by linarith)) (norm_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le ht0 hnorm
  have htail : ‖(2 * (y : ℂ) / (1 - s)) * gaussianIncompleteMellin y (1 - s + 2)‖ ≤
      (2 * y / s.im) * (y ^ (-(3 : ℝ) / 2) * (1 / 2) * Real.Gamma (3 / 2)) := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy]
    exact mul_le_mul (div_le_div_of_nonneg_left (by positivity) ht0 hnorm)
      hE (norm_nonneg _) (by positivity)
  have hpow : y ^ 2 * y ^ (-(3 : ℝ) / 2) = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 1
    norm_num
  have htailval : (2 * y / s.im) *
      (y ^ (-(3 : ℝ) / 2) * (1 / 2) * Real.Gamma (3 / 2)) =
        Real.Gamma (3 / 2) * y ^ (1 / 2 : ℝ) := by
    calc
      _ = Real.Gamma (3 / 2) * (y ^ 2 * y ^ (-(3 : ℝ) / 2)) := by dsimp [y]; ring
      _ = _ := by rw [hpow]
  change ‖gaussianIncompleteMellin y (1 - s)‖ ≤ _
  rw [gaussianIncompleteMellin_recursion hy ha]
  exact (norm_add_le _ _).trans (add_le_add he (htail.trans_eq htailval))

private theorem norm_finiteGaussianModes_inverseHeight_le {K M : ℝ}
    (hK : 0 < K)
    (hk : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 → xi s ≠ 0 → ∀ q : XiZeroCopy,
      ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤ K * ‖(xiZero q - s)⁻¹‖ ^ 2)
    (F : Finset XiZeroCopy) (hM : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ M)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hxi : xi s ≠ 0)
    (ht : 1 ≤ s.im) (htM : 2 * M ≤ s.im) :
    ‖∑ q ∈ F, gaussianMBKernel (1 / s.im) (xiZero q - s)‖ ≤
      4 * K * F.card / s.im := by
  have ht0 : 0 < s.im := by linarith
  let y : ℝ := 1 / s.im
  have hy : 0 < y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := (div_le_one ht0).mpr ht
  have hterm : ∀ q ∈ F, ‖gaussianMBKernel y (xiZero q - s)‖ ≤ 4 * K / s.im := by
    intro q hq
    have hnorm : s.im / 2 ≤ ‖xiZero q - s‖ := by
      have him : s.im / 2 ≤ s.im - (q.1 : ℂ).im := by
        linarith [hM q hq, le_abs_self (q.1 : ℂ).im]
      have h := Complex.im_le_norm (s - (q.1 : ℂ))
      rw [Complex.sub_im, norm_sub_rev] at h
      exact him.trans h
    have hi : ‖(xiZero q - s)⁻¹‖ ≤ 2 / s.im := by
      rw [norm_inv]
      calc
        _ ≤ (s.im / 2)⁻¹ := inv_anti₀ (by positivity) hnorm
        _ = _ := by field_simp
    have hunit : ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤ K * (2 / s.im) ^ 2 := by
      refine (hk s hs0 hs1 hxi q).trans ?_
      apply mul_le_mul_of_nonneg_left _ hK.le
      nlinarith [norm_nonneg ((xiZero q - s)⁻¹)]
    have hp : y ^ (-((xiZero q - s) / 2)).re ≤ s.im := by
      calc
        _ ≤ y ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by
          have hq1 : (xiZero q).re < 1 := xiZeroCopy_re_lt_one q
          simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re]
          linarith)
        _ = _ := by simp [y, Real.rpow_neg_one, one_div]
    have he : ‖gaussianMBKernel y (xiZero q - s)‖ =
        ‖gaussianMBKernel 1 (xiZero q - s)‖ * y ^ (-((xiZero q - s) / 2)).re := by
      simp only [gaussianMBKernel, Complex.ofReal_one, Complex.one_cpow, mul_one]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    rw [he]
    calc
      _ ≤ (K * (2 / s.im) ^ 2) * s.im := mul_le_mul hunit hp (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ q ∈ F, ‖gaussianMBKernel y (xiZero q - s)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ F, 4 * K / s.im := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Failure of AAL supplies an interior high strip on which the raw Gaussian
prime discrepancy recovers its continued finite part at damping `1 / im s`.
No divisor-defined counterterm remains in this limit. -/
theorem not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → T ≤ s.im →
        ‖gaussianPrimeContinuumGap s (1 / s.im) -
          (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
  classical
  obtain ⟨F, θ, σ, H, C, hθ, hgap, hσ1, hH, hC, hq, hrest, hbound, _⟩ :=
    not_asymptoticAbscissaLaw_has_finiteGaussianControl hnot
  obtain ⟨K, hK, hk⟩ := exists_gaussianMode_unit_bound
  let M : ℝ := ∑ q ∈ F, |(q.1 : ℂ).im|
  have hM : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ M := by
    intro q hq
    exact Finset.single_le_sum (fun p _ => abs_nonneg (p.1 : ℂ).im) hq
  let T₀ : ℝ := max H (max 4 (2 * M + 2))
  have hT₀4 : 4 ≤ T₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hσ : 0 < σ := by linarith
  let p : ℝ := (σ - θ) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  let E : ℝ → ℝ := fun t => 2 * C * ((1 + Real.log t) / t ^ p) + 4 * K * F.card / t
  have hE : Tendsto E atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => (t ^ p)⁻¹) atTop (𝓝 0) := by
      have hh : Tendsto (fun t : ℝ => (t⁻¹) ^ p) atTop (𝓝 0) := by
        simpa only [Real.zero_rpow hp.ne', Function.comp_def] using
          (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp tendsto_inv_atTop_zero
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Real.inv_rpow ht.le p
    have hlog : Tendsto (fun t : ℝ => (1 + Real.log t) / t ^ p) atTop (𝓝 0) := by
      simpa only [add_div, one_div, zero_add] using hpow.add (Sieve.tendsto_log_div_rpow hp)
    have hlast : Tendsto (fun t : ℝ => 4 * K * F.card / t) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (4 * K * F.card)
    simpa only [E, mul_zero, add_zero] using (hlog.const_mul (2 * C)).add hlast
  have hestimate : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → T₀ ≤ s.im →
      ‖gaussianPrimeContinuumGap s (1 / s.im) -
        (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ ≤ E s.im := by
    intro s hsσ hs1 ht₀
    have ht : 4 ≤ s.im := hT₀4.trans ht₀
    have ht0 : 0 < s.im := by linarith
    have htH : H ≤ s.im := (le_max_left _ _).trans ht₀
    have htM : 2 * M + 2 ≤ s.im := ((le_max_right _ _).trans (le_max_right _ _)).trans ht₀
    have hs0 : 0 < s.re := hσ.trans_le hsσ
    have hxi : xi s ≠ 0 := by
      intro hz
      obtain ⟨q, hqs⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
      by_cases hqF : q ∈ F
      · have hm := hM q hqF
        rw [hqs] at hm
        linarith [le_abs_self s.im]
      · have hr := hrest q hqF
        change (q.1 : ℂ).re ≤ θ at hr
        rw [hqs] at hr
        linarith
    let y : ℝ := 1 / s.im
    have hy : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := (div_le_one ht0).mpr (by linarith)
    have hyp : y ≤ y ^ p := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hy hy1 hp1
    have hL : 0 ≤ 1 + Real.log s.im := by
      have := Real.log_nonneg (show 1 ≤ s.im by linarith)
      linarith
    have hfinite : ‖finiteGaussianFinitePartError F s y‖ ≤
        2 * C * ((1 + Real.log s.im) / s.im ^ p) := by
      have hb := hbound y hy hy1 s hsσ hs1 htH
      change ‖finiteGaussianFinitePartError F s y‖ ≤ C * (y + y ^ p) * (1 + Real.log s.im) at hb
      calc
        _ ≤ C * (y + y ^ p) * (1 + Real.log s.im) := hb
        _ ≤ C * (2 * y ^ p) * (1 + Real.log s.im) := by gcongr; linarith
        _ = _ := by
          dsimp [y]
          rw [one_div, Real.inv_rpow ht0.le]
          ring
    have hmodes := norm_finiteGaussianModes_inverseHeight_le hK hk F hM hs0 hs1 hxi
      (by linarith : 1 ≤ s.im) (by linarith : 2 * M ≤ s.im)
    have heq : gaussianPrimeContinuumGap s y -
        (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) =
      finiteGaussianFinitePartError F s y - ∑ q ∈ F, gaussianMBKernel y (xiZero q - s) := by
      rw [finiteGaussianFinitePartError]
      ring
    change ‖gaussianPrimeContinuumGap s y -
      (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ ≤ _
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add hfinite hmodes)
  refine ⟨σ, by linarith, hσ1, ?_, fun ε hε => ?_⟩
  · obtain ⟨q, _, hqσ⟩ := hq
    exact ⟨q, hqσ⟩
  · obtain ⟨T, hT⟩ := eventually_atTop.mp
      ((eventually_ge_atTop T₀).and (hE.eventually (eventually_lt_nhds hε)))
    refine ⟨T, by have h := (hT T le_rfl).1; linarith, fun s hsσ hs1 hts => ?_⟩
    exact (hestimate s hsσ hs1 (hT s.im hts).1).trans_lt (hT s.im hts).2

/-- The literal full von Mangoldt sum has the same high-height passage law.
The continuum and every exceptional Gamma correction have disappeared from
the observable; the strip is supplied by the actual failure of AAL. -/
theorem not_asymptoticAbscissaLaw_has_rawPrime_highGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → T ≤ s.im →
        ‖gaussianDampedPrimeSum s (1 / s.im) -
          (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
  obtain ⟨σ, hσ, hσ1, hq, hgap⟩ :=
    not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage hnot
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun t : ℝ => (1 / t) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto.comp hi
  have hcont : Tendsto (fun t : ℝ => 1 / t + Real.Gamma (3 / 2) * (1 / t) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hi.add (hp.const_mul (Real.Gamma (3 / 2)))
  refine ⟨σ, hσ, hσ1, hq, fun ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨T₁, hT₁, hg⟩ := hgap (ε / 2) hε2
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (hcont.eventually (eventually_lt_nhds hε2)))
  refine ⟨max T₁ T₂, hT₁.trans_le (le_max_left _ _), fun s hsσ hs1 ht => ?_⟩
  have ht₁ : T₁ ≤ s.im := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ s.im := (le_max_right _ _).trans ht
  have hs0 : 0 < s.re := by linarith
  have hE : ‖gaussianIncompleteMellin (1 / s.im) (1 - s)‖ < ε / 2 :=
    (norm_gaussianContinuum_inverseHeight_le hs0 (hT₂ s.im ht₂).1).trans_lt (hT₂ s.im ht₂).2
  have hG := hg s hsσ hs1 ht₁
  have heq : gaussianDampedPrimeSum s (1 / s.im) -
      (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) =
    (gaussianPrimeContinuumGap s (1 / s.im) -
      (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)) +
      gaussianIncompleteMellin (1 / s.im) (1 - s) := by
    rw [gaussianPrimeContinuumGap]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

#print axioms norm_gaussianContinuum_inverseHeight_le
#print axioms not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage
#print axioms not_asymptoticAbscissaLaw_has_rawPrime_highGaussianPassage

end GaloisForLFunctions.EulerFETransportTheory
