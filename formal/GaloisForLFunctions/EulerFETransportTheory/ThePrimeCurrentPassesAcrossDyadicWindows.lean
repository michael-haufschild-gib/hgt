import GaloisForLFunctions.EulerFETransportTheory.OnlyExceptionalGaussianModesRemain
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall

/-!
# Fixed Gaussian damping on escaping height windows

The same damping `1 / T` admits the literal prime current throughout the
window `T ≤ im s ≤ 2T`. In the finite-layer world supplied by failure of AAL,
the full complementary Gamma field, finite exceptional modes, continuum and
scalar correction all vanish uniformly. This matches the observation scale
of the infinite head-conditioned mean-value law.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- One Mellin recursion bounds the continuum whenever height exceeds the
damping horizon. -/
theorem norm_gaussianContinuum_horizon_le {s : ℂ} {H : ℝ}
    (hs : 0 < s.re) (hH : 1 ≤ H) (ht : H ≤ s.im) :
    ‖gaussianIncompleteMellin (1 / H) (1 - s)‖ ≤
      1 / H + Real.Gamma (3 / 2) * (1 / H) ^ (1 / 2 : ℝ) := by
  let y : ℝ := 1 / H
  have ht0 : 0 < H := by linarith
  have hsIm : 0 < s.im := ht0.trans_le ht
  have hy : 0 < y := by dsimp [y]; positivity
  have hnorm : H ≤ ‖1 - s‖ := by
    apply ht.trans
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, abs_of_pos hsIm] using
      Complex.abs_im_le_norm (1 - s)
  have ha : (1 : ℂ) - s ≠ 0 := norm_pos_iff.mp (ht0.trans_le hnorm)
  have hE := norm_gaussianIncompleteMellin_le hy (r := 2) (by norm_num)
    (b := 1 - s + 2) (by simp; linarith)
  norm_num only at hE
  have he : ‖-(Real.exp (-y) : ℂ) / (1 - s)‖ ≤ 1 / H := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 / ‖1 - s‖ := div_le_div_of_nonneg_right
        (Real.exp_le_one_iff.mpr (by linarith)) (norm_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le ht0 hnorm
  have htail : ‖(2 * (y : ℂ) / (1 - s)) * gaussianIncompleteMellin y (1 - s + 2)‖ ≤
      (2 * y / H) * (y ^ (-(3 : ℝ) / 2) * (1 / 2) * Real.Gamma (3 / 2)) := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy]
    exact mul_le_mul (div_le_div_of_nonneg_left (by positivity) ht0 hnorm)
      (by simpa only [neg_div] using hE) (norm_nonneg _) (by positivity)
  have hpow : y ^ 2 * y ^ (-(3 : ℝ) / 2) = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 1
    norm_num
  have htailval : (2 * y / H) *
      (y ^ (-(3 : ℝ) / 2) * (1 / 2) * Real.Gamma (3 / 2)) =
        Real.Gamma (3 / 2) * y ^ (1 / 2 : ℝ) := by
    calc
      _ = Real.Gamma (3 / 2) * (y ^ 2 * y ^ (-(3 : ℝ) / 2)) := by dsimp [y]; ring
      _ = _ := by rw [hpow]
  change ‖gaussianIncompleteMellin y (1 - s)‖ ≤ _
  rw [gaussianIncompleteMellin_recursion hy ha]
  exact (norm_add_le _ _).trans (add_le_add he (htail.trans_eq htailval))

private theorem norm_finiteGaussianModes_horizon_le {K M : ℝ}
    (hK : 0 < K)
    (hk : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 → xi s ≠ 0 → ∀ q : XiZeroCopy,
      ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤ K * ‖(xiZero q - s)⁻¹‖ ^ 2)
    (F : Finset XiZeroCopy) (hM : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ M)
    {s : ℂ} {H : ℝ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hxi : xi s ≠ 0)
    (ht : 1 ≤ H) (htH : H ≤ s.im) (htM : 2 * M ≤ H) :
    ‖∑ q ∈ F, gaussianMBKernel (1 / H) (xiZero q - s)‖ ≤
      4 * K * F.card / H := by
  have ht0 : 0 < H := by linarith
  let y : ℝ := 1 / H
  have hy : 0 < y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := (div_le_one ht0).mpr ht
  have hterm : ∀ q ∈ F, ‖gaussianMBKernel y (xiZero q - s)‖ ≤ 4 * K / H := by
    intro q hq
    have hnorm : H / 2 ≤ ‖xiZero q - s‖ := by
      have him : H / 2 ≤ s.im - (q.1 : ℂ).im := by
        linarith [hM q hq, le_abs_self (q.1 : ℂ).im]
      have h := Complex.im_le_norm (s - (q.1 : ℂ))
      rw [Complex.sub_im, norm_sub_rev] at h
      exact him.trans h
    have hi : ‖(xiZero q - s)⁻¹‖ ≤ 2 / H := by
      rw [norm_inv]
      calc
        _ ≤ (H / 2)⁻¹ := inv_anti₀ (by positivity) hnorm
        _ = _ := by field_simp
    have hunit : ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤ K * (2 / H) ^ 2 := by
      refine (hk s hs0 hs1 hxi q).trans ?_
      apply mul_le_mul_of_nonneg_left _ hK.le
      nlinarith [norm_nonneg ((xiZero q - s)⁻¹)]
    have hp : y ^ (-((xiZero q - s) / 2)).re ≤ H := by
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
      _ ≤ (K * (2 / H) ^ 2) * H := mul_le_mul hunit hp (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ q ∈ F, ‖gaussianMBKernel y (xiZero q - s)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ F, 4 * K / H := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Failure of AAL supplies an interior strip on which a single damping
scale recovers the continued finite part across each escaping dyadic window. -/
theorem not_asymptoticAbscissaLaw_has_countertermFree_dyadicGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ L : ℝ, T ≤ L → ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → L ≤ s.im → s.im ≤ 2 * L →
        ‖gaussianPrimeContinuumGap s (1 / L) -
          (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
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
  let E : ℝ → ℝ := fun t => 2 * C * ((1 + Real.log (2 * t)) / t ^ p) + 4 * K * F.card / t
  have hE : Tendsto E atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => (t ^ p)⁻¹) atTop (𝓝 0) := by
      have hh : Tendsto (fun t : ℝ => (t⁻¹) ^ p) atTop (𝓝 0) := by
        simpa only [Real.zero_rpow hp.ne', Function.comp_def] using
          (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp tendsto_inv_atTop_zero
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Real.inv_rpow ht.le p
    have hlog : Tendsto (fun t : ℝ => (1 + Real.log (2 * t)) / t ^ p) atTop (𝓝 0) := by
      have hbase := (hpow.const_mul (1 + Real.log 2)).add (Sieve.tendsto_log_div_rpow hp)
      simp only [mul_zero, zero_add] at hbase
      refine hbase.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
      ring
    have hlast : Tendsto (fun t : ℝ => 4 * K * F.card / t) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (4 * K * F.card)
    simpa only [E, mul_zero, add_zero] using (hlog.const_mul (2 * C)).add hlast
  have hestimate : ∀ L : ℝ, T₀ ≤ L → ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → L ≤ s.im → s.im ≤ 2 * L →
      ‖gaussianPrimeContinuumGap s (1 / L) -
        (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ ≤ E L := by
    intro L hL₀ s hsσ hs1 hLs hsL
    have ht₀ : T₀ ≤ s.im := hL₀.trans hLs
    have hL4 : 4 ≤ L := hT₀4.trans hL₀
    have hL0 : 0 < L := by linarith
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
    let y : ℝ := 1 / L
    have hy : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := (div_le_one hL0).mpr (by linarith)
    have hyp : y ≤ y ^ p := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hy hy1 hp1
    have hL : 0 ≤ 1 + Real.log s.im := by
      have := Real.log_nonneg (show 1 ≤ s.im by linarith)
      linarith
    have hfinite : ‖finiteGaussianFinitePartError F s y‖ ≤
        2 * C * ((1 + Real.log (2 * L)) / L ^ p) := by
      have hb := hbound y hy hy1 s hsσ hs1 htH
      change ‖finiteGaussianFinitePartError F s y‖ ≤ C * (y + y ^ p) * (1 + Real.log s.im) at hb
      calc
        _ ≤ C * (y + y ^ p) * (1 + Real.log s.im) := hb
        _ ≤ C * (2 * y ^ p) * (1 + Real.log (2 * L)) := by
          apply mul_le_mul
          · gcongr; linarith
          · exact add_le_add_right (Real.log_le_log ht0 hsL) 1
          · exact hL
          · positivity
        _ = _ := by
          dsimp [y]
          rw [one_div, Real.inv_rpow hL0.le]
          ring
    have hmodes := norm_finiteGaussianModes_horizon_le hK hk F hM hs0 hs1 hxi
      (by linarith : 1 ≤ L) hLs (by
        have h := ((le_max_right _ _).trans (le_max_right _ _)).trans hL₀
        linarith : 2 * M ≤ L)
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
    refine ⟨T, by have h := (hT T le_rfl).1; linarith, fun L hTL s hsσ hs1 hLs hsL => ?_⟩
    exact (hestimate L (hT L hTL).1 s hsσ hs1 hLs hsL).trans_lt (hT L hTL).2

/-- The literal full von Mangoldt sum has the same high-height passage law.
The continuum and every exceptional Gamma correction have disappeared from
the observable; the strip is supplied by the actual failure of AAL. -/
theorem not_asymptoticAbscissaLaw_has_rawPrime_dyadicGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ L : ℝ, T ≤ L → ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → L ≤ s.im → s.im ≤ 2 * L →
        ‖gaussianDampedPrimeSum s (1 / L) -
          (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
  obtain ⟨σ, hσ, hσ1, hq, hgap⟩ :=
    not_asymptoticAbscissaLaw_has_countertermFree_dyadicGaussianPassage hnot
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
  refine ⟨max T₁ T₂, hT₁.trans_le (le_max_left _ _), fun L ht s hsσ hs1 hLs hsL => ?_⟩
  have ht₁ : T₁ ≤ L := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ L := (le_max_right _ _).trans ht
  have hs0 : 0 < s.re := by linarith
  have hE : ‖gaussianIncompleteMellin (1 / L) (1 - s)‖ < ε / 2 :=
    (norm_gaussianContinuum_horizon_le hs0 (hT₂ L ht₂).1 hLs).trans_lt (hT₂ L ht₂).2
  have hG := hg L ht₁ s hsσ hs1 hLs hsL
  have heq : gaussianDampedPrimeSum s (1 / L) -
      (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) =
    (gaussianPrimeContinuumGap s (1 / L) -
      (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)) +
      gaussianIncompleteMellin (1 / L) (1 - s) := by
    rw [gaussianPrimeContinuumGap]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Scalar and polar corrections with an independent damping horizon. -/
theorem norm_normalizedGaussianFinitePart_horizon_add_logDeriv_le {s : ℂ} {δ H : ℝ}
    (hH : 0 < H) (htH : H ≤ s.im) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (ht : 4 ≤ s.im)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖) :
    ‖(Real.exp (-(1 / H)) : ℂ) *
        (gaussianArchimedeanCurrent s - logDeriv xi s) + logDeriv riemannZeta s‖ ≤
      (logDerivZetaConstant / δ) * (Real.log s.im / H) + 1 / H := by
  have hs0 : 0 < s.re := by linarith
  have ht0 : 0 < s.im := by linarith
  have hsne0 : s ≠ 0 := by intro h; simp [h] at hs0
  have hsne1 : s ≠ 1 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.one_im] at hh
    linarith
  have hxi := xi_ne_zero_of_separated hδ hsep
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    apply hxi
    rw [xi_eq_xiUnit_mul_zeta hsne0 hsne1 hs0, hz, mul_zero]
  have hdec : gaussianArchimedeanCurrent s - logDeriv xi s =
      -logDeriv riemannZeta s - (s - 1)⁻¹ := by
    rw [logDeriv_zeta_eq_logDeriv_xi hs0 hsne1 hζ, gaussianArchimedeanCurrent]
    ring
  have hL : ‖logDeriv riemannZeta s‖ ≤ logDerivZetaConstant * Real.log s.im / δ := by
    have hh := norm_logDeriv_zeta_le hs (by linarith : s.re ≤ 2) ht hδ hδ1
      (fun q => by simpa only [Complex.re_add_im, norm_sub_rev, xiZero] using hsep q)
    simpa only [Complex.re_add_im] using hh
  let y : ℝ := 1 / H
  have hy : 0 < y := by dsimp [y]; positivity
  have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hscalar : ‖(1 : ℂ) - (Real.exp (-y) : ℂ)‖ ≤ y := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he1)]
    linarith [Real.add_one_le_exp (-y)]
  have hexp : ‖(Real.exp (-y) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he1
  have hinv : ‖(s - 1)⁻¹‖ ≤ 1 / H := by
    rw [norm_inv, one_div]
    apply inv_anti₀ hH
    apply htH.trans
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.im_le_norm (s - 1)
  have heq : (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) +
      logDeriv riemannZeta s =
      (1 - (Real.exp (-y) : ℂ)) * logDeriv riemannZeta s -
        (Real.exp (-y) : ℂ) * (s - 1)⁻¹ := by rw [hdec]; ring
  change ‖(Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) +
    logDeriv riemannZeta s‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(1 - (Real.exp (-y) : ℂ)) * logDeriv riemannZeta s‖ +
        ‖(Real.exp (-y) : ℂ) * (s - 1)⁻¹‖ := norm_sub_le _ _
    _ ≤ y * (logDerivZetaConstant * Real.log s.im / δ) + 1 * (1 / H) := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul hscalar hL (norm_nonneg _) hy.le)
        (mul_le_mul hexp hinv (norm_nonneg _) zero_le_one)
    _ = _ := by dsimp [y]; ring

/-- In the actual finite-layer world, damping `1/L` recovers `-ζ'/ζ` uniformly
for `L ≤ im s ≤ 2L` on an interior strip. No counterterm remains. -/
theorem not_asymptoticAbscissaLaw_has_rawEuler_dyadicGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ L : ℝ, T ≤ L → ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → L ≤ s.im → s.im ≤ 2 * L →
        ‖gaussianDampedPrimeSum s (1 / L) + logDeriv riemannZeta s‖ < ε := by
  classical
  obtain ⟨σ₁, hσ₁, hσ₁1, hq₁, hraw⟩ :=
    not_asymptoticAbscissaLaw_has_rawPrime_dyadicGaussianPassage hnot
  obtain ⟨F, θ, σ₂, _, _, hθ, hgap, hσ₂1, _, _, hq₂, hrest, _, _⟩ :=
    not_asymptoticAbscissaLaw_has_finiteGaussianControl hnot
  let σ : ℝ := max σ₁ σ₂
  let δ : ℝ := min (σ₂ - θ) 1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hgap) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let M : ℝ := ∑ q ∈ F, |(q.1 : ℂ).im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hM : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ M := fun q hq =>
    Finset.single_le_sum (fun p _ => abs_nonneg (p.1 : ℂ).im) hq
  let H : ℝ := M + δ + 4
  have hdomain : ∀ s : ℂ, σ ≤ s.re → H ≤ s.im →
      4 ≤ s.im ∧ ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖ := by
    intro s hs ht
    have hs₂ : σ₂ ≤ s.re := (le_max_right _ _).trans hs
    have ht4 : 4 ≤ s.im := by dsimp [H] at ht; linarith
    refine ⟨ht4, fun q => ?_⟩
    by_cases hq : q ∈ F
    · have him : δ ≤ s.im - (q.1 : ℂ).im := by
        have hm := hM q hq
        dsimp [H] at ht
        linarith [le_abs_self (q.1 : ℂ).im]
      have hn := Complex.im_le_norm (s - (q.1 : ℂ))
      rw [Complex.sub_im, norm_sub_rev] at hn
      exact him.trans hn
    · have hre : δ ≤ s.re - (q.1 : ℂ).re := by
        have hr := hrest q hq
        have hd : δ ≤ σ₂ - θ := min_le_left _ _
        change (q.1 : ℂ).re ≤ θ at hr
        linarith
      have hn := Complex.re_le_norm (s - (q.1 : ℂ))
      rw [Complex.sub_re, norm_sub_rev] at hn
      exact hre.trans hn
  have hlim : Tendsto (fun t : ℝ =>
      (logDerivZetaConstant / δ) * (Real.log (2 * t) / t) + 1 / t) atTop (𝓝 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log (2 * t) / t) atTop (𝓝 0) := by
      have hlog := Sieve.tendsto_log_div_rpow (δ := 1) zero_lt_one
      simp only [Real.rpow_one] at hlog
      have hi := tendsto_inv_atTop_zero.const_mul (Real.log 2)
      have hh := hi.add hlog
      simp only [mul_zero, zero_add] at hh
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
      ring
    simpa only [one_div, mul_zero, add_zero] using
      (hlog.const_mul (logDerivZetaConstant / δ)).add tendsto_inv_atTop_zero
  have hσ : 1 / 2 < σ := hσ₁.trans_le (le_max_left _ _)
  refine ⟨σ, hσ, max_lt hσ₁1 hσ₂1, ?_, fun ε hε => ?_⟩
  · rcases le_total σ₁ σ₂ with h | h
    · obtain ⟨q, _, hq⟩ := hq₂
      exact ⟨q, by simpa only [σ, max_eq_right h] using hq⟩
    · obtain ⟨q, hq⟩ := hq₁
      exact ⟨q, by simpa only [σ, max_eq_left h] using hq⟩
  · have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨T₁, hT₁, hr⟩ := hraw (ε / 2) hε2
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
      ((eventually_ge_atTop H).and (hlim.eventually (eventually_lt_nhds hε2)))
    refine ⟨max T₁ T₂, hT₁.trans_le (le_max_left _ _), fun L ht s hs hs1 hLs hsL => ?_⟩
    have ht₁ : T₁ ≤ L := (le_max_left _ _).trans ht
    have ht₂ : T₂ ≤ L := (le_max_right _ _).trans ht
    have hd := hdomain s hs ((hT₂ L ht₂).1.trans hLs)
    have hL0 : 0 < L := hT₁.trans_le ht₁
    have hb := norm_normalizedGaussianFinitePart_horizon_add_logDeriv_le hL0 hLs
      (hσ.le.trans hs) hs1 hd.1 hδ hδ1 hd.2
    have hc : ‖(Real.exp (-(1 / L)) : ℂ) *
        (gaussianArchimedeanCurrent s - logDeriv xi s) + logDeriv riemannZeta s‖ < ε / 2 := by
      refine (hb.trans ?_).trans_lt (hT₂ L ht₂).2
      have hC0 : 0 ≤ logDerivZetaConstant := by
        unfold logDerivZetaConstant
        positivity
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (Real.log_le_log (by linarith only [hd.1]) hsL) hL0.le)
          (div_nonneg hC0 hδ.le)) (1 / L)
    have hp := hr L ht₁ s ((le_max_left _ _).trans hs) hs1 hLs hsL
    have heq : gaussianDampedPrimeSum s (1 / L) + logDeriv riemannZeta s =
        (gaussianDampedPrimeSum s (1 / L) -
          (Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)) +
        ((Real.exp (-(1 / L)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) +
          logDeriv riemannZeta s) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith)

#print axioms norm_gaussianContinuum_horizon_le
#print axioms not_asymptoticAbscissaLaw_has_countertermFree_dyadicGaussianPassage
#print axioms not_asymptoticAbscissaLaw_has_rawPrime_dyadicGaussianPassage
#print axioms norm_normalizedGaussianFinitePart_horizon_add_logDeriv_le
#print axioms not_asymptoticAbscissaLaw_has_rawEuler_dyadicGaussianPassage

end GaloisForLFunctions.EulerFETransportTheory
