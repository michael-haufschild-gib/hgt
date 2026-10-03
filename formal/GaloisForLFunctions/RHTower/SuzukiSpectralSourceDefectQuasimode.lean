import GaloisForLFunctions.RHTower.SuzukiSpectralSourceDefect
import GaloisForLFunctions.RHTower.SuzukiSpectralMarginNecessity

open Complex Filter Set
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private def freeGram (a : SuzukiPositiveAperture) (s t : ℝ) : ℂ :=
  (Real.exp (-(1+s)*a.1) : ℂ) *
    inner ℂ (ccmPolarApertureVector a t) (ccmPolarApertureVector a 1)

private theorem freeGram_tendsto (s : Ioo (1/2 : ℝ) 1) :
    Tendsto (fun a : SuzukiPositiveAperture => freeGram a s.1 s.1)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop)
      (𝓝 ((1/(1+s.1) : ℝ) : ℂ)) ∧
    Tendsto (fun a : SuzukiPositiveAperture => freeGram a s.1 (-s.1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  obtain ⟨hp, hm⟩ := tendsto_suzukiTaV2_scaled_mixed_source_pairings s
  obtain ⟨hep, hem⟩ := tendsto_suzukiTaV2_scaled_mixed_source_errors s.1 s.2.1.le
  constructor
  · simpa only [sub_zero, sub_sub_cancel, freeGram] using hp.sub hep
  · simpa only [sub_self, sub_sub_cancel, freeGram] using hm.sub hem

private theorem mixed_error_bound (b : SuzukiSpectralMarginParameters) (s : ℝ)
    (v : suzukiApertureHilbert b.1) (hv : ‖v‖ ≤ Real.exp (s*b.1.1)) :
    ‖(suzukiSpectralMarginMixedScale b s : ℂ) * inner ℂ v (suzukiSpectralMarginPhysical b.1 b.2) -
        (Real.exp (-(1+s)*b.1.1) : ℂ) * inner ℂ v (ccmPolarApertureVector b.1 1)‖ ≤
      Real.exp (-b.1.1) * ‖suzukiSpectralSourceDefect b‖ := by
  let r := Real.exp (-(1+s)*b.1.1)
  let d := suzukiSpectralMarginShift b.1 b.2
  let f := suzukiSpectralMarginPhysical b.1 b.2
  let p := ccmPolarApertureVector b.1 1
  let e := suzukiApertureL2Equiv b.1
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have heq : (suzukiSpectralMarginMixedScale b s : ℂ) * inner ℂ v f -
      (r : ℂ) * inner ℂ v p =
      (r : ℂ) * inner ℂ v (e (suzukiSpectralSourceDefect b)) := by
    have hphysical : e (suzukiSpectralSourceDefect b) = (d : ℂ) • f - p :=
      suzukiSpectralSourceDefect_physical b
    rw [hphysical, inner_sub_right, inner_smul_right v f (d : ℂ)]
    change (((d*r : ℝ) : ℂ) * _) - _ = _
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  calc
    _ ≤ r * (‖v‖ * ‖e (suzukiSpectralSourceDefect b)‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm v (e (suzukiSpectralSourceDefect b))) hr
    _ = r * (‖v‖ * ‖suzukiSpectralSourceDefect b‖) := by rw [e.norm_map]
    _ ≤ r * (Real.exp (s*b.1.1) * ‖suzukiSpectralSourceDefect b‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) hr
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add,
        show -(1+s)*b.1.1+s*b.1.1 = -b.1.1 by ring]

/-- Both complex mixed-source errors are controlled by the actual amplified
interval defect, on its natural exponential source scale. -/
theorem suzukiSpectralSourceDefect_mixed_error_bound
    (b : SuzukiSpectralMarginParameters) (s : ℝ) (hs : 1/2 ≤ s) :
    ‖(suzukiSpectralMarginMixedScale b s : ℂ) * suzukiSpectralMarginMixedPairing b s -
        (Real.exp (-(1+s)*b.1.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector b.1 s) (ccmPolarApertureVector b.1 1)‖ ≤
      Real.exp (-b.1.1) * ‖suzukiSpectralSourceDefect b‖ ∧
    ‖(suzukiSpectralMarginMixedScale b s : ℂ) * suzukiSpectralMarginMixedPairing b (-s) -
        (Real.exp (-(1+s)*b.1.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector b.1 (-s)) (ccmPolarApertureVector b.1 1)‖ ≤
      Real.exp (-b.1.1) * ‖suzukiSpectralSourceDefect b‖ := by
  exact ⟨mixed_error_bound b s _ (norm_ccmPolarApertureVector_le_exp_of_half_le b.1 s hs),
    mixed_error_bound b s _ (norm_ccmPolarApertureVector_neg_le_exp_of_half_le b.1 s hs)⟩

/-- A nonzero carrier limit forces a genuinely amplified actual source defect.
The lower scale is derived from the carrier equation, not assumed. -/
theorem suzukiSpectralSourceDefect_nonzero_limit_amplification
    (b : ℕ → SuzukiSpectralMarginParameters)
    (hb : Tendsto (fun n => (b n).1.1) atTop atTop)
    (s : Ioo (1/2 : ℝ) 1) (L : ℂ) (hL : L ≠ 0)
    (hconv : Tendsto (fun n => suzukiSpectralMarginLivsic (b n) (I*(s.1 : ℂ)))
      atTop (𝓝 L)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
      η ≤ Real.exp (-(b n).1.1) * ‖suzukiSpectralSourceDefect (b n)‖ := by
  let B := fun n => suzukiSpectralMarginLivsic (b n) (I*(s.1 : ℂ))
  let P := fun n => (suzukiSpectralMarginMixedScale (b n) s.1 : ℂ) *
    suzukiSpectralMarginMixedPairing (b n) s.1
  let M := fun n => (suzukiSpectralMarginMixedScale (b n) s.1 : ℂ) *
    suzukiSpectralMarginMixedPairing (b n) (-s.1)
  let Gp := fun n => freeGram (b n).1 s.1 s.1
  let Gm := fun n => freeGram (b n).1 s.1 (-s.1)
  let Y := fun n => Real.exp (-(b n).1.1) * ‖suzukiSpectralSourceDefect (b n)‖
  let k := (I*(s.1 : ℂ)-I)/(I*(s.1 : ℂ)+I)
  let g : ℂ := ((1/(1+s.1) : ℝ) : ℂ)
  have hg : g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero one_ne_zero (by linarith [s.2.1]))
  have hLg : 0 < ‖L*g‖ := norm_pos_iff.mpr (mul_ne_zero hL hg)
  have hf : Tendsto (fun n => (b n).1) atTop
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) := tendsto_comap_iff.2 hb
  obtain ⟨hp, hm⟩ := freeGram_tendsto s
  have hgp : Tendsto Gp atTop (𝓝 g) := hp.comp hf
  have hgm : Tendsto Gm atTop (𝓝 0) := hm.comp hf
  have hn : ∀ᶠ n in atTop, B n ≠ 0 := hconv.eventually_ne hL
  have hbound : ∀ᶠ n in atTop,
      ‖B n * Gp n - k * Gm n‖ ≤ (‖B n‖ + ‖k‖) * Y n := by
    filter_upwards [hn] with n hn
    obtain ⟨hep, hem⟩ := suzukiSpectralSourceDefect_mixed_error_bound (b n) s.1 s.2.1.le
    change ‖P n - Gp n‖ ≤ Y n at hep
    change ‖M n - Gm n‖ ≤ Y n at hem
    have hd : suzukiSpectralMarginMixedPairing (b n) s.1 ≠ 0 := by
      intro hd
      apply hn
      simp [B, suzukiSpectralMarginLivsic_imaginary, hd]
    have hcancel : B n * P n = k * M n := by
      rw [show B n = k * (suzukiSpectralMarginMixedPairing (b n) (-s.1) /
        suzukiSpectralMarginMixedPairing (b n) s.1) from
          suzukiSpectralMarginLivsic_imaginary (b n) s.1]
      dsimp only [P, M]
      field_simp
    have hid : B n * Gp n - k * Gm n =
        k * (M n - Gm n) - B n * (P n - Gp n) := by
      rw [mul_sub, mul_sub, ← hcancel]
      ring
    rw [hid]
    calc
      _ ≤ ‖k * (M n - Gm n)‖ + ‖B n * (P n - Gp n)‖ := norm_sub_le _ _
      _ = ‖k‖ * ‖M n - Gm n‖ + ‖B n‖ * ‖P n - Gp n‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖k‖ * Y n + ‖B n‖ * Y n := add_le_add
        (mul_le_mul_of_nonneg_left hem (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hep (norm_nonneg _))
      _ = _ := by ring
  have hlim : Tendsto (fun n => ‖B n * Gp n - k * Gm n‖) atTop (𝓝 ‖L*g‖) := by
    simpa only [mul_zero, sub_zero] using ((hconv.mul hgp).sub (hgm.const_mul k)).norm
  have ha : ∀ᶠ n in atTop, ‖L*g‖/2 < ‖B n * Gp n - k * Gm n‖ :=
    hlim.eventually (Ioi_mem_nhds (by linarith))
  have hB : ∀ᶠ n in atTop, ‖B n‖ < ‖L‖ + 1 :=
    hconv.norm.eventually (Iio_mem_nhds (by linarith))
  let β := ‖L‖ + 1 + ‖k‖
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨(‖L*g‖/2)/β, div_pos (by linarith) hβ, ?_⟩
  filter_upwards [ha, hB, hbound] with n ha hB hbound
  have hY : 0 ≤ Y n := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hcoef : ‖B n‖ + ‖k‖ ≤ β := by dsimp [β]; linarith
  have hab := hbound.trans (mul_le_mul_of_nonneg_right hcoef hY)
  apply (div_le_iff₀ hβ).2
  nlinarith

/-- The actual amplified source defect becomes a relative covariance
quasimode. No ground projection, spectral gap or overlap premise is supplied. -/
theorem suzukiSpectralSourceDefect_nonzero_limit_quasimode
    (b : ℕ → SuzukiSpectralMarginParameters)
    (hb : Tendsto (fun n => (b n).1.1) atTop atTop)
    (s : Ioo (1/2 : ℝ) 1) (L : ℂ) (hL : L ≠ 0)
    (hconv : Tendsto (fun n => suzukiSpectralMarginLivsic (b n) (I*(s.1 : ℂ)))
      atTop (𝓝 L)) :
    (∀ᶠ n in atTop, suzukiSpectralSourceDefect (b n) ≠ 0) ∧
    Tendsto (fun n =>
      ‖suzukiSpectralSourceDefect (b n) - suzukiSpectralNormalizedCovariance (b n).1
          (suzukiSpectralSourceDefect (b n))‖ / ‖suzukiSpectralSourceDefect (b n)‖)
      atTop (𝓝 0) := by
  obtain ⟨η, hη, hsize⟩ :=
    suzukiSpectralSourceDefect_nonzero_limit_amplification b hb s L hL hconv
  have hy : ∀ᶠ n in atTop, 0 < ‖suzukiSpectralSourceDefect (b n)‖ := by
    filter_upwards [hsize] with n hn
    have he := Real.exp_pos (-(b n).1.1)
    have hn0 := norm_nonneg (suzukiSpectralSourceDefect (b n))
    nlinarith
  have hbase : Tendsto (fun n =>
      Real.exp (-(b n).1.1) * ‖suzukiSpectralBaseDefect (b n).1‖ / η) atTop (𝓝 0) := by
    have hf : Tendsto (fun n => (b n).1) atTop
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) := tendsto_comap_iff.2 hb
    simpa only [Function.comp_def, zero_div] using
      (tendsto_suzukiSpectralBaseDefect_scaled_norm.comp hf).div_const η
  have hratio : Tendsto (fun n =>
      ‖suzukiSpectralBaseDefect (b n).1‖ / ‖suzukiSpectralSourceDefect (b n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ hbase
    filter_upwards [hsize, hy] with n hn hy
    apply (div_le_div_iff₀ hy hη).2
    calc
      _ ≤ ‖suzukiSpectralBaseDefect (b n).1‖ *
          (Real.exp (-(b n).1.1) * ‖suzukiSpectralSourceDefect (b n)‖) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring
  have hm := suzukiSpectralMargin_nonzero_limit_forces_margin_zero b hb s L hL hconv
  refine ⟨hy.mono fun n hn => norm_pos_iff.mp hn, ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    (by simpa only [add_zero] using hratio.add hm)
  filter_upwards [hy] with n hn
  calc
    _ ≤ (‖suzukiSpectralBaseDefect (b n).1‖ +
          (b n).2.1 * ‖suzukiSpectralSourceDefect (b n)‖) /
          ‖suzukiSpectralSourceDefect (b n)‖ :=
      div_le_div_of_nonneg_right (norm_suzukiSpectralSourceDefect_topResidual_le (b n)) hn.le
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hn.ne']

/-- Any fixed-source Xi identification must realize this actual source
quasimode, rather than merely supplying an abstract bottom eigenspace. -/
theorem suzukiSpectralSourceDefect_xi_limit_forces_quasimode :
    ∀ b : ℕ → SuzukiSpectralMarginParameters,
      Tendsto (fun n => (b n).1.1) atTop atTop →
      TendstoLocallyUniformlyOn (fun n => suzukiSpectralMarginLivsic (b n))
        xiHedenmalmLivsicTarget atTop {z : ℂ | 0 < z.im} →
      (∀ᶠ n in atTop, suzukiSpectralSourceDefect (b n) ≠ 0) ∧
      Tendsto (fun n =>
        ‖suzukiSpectralSourceDefect (b n) - suzukiSpectralNormalizedCovariance (b n).1
            (suzukiSpectralSourceDefect (b n))‖ / ‖suzukiSpectralSourceDefect (b n)‖)
        atTop (𝓝 0) := by
  intro b hb hconv
  obtain ⟨s, hs⟩ := exists_xi_target_imaginary_ne_zero
  exact suzukiSpectralSourceDefect_nonzero_limit_quasimode b hb s _ hs
    (hconv.tendsto_at (by
      change 0 < (I*(s.1 : ℂ)).im
      simpa using (show 0 < s.1 by linarith [s.2.1])))

end RHTower
end
