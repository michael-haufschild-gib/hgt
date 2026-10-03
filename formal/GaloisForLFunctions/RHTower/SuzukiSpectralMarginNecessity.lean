import GaloisForLFunctions.RHTower.SuzukiSpectralMarginLimit
import GaloisForLFunctions.RHTower.SuzukiRaisedMetricShiftCarrier

open Complex Filter Set
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Literal Fourier carrier of the actual source response at every shift
strictly above the actual spectral floor. -/
def suzukiSpectralMarginLivsic (b : SuzukiSpectralMarginParameters) (z : ℂ) : ℂ :=
  ((z-I)/(z+I)) *
    (suzukiTaPhysicalFourier b.1 (suzukiSpectralMarginRawDeficiency b.1 b.2) z /
      suzukiTaPhysicalFourier b.1 (suzukiSpectralMarginRawDeficiency b.1 b.2) (-z))

theorem suzukiSpectralMarginLivsic_imaginary
    (b : SuzukiSpectralMarginParameters) (s : ℝ) :
    suzukiSpectralMarginLivsic b (I*(s : ℂ)) =
      ((I*(s : ℂ)-I)/(I*(s : ℂ)+I)) *
        (suzukiSpectralMarginMixedPairing b (-s) / suzukiSpectralMarginMixedPairing b s) := by
  rw [suzukiSpectralMarginLivsic,
    show -(I*(s : ℂ)) = I*((-s : ℝ) : ℂ) by push_cast; ring,
    suzukiTaPhysicalFourier_imaginary_eq_polar_pairing,
    suzukiTaPhysicalFourier_imaginary_eq_polar_pairing, neg_neg]
  rfl

/-- Any nonzero carrier limit on the interior imaginary segment forces
approach to the actual floor in relative scale. This covers every strictly
admissible shift, without source-overlap or ground-parity assumptions. -/
theorem suzukiSpectralMargin_nonzero_limit_forces_margin_zero
    (b : ℕ → SuzukiSpectralMarginParameters)
    (hb : Tendsto (fun n => (b n).1.1) atTop atTop)
    (s : Ioo (1/2 : ℝ) 1) (L : ℂ) (hL : L ≠ 0)
    (hconv : Tendsto (fun n => suzukiSpectralMarginLivsic (b n) (I*(s.1 : ℂ)))
      atTop (𝓝 L)) : Tendsto (fun n => (b n).2.1) atTop (𝓝 0) := by
  let q := fun n => suzukiSpectralMarginWeight (b n).2
  let P := fun n => (suzukiSpectralMarginMixedScale (b n) s.1 : ℂ) *
    suzukiSpectralMarginMixedPairing (b n) s.1
  let M := fun n => (suzukiSpectralMarginMixedScale (b n) s.1 : ℂ) *
    suzukiSpectralMarginMixedPairing (b n) (-s.1)
  let B := fun n => suzukiSpectralMarginLivsic (b n) (I*(s.1 : ℂ))
  let k := (I*(s.1 : ℂ)-I)/(I*(s.1 : ℂ)+I)
  let g : ℂ := ((1/(1+s.1) : ℝ) : ℂ)
  have hg : g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero one_ne_zero (by linarith [s.2.1]))
  obtain ⟨hep, hem⟩ := tendsto_suzukiSpectralMargin_weighted_mixed_pairings s
  have hf : Tendsto b atTop
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) :=
    tendsto_comap_iff.2 hb
  have hp : Tendsto (fun n => (q n : ℂ) * (P n - g)) atTop (𝓝 0) := hep.comp hf
  have hm : Tendsto (fun n => (q n : ℂ) * M n) atTop (𝓝 0) := hem.comp hf
  have hn : ∀ᶠ n in atTop, B n ≠ 0 := hconv.eventually_ne hL
  have heq : ∀ᶠ n in atTop,
      (k * ((q n : ℂ) * M n)) / B n = (q n : ℂ) * P n := by
    filter_upwards [hn] with n hn
    have hd : suzukiSpectralMarginMixedPairing (b n) s.1 ≠ 0 := by
      intro hd
      apply hn
      simp [B, suzukiSpectralMarginLivsic_imaginary, hd]
    apply (div_eq_iff hn).2
    rw [show B n = k * (suzukiSpectralMarginMixedPairing (b n) (-s.1) /
      suzukiSpectralMarginMixedPairing (b n) s.1) from
        suzukiSpectralMarginLivsic_imaginary (b n) s.1]
    dsimp only [P, M]
    field_simp
  have hP : Tendsto (fun n => (q n : ℂ) * P n) atTop (𝓝 0) := by
    have h := ((hm.const_mul k).div hconv hL).congr' heq
    simpa only [mul_zero, zero_div] using h
  have hqg : Tendsto (fun n => (q n : ℂ) * g) atTop (𝓝 0) := by
    have h := hP.sub hp
    simpa only [mul_sub, sub_sub_cancel, sub_self] using h
  have hqc : Tendsto (fun n => (q n : ℂ)) atTop (𝓝 0) := by
    simpa only [mul_div_cancel_right₀ _ hg, zero_div] using hqg.div_const g
  have hq : Tendsto q atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using
      (Complex.continuous_re.tendsto (0 : ℂ)).comp hqc
  have hsmall : ∀ᶠ n in atTop, q n < 1 := hq.eventually (Iio_mem_nhds zero_lt_one)
  apply hq.congr'
  filter_upwards [hsmall] with n hn
  change min 1 (b n).2.1 = (b n).2.1
  rcases le_total 1 (b n).2.1 with hm | hm
  · have : q n = 1 := min_eq_left hm
    linarith
  · exact min_eq_right hm

/-- Xi identification itself requires relative spectral-floor approach.
No bounded-shift, simplicity, parity or source-overlap premise is present. -/
theorem suzukiSpectralMargin_xi_limit_forces_relative_floor :
    ∀ b : ℕ → SuzukiSpectralMarginParameters,
      Tendsto (fun n => (b n).1.1) atTop atTop →
      TendstoLocallyUniformlyOn (fun n => suzukiSpectralMarginLivsic (b n))
        xiHedenmalmLivsicTarget atTop {z : ℂ | 0 < z.im} →
      Tendsto (fun n =>
        (suzukiWeilIntervalGroundEnergy (b n).1 +
            suzukiSpectralMarginShift (b n).1 (b n).2) /
          (suzukiWeilIntervalGroundEnergy (b n).1 +
            boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder (b n).1)))
        atTop (𝓝 0) := by
  intro b hb hconv
  obtain ⟨s, hs⟩ := exists_xi_target_imaginary_ne_zero
  have h := suzukiSpectralMargin_nonzero_limit_forces_margin_zero b hb s _ hs
    (hconv.tendsto_at (by
      change 0 < (I*(s.1 : ℂ)).im
      simpa using (show 0 < s.1 by linarith [s.2.1])))
  simpa only [suzukiSpectralMarginShift_relative_floor] using h

end RHTower
end
