import GaloisForLFunctions.HTGeometry.FirstEndpointMellinSpatial

/-! The exact cutoff limit of the restored first Mellin endpoint subtraction. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The subtracted endpoint has its actual integrable power bound. -/
theorem firstEndpointMellinRemainder_norm_le {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hw : -2 < w.re)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    ‖firstEndpointMellinRemainder F b w‖ ≤ C*b^(w.re+2)/(w.re+2) := by
  rw [firstEndpointMellinRemainder,← intervalIntegral.integral_of_le hb]
  calc
    _ ≤ ∫ t in (0:ℝ)..b, C*t^(w.re+1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hb
      · filter_upwards with t ht
        rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
          Real.rpow_add ht.1,Real.rpow_one]
        calc
          _ ≤ t^w.re*(C*t) := mul_le_mul_of_nonneg_left (hC t ht)
            (Real.rpow_nonneg ht.1.le _)
          _ = _ := by ring
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re+1)).const_mul C
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : -1 < w.re+1))]
      rw [show w.re+1+1=w.re+2 by ring,Real.zero_rpow (by linarith : w.re+2 ≠ 0),sub_zero]
      ring

/-- After restoring the explicit singular term, the remaining endpoint current vanishes. -/
theorem firstEndpointMellinRemainder_tendsto_zero {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    Tendsto (fun e => firstEndpointMellinRemainder F e w) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : 0 < w.re+2 := by linarith
  have hlim : Tendsto (fun e : ℝ => C*e^(w.re+2)/(w.re+2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (w.re+2) (Or.inr hp.le)).const_mul C).div_const (w.re+2)
    simpa only [Real.zero_rpow hp.ne',mul_zero,zero_div] using h.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact firstEndpointMellinRemainder_norm_le he0.le hw
    (fun t ht => hC t ⟨ht.1,ht.2.trans heb.le⟩)

/-- The cutoff integral retains exactly the endpoint term fixed by its original source. -/
theorem firstEndpointMellin_cutoff_eq {F : ℂ → ℝ → ℂ} {w : ℂ} {b e C : ℝ}
    (he : 0 < e) (heb : e ≤ b) (hw : -2 < w.re) (hw1 : w+1 ≠ 0)
    (hm : Measurable (F w)) (hc : ∀ t ∈ Ioc (0:ℝ) b, ContinuousAt (F w) t)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    (∫ t in e..b, (t:ℂ)^w*F w t)+F w 0*(e:ℂ)^(w+1)/(w+1) =
      firstEndpointMellin F b w-firstEndpointMellinRemainder F e w := by
  have hs : uIcc e b ⊆ Ioc (0:ℝ) b := by
    rw [uIcc_of_le heb]
    intro t ht
    exact ⟨he.trans_le ht.1,ht.2⟩
  have hder (t : ℝ) (ht : t ∈ uIcc e b) := firstEndpointMellin_hasDerivAt
    (hs ht).1 hw hw1 hm (hc t (hs ht)) (fun v hv => hC v ⟨hv.1,hv.2.trans (hs ht).2⟩)
  have hi : IntervalIntegrable (fun t : ℝ => (t:ℂ)^w*F w t) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hp := (Complex.hasStrictDerivAt_cpow_const (c := w)
      (show (t:ℂ) ∈ Complex.slitPlane by simp [Complex.mem_slitPlane_iff,(hs ht).1])).hasDerivAt.comp_ofReal
    exact (hp.continuousAt.mul (hc t (hs ht))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi,firstEndpointMellin]
  simp only [firstEndpointMellin]
  ring

/-- The original cutoff integrals converge after their source-determined endpoint restoration. -/
theorem firstEndpointMellin_cutoff_tendsto {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hw1 : w+1 ≠ 0)
    (hm : Measurable (F w)) (hc : ∀ t ∈ Ioc (0:ℝ) b, ContinuousAt (F w) t)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    Tendsto (fun e : ℝ => (∫ t in e..b, (t:ℂ)^w*F w t)+F w 0*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (firstEndpointMellin F b w)) := by
  have h := (tendsto_const_nhds (x := firstEndpointMellin F b w)).sub
    (firstEndpointMellinRemainder_tendsto_zero hb hw hC)
  simp only [sub_zero] at h
  apply h.congr'
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact (firstEndpointMellin_cutoff_eq he0 heb.le hw hw1 hm hc hC).symm

end
end GaloisForLFunctions.HTGeometry
