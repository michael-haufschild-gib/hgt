import GaloisForLFunctions.HTGeometry.FirstEndpointMellin

/-! The actual restored source moment after removal of its explicit horizon power. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The restored moment with its explicit incoming power divided out and its endpoint value restored. -/
def normalizedFirstEndpointMellin (F : ℂ → ℝ → ℂ) (w : ℂ) (b : ℝ) : ℂ :=
  if b=0 then F w 0/(w+1) else firstEndpointMellin F b w/(b:ℂ)^(w+1)

theorem normalizedFirstEndpointMellin_zero (F : ℂ → ℝ → ℂ) (w : ℂ) :
    normalizedFirstEndpointMellin F w 0=F w 0/(w+1) := by simp [normalizedFirstEndpointMellin]

/-- The actual remainder integral has a sharp power bound throughout Re(w)>-2. -/
theorem normalizedMellinRemainder_norm_le {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    ‖firstEndpointMellinRemainder F b w‖ ≤ C*b^(w.re+2)/(w.re+2) := by
  have hr := firstEndpointMellinRemainder_integrable hb.le hw hm hC
  have hp : IntegrableOn (fun t : ℝ => t^(w.re+1)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have he : (∫ t in Ioc (0:ℝ) b, C*t^(w.re+1))=C*b^(w.re+2)/(w.re+2) := by
    rw [integral_const_mul,← intervalIntegral.integral_of_le hb.le,
      integral_rpow (Or.inl (by linarith : -1 < w.re+1)),
      show w.re+1+1=w.re+2 by ring,Real.zero_rpow (by linarith : w.re+2 ≠ 0),sub_zero]
    ring
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) b, ‖(t:ℂ)^w*(F w t-F w 0)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (0:ℝ) b, C*t^(w.re+1) := by
      apply integral_mono_ae hr.norm (hp.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1,Real.rpow_add ht.1,Real.rpow_one]
      calc
        _ ≤ t^w.re*(C*t) := mul_le_mul_of_nonneg_left (hC t ht) (Real.rpow_nonneg ht.1.le _)
        _ = _ := by ring
    _ = _ := he

/-- Dividing out the actual incoming power leaves a uniform linear endpoint remainder. -/
theorem normalizedFirstEndpointMellin_sub_zero_bound {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    ‖normalizedFirstEndpointMellin F w b-F w 0/(w+1)‖ ≤ C*b/(w.re+2) := by
  have hn : (b:ℂ)^(w+1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hb)))
  have he : normalizedFirstEndpointMellin F w b-F w 0/(w+1)=
      firstEndpointMellinRemainder F b w/(b:ℂ)^(w+1) := by
    rw [normalizedFirstEndpointMellin,if_neg (ne_of_gt hb),firstEndpointMellin]
    field_simp [hn]
    ring
  rw [he,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hb,Complex.add_re,Complex.one_re]
  calc
    _ ≤ (C*b^(w.re+2)/(w.re+2))/b^(w.re+1) :=
      div_le_div_of_nonneg_right (normalizedMellinRemainder_norm_le hb hw hm hC) (Real.rpow_nonneg hb.le _)
    _ = _ := by
      rw [show w.re+2=(w.re+1)+1 by ring,Real.rpow_add hb,Real.rpow_one]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hb (w.re+1))]

/-- A common source remainder and a real-part margin give a common normalized endpoint bound. -/
theorem normalizedFirstEndpointMellin_uniform_bound {F : ℂ → ℝ → ℂ}
    {w : ℂ} {b C β : ℝ} (hb : 0 < b) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hw : β ≤ w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    ‖normalizedFirstEndpointMellin F w b-F w 0/(w+1)‖ ≤ C*b/(β+2) :=
  (normalizedFirstEndpointMellin_sub_zero_bound hb (lt_of_lt_of_le hβ hw) hm hC).trans
    (div_le_div_of_nonneg_left (mul_nonneg hC0 hb.le) (by linarith) (by linarith))

/-- The normalized restored source moment reaches its derived horizon value. -/
theorem normalizedFirstEndpointMellin_tendsto {F : ℂ → ℝ → ℂ} {w : ℂ} {B C : ℝ}
    (hB : 0 < B) (hw : -2 < w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) B, ‖F w t-F w 0‖ ≤ C*t) :
    Tendsto (normalizedFirstEndpointMellin F w) (𝓝[>] (0:ℝ)) (𝓝 (F w 0/(w+1))) := by
  have hlim : Tendsto (fun b : ℝ => C*b/(w.re+2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero,zero_div] using
      ((show Tendsto (fun b : ℝ => b) (𝓝[>] (0:ℝ)) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).const_mul C).div_const (w.re+2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun b => norm_nonneg _)) ?_ hlim
  have he : ∀ᶠ b : ℝ in 𝓝[>] (0:ℝ), b < B :=
    (show ∀ᶠ b : ℝ in 𝓝 (0:ℝ), b < B from Iio_mem_nhds hB).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with b hb hbB
  exact normalizedFirstEndpointMellin_sub_zero_bound hb hw hm
    (fun t ht => hC t ⟨ht.1,ht.2.trans hbB.le⟩)

end
end GaloisForLFunctions.HTGeometry
