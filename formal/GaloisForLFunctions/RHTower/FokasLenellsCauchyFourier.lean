import GaloisForLFunctions.RHTower.FokasLenellsCauchyExtension
import GaloisForLFunctions.RHTower.FokasLenellsCauchyTrace
import GaloisForLFunctions.RHTower.CauchyKernelTotality

/-!
# The Cauchy integral is the damped Fourier trace

The existing one-sided exponential transforms identify the actual Cauchy kernel
with an L² Fourier datum. Plancherel then identifies the Cauchy integral with the
signed Fourier transform of the damped datum. This proves that the strong Hardy
limits are limits of the actual holomorphic integral, including its normalization.
-/

open MeasureTheory Complex Set Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

def cauchyFourierDatumRaw (upper : Bool) (r a : ℝ) : ℝ → ℂ :=
  if upper then cauchyDatum ((starRingEnd ℂ) (halfPlanePoint upper r a))
  else cauchyDatumUpper ((starRingEnd ℂ) (halfPlanePoint upper r a))

theorem cauchyFourierDatumRaw_memLp (upper : Bool) (r a : ℝ) :
    MemLp (cauchyFourierDatumRaw upper r a) 2 volume := by
  cases upper
  · apply memLp_cauchyDatumUpper
    simpa only [Complex.conj_im,halfPlanePoint_im,Bool.false_eq_true,↓reduceIte,neg_neg] using Real.exp_pos a
  · apply memLp_cauchyDatum
    simpa only [Complex.conj_im,halfPlanePoint_im,↓reduceIte,neg_lt_zero] using Real.exp_pos a

def cauchyFourierDatum (upper : Bool) (r a : ℝ) : SoninL2 :=
  (cauchyFourierDatumRaw_memLp upper r a).toLp (cauchyFourierDatumRaw upper r a)

theorem cauchyFourierDatum_ae (upper : Bool) (r a : ℝ) :
    (cauchyFourierDatum upper r a : ℝ → ℂ) =ᵐ[volume] cauchyFourierDatumRaw upper r a :=
  (cauchyFourierDatumRaw_memLp upper r a).coeFn_toLp

/-- The evaluation kernel is exactly the Fourier transform of the constructed exponential datum. -/
theorem fourier_cauchyFourierDatum (upper : Bool) (r a : ℝ) :
    fourierUnitary (cauchyFourierDatum upper r a) =
      (memLp_cauchyKernel (conj_im_ne (halfPlanePoint_im_ne_zero upper r a))).toLp
        (fun s : ℝ => ((s:ℂ)-(starRingEnd ℂ) (halfPlanePoint upper r a))⁻¹) := by
  cases upper
  · exact fourierTransform_cauchyDatumUpper
      (by simpa only [Complex.conj_im,halfPlanePoint_im,Bool.false_eq_true,↓reduceIte,neg_neg] using Real.exp_pos a)
  · exact fourierTransform_cauchyDatum
      (by simpa only [Complex.conj_im,halfPlanePoint_im,↓reduceIte,neg_lt_zero] using Real.exp_pos a)

/-- Plancherel transfers Cauchy evaluation to the Fourier datum without a Fubini assumption. -/
theorem cauchyExtension_eq_fourierDatum_inner (u : SoninL2) (upper : Bool) (r a : ℝ) :
    cauchyExtension u (halfPlanePoint upper r a) =
      (2*(Real.pi:ℂ)*I)⁻¹ * inner ℂ (cauchyFourierDatum upper r a) (fourierUnitary.symm u) := by
  rw [← cauchyEvaluation_apply]
  change (2*(Real.pi:ℂ)*I)⁻¹ * inner ℂ _ u = _
  rw [← fourier_cauchyFourierDatum,fourierUnitary.inner_map_eq_flip]

private theorem cauchy_phase_factor (upper : Bool) (r a s : ℝ)
    (hs : s ∈ cauchyRay upper) :
    Complex.exp (-2*(Real.pi:ℂ)*I*halfPlanePoint upper r a*(s:ℂ)) =
      Complex.exp (-2*(Real.pi:ℂ)*I*(r:ℂ)*(s:ℂ)) *
        ((Real.exp (-2*Real.pi*|Real.exp a| * |s|):ℝ):ℂ) := by
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  cases upper
  · have hp : 0 < s := hs
    simp only [halfPlanePoint,Bool.false_eq_true,↓reduceIte,abs_of_pos (Real.exp_pos a),abs_of_pos hp]
    push_cast
    ring_nf
    simp
    ring
  · have hn : s < 0 := hs
    simp only [halfPlanePoint,↓reduceIte,abs_of_pos (Real.exp_pos a),abs_of_neg hn]
    push_cast
    ring_nf
    simp

/-- Exact phase and sign normalization of the one-sided Cauchy datum. -/
theorem normalized_cauchyFourierDatum_conj (upper : Bool) (r a s : ℝ) :
    (2*(Real.pi:ℂ)*I)⁻¹ * (starRingEnd ℂ) (cauchyFourierDatumRaw upper r a s) =
      (if upper then (1:ℂ) else -1) *
        Complex.exp (-2*(Real.pi:ℂ)*I*(r:ℂ)*(s:ℂ)) * cauchyDamping upper (Real.exp a) s := by
  have hc : (2*(Real.pi:ℂ)*I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  by_cases hs : s ∈ cauchyRay upper
  · have hphase := cauchy_phase_factor upper r a s hs
    have hconj : (starRingEnd ℂ) (Complex.exp (2*(Real.pi:ℂ)*I*
        (starRingEnd ℂ) (halfPlanePoint upper r a)*(s:ℂ))) =
        Complex.exp (-2*(Real.pi:ℂ)*I*halfPlanePoint upper r a*(s:ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.conj_conj,map_ofNat]
      ring
    cases upper
    · change s ∈ Ioi (0:ℝ) at hs
      simp only [cauchyFourierDatumRaw,Bool.false_eq_true,↓reduceIte,cauchyDatumUpper,
        Set.indicator_of_mem hs,map_mul,hconj,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
      rw [show cauchyDamping false (Real.exp a) s =
        ((Real.exp (-2*Real.pi*|Real.exp a| * |s|):ℝ):ℂ) from Set.indicator_of_mem hs _,hphase]
      field_simp
    · change s ∈ Iio (0:ℝ) at hs
      simp only [cauchyFourierDatumRaw,↓reduceIte,cauchyDatum,
        Set.indicator_of_mem hs,map_neg,map_mul,hconj,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
      rw [show cauchyDamping true (Real.exp a) s =
        ((Real.exp (-2*Real.pi*|Real.exp a| * |s|):ℝ):ℂ) from Set.indicator_of_mem hs _,hphase]
      field_simp
  · cases upper <;> simp only [cauchyFourierDatumRaw,cauchyDatum,cauchyDatumUpper,
      cauchyDamping,cauchyRay,Bool.false_eq_true,↓reduceIte] at hs ⊢ <;>
      simp [Set.indicator_of_notMem hs]

/-- Exponential damping of any L² datum is integrable at every strictly positive height. -/
theorem cauchyDamping_mul_integrable (u : SoninL2) (upper : Bool) (a : ℝ) :
    Integrable (fun s => cauchyDamping upper (Real.exp a) s*(u : ℝ → ℂ) s) volume := by
  have hm := ((cauchyFourierDatumRaw_memLp upper 0 a).star.const_mul
    (2*(Real.pi:ℂ)*I)⁻¹).integrable_mul (Lp.memLp u)
  change Integrable (fun s => ((2*(Real.pi:ℂ)*I)⁻¹ *
    (starRingEnd ℂ) (cauchyFourierDatumRaw upper 0 a s))*(u : ℝ → ℂ) s) volume at hm
  have he : (fun s => ((2*(Real.pi:ℂ)*I)⁻¹ *
    (starRingEnd ℂ) (cauchyFourierDatumRaw upper 0 a s))*(u : ℝ → ℂ) s) =
      (fun s => (if upper then (1:ℂ) else -1)*(cauchyDamping upper (Real.exp a) s*(u : ℝ → ℂ) s)) := by
    funext s
    rw [normalized_cauchyFourierDatum_conj]
    simp [mul_assoc]
  rw [he] at hm
  cases upper
  · simpa using hm.neg
  · simpa using hm

/-- The damped L² representative is also in L¹, so its Fourier integral is literal. -/
theorem dampedCauchyDatum_integrable (u : SoninL2) (upper : Bool) (a : ℝ) :
    Integrable (dampedCauchyDatum upper (Real.exp a) u : ℝ → ℂ) volume :=
  (cauchyDamping_mul_integrable u upper a).congr (dampedCauchyDatum_ae upper (Real.exp a) u).symm

private theorem fourierChar_eq_cauchy_phase (r s : ℝ) :
    (Real.fourierChar (-(inner ℝ s r)) : ℂ) =
      Complex.exp (-2*(Real.pi:ℂ)*I*(r:ℂ)*(s:ℂ)) := by
  rw [Real.fourierChar_apply,
    show (-(inner ℝ s r) : ℝ) = -(s*r) by simp [mul_comm]]
  congr 1
  push_cast
  ring

/-- The literal normalized Cauchy integral is the signed Fourier–Laplace integral. -/
theorem cauchyExtension_eq_fourierIntegral (u : SoninL2) (upper : Bool) (r a : ℝ) :
    cauchyExtension u (halfPlanePoint upper r a) =
      (if upper then (1:ℂ) else -1) *
        𝓕 (fun s => cauchyDamping upper (Real.exp a) s*(fourierUnitary.symm u : ℝ → ℂ) s) r := by
  rw [cauchyExtension_eq_fourierDatum_inner,MeasureTheory.L2.inner_def,← integral_const_mul,
    Real.fourier_eq,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [cauchyFourierDatum_ae upper r a] with s hs
  rw [RCLike.inner_apply,hs]
  change (2*(Real.pi:ℂ)*I)⁻¹ * ((fourierUnitary.symm u : ℝ → ℂ) s *
    (starRingEnd ℂ) (cauchyFourierDatumRaw upper r a s)) = _
  calc
    _ = ((2*(Real.pi:ℂ)*I)⁻¹ * (starRingEnd ℂ) (cauchyFourierDatumRaw upper r a s))*
        (fourierUnitary.symm u : ℝ → ℂ) s := by ring
    _ = _ := by
      rw [normalized_cauchyFourierDatum_conj]
      change _ = (if upper then (1:ℂ) else -1)*((Real.fourierChar (-(inner ℝ s r)) : ℂ)*
        (cauchyDamping upper (Real.exp a) s*(fourierUnitary.symm u : ℝ → ℂ) s))
      rw [fourierChar_eq_cauchy_phase]
      ring

private theorem fourierUnitary_ae_fourierIntegral (u : SoninL2)
    (hu : Integrable (u : ℝ → ℂ) volume) :
    (fourierUnitary u : ℝ → ℂ) =ᵐ[volume] 𝓕 (u : ℝ → ℂ) := by
  have he := coeFn_fourierTransform_ae_eq_fourierIntegral u hu
  filter_upwards [he] with r hr
  change (fourierUnitary u : ℝ → ℂ) r = _ at hr
  rw [hr,Real.Lp.fourierTransform_apply,Real.fourier_eq,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr hu).coeFn_toLp] with s hs
  rw [hs]

private theorem fourierIntegral_dampedCauchyDatum (u : SoninL2) (upper : Bool) (r a : ℝ) :
    𝓕 (dampedCauchyDatum upper (Real.exp a) u : ℝ → ℂ) r =
      𝓕 (fun s => cauchyDamping upper (Real.exp a) s*(u : ℝ → ℂ) s) r := by
  rw [Real.fourier_eq,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [dampedCauchyDatum_ae upper (Real.exp a) u] with s hs
  rw [hs]

/-- The horizontal values of the holomorphic Cauchy integral equal the constructed L² trace. -/
theorem cauchyTrace_ae_cauchyExtension (u : SoninL2) (upper : Bool) (a : ℝ) :
    (cauchyTrace u upper (Real.exp a) : ℝ → ℂ) =ᵐ[volume]
      (fun r => cauchyExtension u (halfPlanePoint upper r a)) := by
  filter_upwards [Lp.coeFn_smul (if upper then (1:ℂ) else -1)
      (fourierUnitary (dampedCauchyDatum upper (Real.exp a) (fourierUnitary.symm u))),
    fourierUnitary_ae_fourierIntegral
      (dampedCauchyDatum upper (Real.exp a) (fourierUnitary.symm u))
      (dampedCauchyDatum_integrable (fourierUnitary.symm u) upper a)] with r hs hf
  change ((if upper then (1:ℂ) else -1) •
    fourierUnitary (dampedCauchyDatum upper (Real.exp a) (fourierUnitary.symm u)) : SoninL2) r = _
  rw [hs,Pi.smul_apply,smul_eq_mul,hf,fourierIntegral_dampedCauchyDatum,
    cauchyExtension_eq_fourierIntegral]

/-- Every horizontal slice of the actual Cauchy integral belongs to L². -/
theorem cauchyExtension_slice_memLp (u : SoninL2) (upper : Bool) (a : ℝ) :
    MemLp (fun r => cauchyExtension u (halfPlanePoint upper r a)) 2 volume :=
  (memLp_congr_ae (cauchyTrace_ae_cauchyExtension u upper a)).mp (Lp.memLp _)

def cauchySlice (u : SoninL2) (upper : Bool) (a : ℝ) : SoninL2 :=
  (cauchyExtension_slice_memLp u upper a).toLp (fun r => cauchyExtension u (halfPlanePoint upper r a))

theorem cauchySlice_eq_trace (u : SoninL2) (upper : Bool) (a : ℝ) :
    cauchySlice u upper a = cauchyTrace u upper (Real.exp a) := by
  apply Lp.ext
  exact (cauchyExtension_slice_memLp u upper a).coeFn_toLp.trans
    (cauchyTrace_ae_cauchyExtension u upper a).symm

/-- The actual holomorphic slices obey the sharp L² contraction bound. -/
theorem cauchySlice_bound (u : SoninL2) (upper : Bool) (a : ℝ) : ‖cauchySlice u upper a‖ ≤ ‖u‖ := by
  rw [cauchySlice_eq_trace]
  exact cauchyTrace_bound u upper (Real.exp a)

/-- Plemelj's lower boundary value, in the strong L² topology. -/
theorem cauchySlice_lower_tendsto (u : SoninL2) :
    Tendsto (cauchySlice u false) atBot (𝓝 (negativeCauchy u)) := by
  exact ((cauchyTrace_lower_tendsto u).comp Real.tendsto_exp_atBot).congr
    (fun a => (cauchySlice_eq_trace u false a).symm)

/-- Plemelj's upper boundary value, in the strong L² topology. -/
theorem cauchySlice_upper_tendsto (u : SoninL2) :
    Tendsto (cauchySlice u true) atBot (𝓝 (u+negativeCauchy u)) := by
  exact ((cauchyTrace_upper_tendsto u).comp Real.tendsto_exp_atBot).congr
    (fun a => (cauchySlice_eq_trace u true a).symm)

end
end RHTower.FokasLenells
