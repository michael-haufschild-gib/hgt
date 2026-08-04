import GaloisForLFunctions.HTGeometry.KleinGordonEnergyConservation
import GaloisForLFunctions.HTGeometry.KleinGordonSymbolEvolution

/-!
# The propagator is differentiable on regular data

The generator of the Klein–Gordon rotation is unbounded — it is `⟨D⟩` in the off-diagonal entries —
so `t ↦ U(t)v` is differentiable only for `v` in a domain. That domain is the range of `⟨D⟩⁻¹`, and
on it the derivative is again a *bounded* expression: differentiating `cos(t⟨ξ⟩)/⟨ξ⟩` produces
`-sin(t⟨ξ⟩)`, and the `⟨ξ⟩` produced by the chain rule cancels the `⟨ξ⟩⁻¹` of the datum.

That is what makes the statement provable with the strong-convergence machinery alone. The difference
quotient of `cos(s⟨ξ⟩)/⟨ξ⟩` at `t` is bounded by one uniformly in `s`, because the cosine is
`1`-Lipschitz, and converges pointwise to `-sin(t⟨ξ⟩)`; so the corresponding multipliers converge
strongly, which is exactly the limit defining the derivative in `L²`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

/-! ## The symbols of the regularised propagator and its difference quotients -/

section Symbols

variable {E : Type*} [NormedAddCommGroup E]

/-- The cosine symbol divided by the frequency: the symbol of `C_t ⟨D⟩⁻¹`. -/
def kgCosOverFreq (t : ℝ) (ξ : E) : ℂ := ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)

/-- The sine symbol divided by the frequency: the symbol of `S_t ⟨D⟩⁻¹`. -/
def kgSinOverFreq (t : ℝ) (ξ : E) : ℂ := ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)

/-- The difference quotient of the cosine symbol over the frequency. -/
def kgCosSlope (t s : ℝ) (ξ : E) : ℂ :=
  (((s - t)⁻¹ * (Real.cos (s * kgFreq ξ) - Real.cos (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)

/-- The difference quotient of the sine symbol over the frequency. -/
def kgSinSlope (t s : ℝ) (ξ : E) : ℂ :=
  (((s - t)⁻¹ * (Real.sin (s * kgFreq ξ) - Real.sin (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)

theorem norm_kgCosOverFreq_le (t : ℝ) (ξ : E) : ‖kgCosOverFreq t ξ‖ ≤ 1 := by
  rw [kgCosOverFreq, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (kgFreq_pos ξ), div_le_one (kgFreq_pos ξ)]
  exact le_trans (Real.abs_cos_le_one _) (one_le_kgFreq ξ)

theorem norm_kgSinOverFreq_le (t : ℝ) (ξ : E) : ‖kgSinOverFreq t ξ‖ ≤ 1 := by
  rw [kgSinOverFreq, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (kgFreq_pos ξ), div_le_one (kgFreq_pos ξ)]
  exact le_trans (Real.abs_sin_le_one _) (one_le_kgFreq ξ)

/-- The difference quotient of a `1`-Lipschitz function of `s⟨ξ⟩`, divided by `⟨ξ⟩`, is bounded by
one uniformly in `s`. -/
private theorem abs_slope_div_le {t s c : ℝ} (hc : 1 ≤ c) {a b : ℝ}
    (hab : |a - b| ≤ |s - t| * c) : |(s - t)⁻¹ * (a - b) / c| ≤ 1 := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rcases eq_or_ne s t with rfl | hst
  · rw [sub_self, inv_zero, zero_mul, zero_div, abs_zero]
    exact zero_le_one
  · have hne : |s - t| ≠ 0 := by
      simpa [sub_eq_zero] using hst
    have hpos : 0 < |s - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    rw [abs_div, abs_mul, abs_inv, abs_of_pos hcpos, div_le_one hcpos]
    calc |s - t|⁻¹ * |a - b| ≤ |s - t|⁻¹ * (|s - t| * c) :=
          mul_le_mul_of_nonneg_left hab (by positivity)
      _ = c := by field_simp

theorem norm_kgCosSlope_le (t s : ℝ) (ξ : E) : ‖kgCosSlope t s ξ‖ ≤ 1 := by
  rw [kgCosSlope, Complex.norm_real, Real.norm_eq_abs]
  refine abs_slope_div_le (one_le_kgFreq ξ) ?_
  refine le_trans (Real.abs_cos_sub_cos_le _ _) (le_of_eq ?_)
  rw [← sub_mul, abs_mul, abs_of_pos (kgFreq_pos ξ)]

theorem norm_kgSinSlope_le (t s : ℝ) (ξ : E) : ‖kgSinSlope t s ξ‖ ≤ 1 := by
  rw [kgSinSlope, Complex.norm_real, Real.norm_eq_abs]
  refine abs_slope_div_le (one_le_kgFreq ξ) ?_
  refine le_trans (Real.abs_sin_sub_sin_le _ _) (le_of_eq ?_)
  rw [← sub_mul, abs_mul, abs_of_pos (kgFreq_pos ξ)]

theorem continuous_kgCosOverFreq (t : ℝ) : Continuous (kgCosOverFreq (E := E) t) := by
  show Continuous fun ξ : E => ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp ?_
  exact (Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq)).div
    continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'

theorem continuous_kgSinOverFreq (t : ℝ) : Continuous (kgSinOverFreq (E := E) t) := by
  show Continuous fun ξ : E => ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp ?_
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq)).div
    continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'

theorem continuous_kgCosSlope (t s : ℝ) : Continuous (kgCosSlope (E := E) t s) := by
  show Continuous fun ξ : E =>
    (((s - t)⁻¹ * (Real.cos (s * kgFreq ξ) - Real.cos (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div ?_ continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'
  exact continuous_const.mul
    ((Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq)).sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq)))

theorem continuous_kgSinSlope (t s : ℝ) : Continuous (kgSinSlope (E := E) t s) := by
  show Continuous fun ξ : E =>
    (((s - t)⁻¹ * (Real.sin (s * kgFreq ξ) - Real.sin (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div ?_ continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'
  exact continuous_const.mul
    ((Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq)).sub
      (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq)))

/-! ## The pointwise limits -/

theorem tendsto_kgCosSlope (t : ℝ) (ξ : E) :
    Tendsto (fun s : ℝ => kgCosSlope t s ξ) (nhdsWithin t {t}ᶜ)
      (nhds ((-Real.sin (t * kgFreq ξ) : ℝ) : ℂ)) := by
  have hd : HasDerivAt (fun r : ℝ => Real.cos (r * kgFreq ξ) / kgFreq ξ)
      (-Real.sin (t * kgFreq ξ)) t := by
    have h := (hasDerivAt_cosFreq ξ t).div_const (kgFreq ξ)
    have heq : -(kgFreq ξ * Real.sin (t * kgFreq ξ)) / kgFreq ξ = -Real.sin (t * kgFreq ξ) := by
      rw [neg_div, mul_comm, mul_div_assoc, div_self (kgFreq_pos ξ).ne', mul_one]
    rwa [heq] at h
  have hs := hd.tendsto_slope
  have hcongr : ∀ s : ℝ, slope (fun r : ℝ => Real.cos (r * kgFreq ξ) / kgFreq ξ) t s
      = (s - t)⁻¹ * (Real.cos (s * kgFreq ξ) - Real.cos (t * kgFreq ξ)) / kgFreq ξ := by
    intro s
    rw [slope_def_field]
    field_simp
  have hreal : Tendsto
      (fun s : ℝ => (s - t)⁻¹ * (Real.cos (s * kgFreq ξ) - Real.cos (t * kgFreq ξ)) / kgFreq ξ)
      (nhdsWithin t {t}ᶜ) (nhds (-Real.sin (t * kgFreq ξ))) := by
    exact hs.congr hcongr
  exact (Complex.continuous_ofReal.tendsto _).comp hreal

theorem tendsto_kgSinSlope (t : ℝ) (ξ : E) :
    Tendsto (fun s : ℝ => kgSinSlope t s ξ) (nhdsWithin t {t}ᶜ)
      (nhds ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)) := by
  have hd : HasDerivAt (fun r : ℝ => Real.sin (r * kgFreq ξ) / kgFreq ξ)
      (Real.cos (t * kgFreq ξ)) t := by
    have h := (hasDerivAt_sinFreq ξ t).div_const (kgFreq ξ)
    have heq : kgFreq ξ * Real.cos (t * kgFreq ξ) / kgFreq ξ = Real.cos (t * kgFreq ξ) := by
      rw [mul_comm, mul_div_assoc, div_self (kgFreq_pos ξ).ne', mul_one]
    rwa [heq] at h
  have hs := hd.tendsto_slope
  have hcongr : ∀ s : ℝ, slope (fun r : ℝ => Real.sin (r * kgFreq ξ) / kgFreq ξ) t s
      = (s - t)⁻¹ * (Real.sin (s * kgFreq ξ) - Real.sin (t * kgFreq ξ)) / kgFreq ξ := by
    intro s
    rw [slope_def_field]
    field_simp
  have hreal : Tendsto
      (fun s : ℝ => (s - t)⁻¹ * (Real.sin (s * kgFreq ξ) - Real.sin (t * kgFreq ξ)) / kgFreq ξ)
      (nhdsWithin t {t}ᶜ) (nhds (Real.cos (t * kgFreq ξ))) := by
    exact hs.congr hcongr
  exact (Complex.continuous_ofReal.tendsto _).comp hreal

end Symbols

/-! ## The regularised propagators -/

section SymbolsMeasurable

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_kgCosOverFreq (t : ℝ) : Measurable (kgCosOverFreq (E := E) t) :=
  (continuous_kgCosOverFreq t).measurable

theorem measurable_kgSinOverFreq (t : ℝ) : Measurable (kgSinOverFreq (E := E) t) :=
  (continuous_kgSinOverFreq t).measurable

theorem measurable_kgCosSlope (t s : ℝ) : Measurable (kgCosSlope (E := E) t s) :=
  (continuous_kgCosSlope t s).measurable

theorem measurable_kgSinSlope (t s : ℝ) : Measurable (kgSinSlope (E := E) t s) :=
  (continuous_kgSinSlope t s).measurable

end SymbolsMeasurable

section Operators

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A real scalar acts on `L²` through its complex image. -/
private theorem real_smul_lp (r : ℝ) (y : Lp (α := E) ℂ 2) : ((r : ℂ)) • y = r • y := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

theorem kgFreqInvOp_eq : kgFreqInvOp (E := E)
    = fourierMulCLM (measurable_kgFreqInv (E := E)) zero_le_one norm_kgFreqInv_le := rfl

/-- `C_t ⟨D⟩⁻¹` is the multiplier with symbol `cos(t⟨ξ⟩)/⟨ξ⟩`. -/
theorem kgCosOp_comp_kgFreqInvOp (t : ℝ) :
    (kgCosOp (E := E) t).comp kgFreqInvOp
      = fourierMulCLM (measurable_kgCosOverFreq (E := E) t) zero_le_one
        (norm_kgCosOverFreq_le t) := by
  rw [kgCosOp_eq, kgFreqInvOp_eq]
  refine fourierMulCLM_comp _ _ (measurable_kgCosOverFreq (E := E) t) _ _ _ _ _
    (norm_kgCosOverFreq_le t) (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * (((kgFreq ξ)⁻¹ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, div_eq_mul_inv]

/-- `S_t ⟨D⟩⁻¹` is the multiplier with symbol `sin(t⟨ξ⟩)/⟨ξ⟩`. -/
theorem kgSinOp_comp_kgFreqInvOp (t : ℝ) :
    (kgSinOp (E := E) t).comp kgFreqInvOp
      = fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one
        (norm_kgSinOverFreq_le t) := by
  rw [kgSinOp_eq, kgFreqInvOp_eq]
  refine fourierMulCLM_comp _ _ (measurable_kgSinOverFreq (E := E) t) _ _ _ _ _
    (norm_kgSinOverFreq_le t) (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    = ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * (((kgFreq ξ)⁻¹ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, div_eq_mul_inv]

/-- The difference quotient of the regularised cosine propagator is itself a multiplier. -/
theorem slope_kgCosOp_freqInv (t s : ℝ) (g : Lp (α := E) ℂ 2) :
    slope (fun r : ℝ => kgCosOp r (kgFreqInvOp g)) t s
      = fourierMulCLM (measurable_kgCosSlope (E := E) t s) zero_le_one
        (norm_kgCosSlope_le t s) g := by
  have hdiff : Measurable fun ξ : E => kgCosOverFreq s ξ - kgCosOverFreq t ξ :=
    (measurable_kgCosOverFreq s).sub (measurable_kgCosOverFreq t)
  have hdiffb : ∀ ξ : E, ‖kgCosOverFreq s ξ - kgCosOverFreq t ξ‖ ≤ 2 := by
    intro ξ
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := norm_kgCosOverFreq_le s ξ
    have h2 := norm_kgCosOverFreq_le t ξ
    linarith
  have hsub : fourierMulCLM hdiff (by norm_num) hdiffb
      = fourierMulCLM (measurable_kgCosOverFreq (E := E) s) zero_le_one
          (norm_kgCosOverFreq_le s)
        - fourierMulCLM (measurable_kgCosOverFreq (E := E) t) zero_le_one
          (norm_kgCosOverFreq_le t) :=
    fourierMulCLM_sub _ _ hdiff _ _ _ _ _ hdiffb (Filter.Eventually.of_forall fun _ => rfl)
  have hsmul : fourierMulCLM (measurable_kgCosSlope (E := E) t s) zero_le_one
      (norm_kgCosSlope_le t s)
      = (((s - t)⁻¹ : ℝ) : ℂ) • fourierMulCLM hdiff (by norm_num) hdiffb := by
    refine fourierMulCLM_smul _ _ _ _ _ (norm_kgCosSlope_le t s) _
      (Filter.Eventually.of_forall fun ξ => ?_)
    show (((s - t)⁻¹ * (Real.cos (s * kgFreq ξ) - Real.cos (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)
      = (((s - t)⁻¹ : ℝ) : ℂ)
        * (((Real.cos (s * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
          - ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ))
    rw [← Complex.ofReal_sub, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrw : ∀ r : ℝ, (fourierMulCLM (measurable_kgCosOverFreq (E := E) r) zero_le_one
      (norm_kgCosOverFreq_le r)) g = kgCosOp r (kgFreqInvOp g) := by
    intro r
    rw [← kgCosOp_comp_kgFreqInvOp]
    rfl
  rw [hsmul, hsub, slope_def_module, smul_apply, sub_apply, hrw, hrw, real_smul_lp]

/-- The difference quotient of the regularised sine propagator is itself a multiplier. -/
theorem slope_kgSinOp_freqInv (t s : ℝ) (g : Lp (α := E) ℂ 2) :
    slope (fun r : ℝ => kgSinOp r (kgFreqInvOp g)) t s
      = fourierMulCLM (measurable_kgSinSlope (E := E) t s) zero_le_one
        (norm_kgSinSlope_le t s) g := by
  have hdiff : Measurable fun ξ : E => kgSinOverFreq s ξ - kgSinOverFreq t ξ :=
    (measurable_kgSinOverFreq s).sub (measurable_kgSinOverFreq t)
  have hdiffb : ∀ ξ : E, ‖kgSinOverFreq s ξ - kgSinOverFreq t ξ‖ ≤ 2 := by
    intro ξ
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := norm_kgSinOverFreq_le s ξ
    have h2 := norm_kgSinOverFreq_le t ξ
    linarith
  have hsub : fourierMulCLM hdiff (by norm_num) hdiffb
      = fourierMulCLM (measurable_kgSinOverFreq (E := E) s) zero_le_one
          (norm_kgSinOverFreq_le s)
        - fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one
          (norm_kgSinOverFreq_le t) :=
    fourierMulCLM_sub _ _ hdiff _ _ _ _ _ hdiffb (Filter.Eventually.of_forall fun _ => rfl)
  have hsmul : fourierMulCLM (measurable_kgSinSlope (E := E) t s) zero_le_one
      (norm_kgSinSlope_le t s)
      = (((s - t)⁻¹ : ℝ) : ℂ) • fourierMulCLM hdiff (by norm_num) hdiffb := by
    refine fourierMulCLM_smul _ _ _ _ _ (norm_kgSinSlope_le t s) _
      (Filter.Eventually.of_forall fun ξ => ?_)
    show (((s - t)⁻¹ * (Real.sin (s * kgFreq ξ) - Real.sin (t * kgFreq ξ)) / kgFreq ξ : ℝ) : ℂ)
      = (((s - t)⁻¹ : ℝ) : ℂ)
        * (((Real.sin (s * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
          - ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ))
    rw [← Complex.ofReal_sub, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrw : ∀ r : ℝ, (fourierMulCLM (measurable_kgSinOverFreq (E := E) r) zero_le_one
      (norm_kgSinOverFreq_le r)) g = kgSinOp r (kgFreqInvOp g) := by
    intro r
    rw [← kgSinOp_comp_kgFreqInvOp]
    rfl
  rw [hsmul, hsub, slope_def_module, smul_apply, sub_apply, hrw, hrw, real_smul_lp]

/-! ## The derivatives -/

/-- **The regularised cosine propagator is differentiable, with derivative `-S_t`.** The `⟨ξ⟩`
produced by the chain rule cancels the `⟨ξ⟩⁻¹` of the datum, so the derivative is bounded. -/
theorem hasDerivAt_kgCosOp_freqInv (t : ℝ) (g : Lp (α := E) ℂ 2) :
    HasDerivAt (fun s : ℝ => kgCosOp s (kgFreqInvOp g)) (-(kgSinOp t g)) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hneg : Measurable fun ξ : E => ((-Real.sin (t * kgFreq ξ) : ℝ) : ℂ) := by
    have hcont : Continuous fun ξ : E => ((-Real.sin (t * kgFreq ξ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq)).neg)
    exact hcont.measurable
  have hnegb : ∀ ξ : E, ‖((-Real.sin (t * kgFreq ξ) : ℝ) : ℂ)‖ ≤ 1 := by
    intro ξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact Real.abs_sin_le_one _
  have hlimit : Tendsto
      (fun s : ℝ => fourierMulCLM (measurable_kgCosSlope (E := E) t s) zero_le_one
        (norm_kgCosSlope_le t s) g) (nhdsWithin t {t}ᶜ)
      (nhds (fourierMulCLM hneg zero_le_one hnegb g)) :=
    tendsto_fourierMulCLM_apply (l := nhdsWithin t {t}ᶜ)
      (fun s => measurable_kgCosSlope (E := E) t s) hneg zero_le_one
      (fun s => norm_kgCosSlope_le t s) hnegb (fun ξ => tendsto_kgCosSlope t ξ) g
  have hval : fourierMulCLM hneg zero_le_one hnegb = -(kgSinOp (E := E) t) := by
    rw [kgSinOp_eq]
    exact fourierMulCLM_neg _ hneg _ _ _ hnegb (Filter.Eventually.of_forall fun ξ => by
      show ((-Real.sin (t * kgFreq ξ) : ℝ) : ℂ) = -((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
      rw [Complex.ofReal_neg])
  rw [hval] at hlimit
  refine hlimit.congr fun s => ?_
  exact (slope_kgCosOp_freqInv t s g).symm

/-- **The regularised sine propagator is differentiable, with derivative `C_t`.** -/
theorem hasDerivAt_kgSinOp_freqInv (t : ℝ) (g : Lp (α := E) ℂ 2) :
    HasDerivAt (fun s : ℝ => kgSinOp s (kgFreqInvOp g)) (kgCosOp t g) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlimit : Tendsto
      (fun s : ℝ => fourierMulCLM (measurable_kgSinSlope (E := E) t s) zero_le_one
        (norm_kgSinSlope_le t s) g) (nhdsWithin t {t}ᶜ)
      (nhds (fourierMulCLM (measurable_kgCosSymbol (E := E) t) zero_le_one
        (norm_kgCosSymbol_le t) g)) :=
    tendsto_fourierMulCLM_apply (l := nhdsWithin t {t}ᶜ)
      (fun s => measurable_kgSinSlope (E := E) t s) (measurable_kgCosSymbol (E := E) t)
      zero_le_one (fun s => norm_kgSinSlope_le t s) (norm_kgCosSymbol_le t)
      (fun ξ => tendsto_kgSinSlope t ξ) g
  rw [← kgCosOp_eq] at hlimit
  refine hlimit.congr fun s => ?_
  exact (slope_kgSinOp_freqInv t s g).symm

end Operators

/-! ## The propagator on regular data -/

section Regular

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The regularisation of an energy state: apply `⟨D⟩⁻¹` in both components. Its range is the domain
on which the propagator is differentiable. -/
def kgRegular (g : KGEnergy E) : KGEnergy E :=
  kgPair E (kgFreqInvOp g.fst, kgFreqInvOp g.snd)

theorem kgPropagator_kgRegular (s : ℝ) (g : KGEnergy E) :
    kgPropagator s (kgRegular g)
      = kgPair E (kgCosOp s (kgFreqInvOp g.fst) + kgSinOp s (kgFreqInvOp g.snd),
          -(kgSinOp s (kgFreqInvOp g.fst)) + kgCosOp s (kgFreqInvOp g.snd)) := by
  rw [kgPropagator_apply, kgRegular]
  simp only [kgPair_fst, kgPair_snd]

set_option maxHeartbeats 1000000 in
/-- **The propagator is differentiable on regular data**, with the derivative given by the generator
evaluated at the regularising vector. -/
theorem hasDerivAt_kgPropagator_regular (t : ℝ) (g : KGEnergy E) :
    HasDerivAt (fun s : ℝ => kgPropagator s (kgRegular g))
      (kgPair E (-(kgSinOp t g.fst) + kgCosOp t g.snd,
        -(kgCosOp t g.fst) + -(kgSinOp t g.snd))) t := by
  have h1 : HasDerivAt
      (fun s : ℝ => kgCosOp s (kgFreqInvOp g.fst) + kgSinOp s (kgFreqInvOp g.snd))
      (-(kgSinOp t g.fst) + kgCosOp t g.snd) t :=
    (hasDerivAt_kgCosOp_freqInv t g.fst).add (hasDerivAt_kgSinOp_freqInv t g.snd)
  have h2 : HasDerivAt
      (fun s : ℝ => -(kgSinOp s (kgFreqInvOp g.fst)) + kgCosOp s (kgFreqInvOp g.snd))
      (-(kgCosOp t g.fst) + -(kgSinOp t g.snd)) t :=
    ((hasDerivAt_kgSinOp_freqInv t g.fst).neg).add (hasDerivAt_kgCosOp_freqInv t g.snd)
  have hL : HasFDerivAt (fun w : (Lp (α := E) ℂ 2) × (Lp (α := E) ℂ 2) => kgPair E w)
      ((kgPair E).restrictScalars ℝ)
      (kgCosOp t (kgFreqInvOp g.fst) + kgSinOp t (kgFreqInvOp g.snd),
        -(kgSinOp t (kgFreqInvOp g.fst)) + kgCosOp t (kgFreqInvOp g.snd)) :=
    ((kgPair E).restrictScalars ℝ).hasFDerivAt
  simp only [kgPropagator_kgRegular]
  exact hL.comp_hasDerivAt t (h1.prodMk h2)

end Regular

end GaloisForLFunctions.HTGeometry
