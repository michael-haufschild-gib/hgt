import GaloisForLFunctions.HTGeometry.WienerConvolutionOperator

/-!
# The propagator symbols as multiplication operators

On the weighted frequency space the free propagator is multiplication by a bounded symbol, which is
multiplication in the ring of bounded continuous functions — so the operator bound is automatic.

What is not automatic is continuity in time. The symbol `cos(t⟨ξ⟩)` is *not* continuous in `t` for
the supremum norm: at frequency `⟨ξ⟩` the phase moves at speed `⟨ξ⟩`, and the supremum over all
frequencies of `|cos(t⟨ξ⟩) - cos(t'⟨ξ⟩)|` stays equal to `2` for every `t ≠ t'`. Dividing by the
frequency repairs exactly this: the symbols

`cos(t⟨ξ⟩)/⟨ξ⟩` and `sin(t⟨ξ⟩)/⟨ξ⟩`

are bounded by `1` and Lipschitz in `t` with constant `1`, uniformly in `ξ`, because the derivative
in `t` is again bounded by `1` after the division. One derivative of loss buys uniform continuity in
time; that is the entire regularity bookkeeping of the evolution.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E]

/-! ## Multiplication -/

/-- Multiplication by a bounded continuous symbol. -/
noncomputable def kgMulCLM (m : E →ᵇ ℂ) : (E →ᵇ ℂ) →L[ℝ] (E →ᵇ ℂ) :=
  ContinuousLinearMap.mul ℝ (E →ᵇ ℂ) m

theorem kgMulCLM_apply (m G : E →ᵇ ℂ) (ξ : E) : kgMulCLM m G ξ = m ξ * G ξ := rfl

theorem norm_kgMulCLM_le (m : E →ᵇ ℂ) : ‖kgMulCLM m‖ ≤ ‖m‖ := by
  have h := (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).le_opNorm m
  refine h.trans ?_
  have hle : ‖ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_mul_le ℝ (E →ᵇ ℂ)
  nlinarith [norm_nonneg m, norm_nonneg (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ))]

theorem kgMulCLM_sub (m m' : E →ᵇ ℂ) : kgMulCLM m - kgMulCLM m' = kgMulCLM (m - m') := by
  rw [kgMulCLM, kgMulCLM, kgMulCLM, map_sub]

theorem norm_kgMulCLM_sub_le (m m' : E →ᵇ ℂ) : ‖kgMulCLM m - kgMulCLM m'‖ ≤ ‖m - m'‖ := by
  rw [kgMulCLM_sub]
  exact norm_kgMulCLM_le _

/-! ## The two damped propagator symbols -/

theorem continuous_kgSinc (t : ℝ) :
    Continuous fun ξ : E => ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq))
    continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'

theorem continuous_kgCosc (t : ℝ) :
    Continuous fun ξ : E => ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div (Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq))
    continuous_kgFreq fun ξ => (kgFreq_pos ξ).ne'

theorem norm_kgSinc_le (t : ℝ) (ξ : E) :
    ‖((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (kgFreq_pos ξ)]
  rw [div_le_one (kgFreq_pos ξ)]
  exact (Real.abs_sin_le_one _).trans (one_le_kgFreq ξ)

theorem norm_kgCosc_le (t : ℝ) (ξ : E) :
    ‖((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (kgFreq_pos ξ)]
  rw [div_le_one (kgFreq_pos ξ)]
  exact (Real.abs_cos_le_one _).trans (one_le_kgFreq ξ)

/-- The damped sine symbol `sin(t⟨ξ⟩)/⟨ξ⟩`, the Duhamel propagator. -/
noncomputable def kgSincBCF (t : ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : E => ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)) (continuous_kgSinc t) 1
    (norm_kgSinc_le t)

/-- The damped cosine symbol `cos(t⟨ξ⟩)/⟨ξ⟩`, the free propagator with one frequency of loss. -/
noncomputable def kgCoscBCF (t : ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : E => ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)) (continuous_kgCosc t) 1
    (norm_kgCosc_le t)

theorem kgSincBCF_apply (t : ℝ) (ξ : E) :
    kgSincBCF t ξ = ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := rfl

theorem kgCoscBCF_apply (t : ℝ) (ξ : E) :
    kgCoscBCF t ξ = ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := rfl

theorem norm_kgSincBCF_le (t : ℝ) : ‖kgSincBCF (E := E) t‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _

theorem norm_kgCoscBCF_le (t : ℝ) : ‖kgCoscBCF (E := E) t‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _

/-! ## Lipschitz continuity in time -/

/-- **The damped sine symbol is Lipschitz in time, uniformly in the frequency.** -/
theorem norm_kgSincBCF_sub_le (t t' : ℝ) :
    ‖kgSincBCF (E := E) t - kgSincBCF (E := E) t'‖ ≤ |t - t'| := by
  refine (BoundedContinuousFunction.norm_le (abs_nonneg _)).mpr fun ξ => ?_
  have hpos := kgFreq_pos ξ
  have hlip : |Real.sin (t * kgFreq ξ) - Real.sin (t' * kgFreq ξ)|
      ≤ |t * kgFreq ξ - t' * kgFreq ξ| := by
    have h := Real.lipschitzWith_sin.dist_le_mul (t * kgFreq ξ) (t' * kgFreq ξ)
    simpa [Real.dist_eq] using h
  have hsub : (kgSincBCF (E := E) t - kgSincBCF (E := E) t') ξ
      = ((Real.sin (t * kgFreq ξ) / kgFreq ξ - Real.sin (t' * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := by
    rw [BoundedContinuousFunction.sub_apply, kgSincBCF_apply, kgSincBCF_apply]
    push_cast
    ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, div_sub_div_same, abs_div,
    abs_of_pos hpos, div_le_iff₀ hpos]
  calc |Real.sin (t * kgFreq ξ) - Real.sin (t' * kgFreq ξ)|
      ≤ |t * kgFreq ξ - t' * kgFreq ξ| := hlip
    _ = |t - t'| * kgFreq ξ := by
        rw [← sub_mul, abs_mul, abs_of_pos hpos]

/-- **The damped cosine symbol is Lipschitz in time, uniformly in the frequency.** -/
theorem norm_kgCoscBCF_sub_le (t t' : ℝ) :
    ‖kgCoscBCF (E := E) t - kgCoscBCF (E := E) t'‖ ≤ |t - t'| := by
  refine (BoundedContinuousFunction.norm_le (abs_nonneg _)).mpr fun ξ => ?_
  have hpos := kgFreq_pos ξ
  have hlip : |Real.cos (t * kgFreq ξ) - Real.cos (t' * kgFreq ξ)|
      ≤ |t * kgFreq ξ - t' * kgFreq ξ| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (t * kgFreq ξ) (t' * kgFreq ξ)
    simpa [Real.dist_eq] using h
  have hsub : (kgCoscBCF (E := E) t - kgCoscBCF (E := E) t') ξ
      = ((Real.cos (t * kgFreq ξ) / kgFreq ξ - Real.cos (t' * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) := by
    rw [BoundedContinuousFunction.sub_apply, kgCoscBCF_apply, kgCoscBCF_apply]
    push_cast
    ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, div_sub_div_same, abs_div,
    abs_of_pos hpos, div_le_iff₀ hpos]
  calc |Real.cos (t * kgFreq ξ) - Real.cos (t' * kgFreq ξ)|
      ≤ |t * kgFreq ξ - t' * kgFreq ξ| := hlip
    _ = |t - t'| * kgFreq ξ := by
        rw [← sub_mul, abs_mul, abs_of_pos hpos]

theorem continuous_kgSincBCF : Continuous (kgSincBCF (E := E)) := by
  refine LipschitzWith.continuous (K := 1) ?_
  intro t t'
  rw [edist_dist, edist_dist]
  have h := norm_kgSincBCF_sub_le (E := E) t t'
  have hd : dist (kgSincBCF (E := E) t) (kgSincBCF (E := E) t') ≤ dist t t' := by
    rw [dist_eq_norm, Real.dist_eq]
    exact h
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal hd

theorem continuous_kgCoscBCF : Continuous (kgCoscBCF (E := E)) := by
  refine LipschitzWith.continuous (K := 1) ?_
  intro t t'
  rw [edist_dist, edist_dist]
  have h := norm_kgCoscBCF_sub_le (E := E) t t'
  have hd : dist (kgCoscBCF (E := E) t) (kgCoscBCF (E := E) t') ≤ dist t t' := by
    rw [dist_eq_norm, Real.dist_eq]
    exact h
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal hd

end GaloisForLFunctions.HTGeometry
