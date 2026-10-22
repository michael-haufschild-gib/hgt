import GaloisForLFunctions.HTGeometry.WienerSynthesisDensity

/-!
# Uniform bounds on the evolution and its time derivatives

To differentiate the synthesis under the frequency integral one needs bounds on the evolution and on
its first two time derivatives that are *uniform in the frequency* and locally uniform in time. All
three are available, and none of them costs more than the norm of the space the evolution lives in:

* the evolution itself is bounded by `‖G₀‖e^{M|t|}`, the Volterra bound;
* its first time derivative by `‖G₀‖ + 2|t|M‖G₀‖e^{M|t|}`, because the two moments of the source are
  each bounded by the length of the time interval times the supremum of the source;
* its second time derivative by `⟨ξ⟩²` times the first bound plus the source — which is the only
  place where a power of the frequency appears, and it is the reason the synthesis needs two spare
  powers of the weight.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## Moments of a bounded source -/

theorem norm_duhamelCosPart_le {ω : ℝ} {h : ℝ → ℂ} {C : ℝ} {t : ℝ}
    (hC : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖h s‖ ≤ C) :
    ‖duhamelCosPart ω h t‖ ≤ C * |t| := by
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖((Real.cos (s * ω) : ℝ) : ℂ) * h s‖ ≤ C := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos (s * ω)| ≤ 1 := Real.abs_cos_le_one _
    have h2 := hC s hs
    nlinarith [norm_nonneg (h s), abs_nonneg (Real.cos (s * ω))]
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa [duhamelCosPart] using hmain

theorem norm_duhamelSinPart_le {ω : ℝ} {h : ℝ → ℂ} {C : ℝ} {t : ℝ}
    (hC : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖h s‖ ≤ C) :
    ‖duhamelSinPart ω h t‖ ≤ C * |t| := by
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖((Real.sin (s * ω) : ℝ) : ℂ) * h s‖ ≤ C := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.sin (s * ω)| ≤ 1 := Real.abs_sin_le_one _
    have h2 := hC s hs
    nlinarith [norm_nonneg (h s), abs_nonneg (Real.sin (s * ω))]
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa [duhamelSinPart] using hmain

theorem abs_le_abs_of_mem_uIoc {t s : ℝ} (hs : s ∈ Set.uIoc (0 : ℝ) t) : |s| ≤ |t| := by
  rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_pos h1, abs_of_pos (lt_of_lt_of_le h1 h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_neg (lt_of_lt_of_le h1 h2)]
    linarith

/-! ## The evolution and its source -/

/-- The uniform bound on the kernel of the evolution. -/
noncomputable def kgFlowBoundConst (a : WienerFamily E N) : ℝ := Real.sqrt 2 ^ N * a.bound

theorem kgFlowBoundConst_nonneg (a : WienerFamily E N) : 0 ≤ kgFlowBoundConst a :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.bound_nonneg

/-- **The evolution obeys the Volterra bound.** -/
theorem norm_kgPotentialFlow_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    ‖kgPotentialFlow a G₀ t‖ ≤ ‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|) :=
  norm_volterraSolution_le (M := kgFlowBoundConst a) (F := ‖G₀‖)
    (continuous_kgFreeTerm G₀) (continuous_kgDuhamelKernel a) (kgFlowBoundConst_nonneg a)
    (norm_nonneg _) (norm_kgDuhamelKernel_le a) (norm_kgFreeTerm_le G₀) t

/-- **The source is bounded by the evolution**, uniformly in the frequency. -/
theorem norm_kgFlowSource_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (s : ℝ) :
    ‖kgFlowSource a G₀ ξ s‖
      ≤ kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |s|)) := by
  have h1 : ‖kgFlowSource a G₀ ξ s‖
      ≤ Real.sqrt 2 ^ N * (a.density s).norm' * ‖kgPotentialFlow a G₀ s‖ :=
    norm_kgConv_le (a.density s) (kgPotentialFlow a G₀ s) ξ
  have h2 := norm_kgPotentialFlow_le a G₀ s
  have hb : Real.sqrt 2 ^ N * (a.density s).norm' ≤ kgFlowBoundConst a := by
    rw [kgFlowBoundConst]
    exact mul_le_mul_of_nonneg_left (a.norm_le s) (pow_nonneg (Real.sqrt_nonneg 2) N)
  refine h1.trans ?_
  calc Real.sqrt 2 ^ N * (a.density s).norm' * ‖kgPotentialFlow a G₀ s‖
      ≤ kgFlowBoundConst a * ‖kgPotentialFlow a G₀ s‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |s|)) :=
        mul_le_mul_of_nonneg_left h2 (kgFlowBoundConst_nonneg a)

/-- The source, bounded uniformly on a time interval and in the frequency. -/
theorem norm_kgFlowSource_le_of_mem (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) {t s : ℝ}
    (hs : s ∈ Set.uIoc (0 : ℝ) t) :
    ‖kgFlowSource a G₀ ξ s‖
      ≤ kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) := by
  refine (norm_kgFlowSource_le a G₀ ξ s).trans ?_
  have habs := abs_le_abs_of_mem_uIoc hs
  have hexp : Real.exp (kgFlowBoundConst a * |s|)
      ≤ Real.exp (kgFlowBoundConst a * |t|) := by
    refine Real.exp_le_exp.mpr ?_
    exact mul_le_mul_of_nonneg_left habs (kgFlowBoundConst_nonneg a)
  have hG : (0 : ℝ) ≤ ‖G₀‖ := norm_nonneg _
  have hstep : ‖G₀‖ * Real.exp (kgFlowBoundConst a * |s|)
      ≤ ‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|) := mul_le_mul_of_nonneg_left hexp hG
  exact mul_le_mul_of_nonneg_left hstep (kgFlowBoundConst_nonneg a)

/-! ## The first time derivative -/

/-- **The first time derivative of the evolution is bounded uniformly in the frequency.** -/
theorem norm_deriv_kgPotentialFlow_apply_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E)
    (t : ℝ) :
    ‖deriv (fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
      ≤ ‖G₀‖ + 2 * (kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) * |t|) := by
  set C : ℝ := kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) with hC
  have hsrc : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖kgFlowSource a G₀ ξ s‖ ≤ C := fun s hs =>
    norm_kgFlowSource_le_of_mem a G₀ ξ hs
  have hA : ‖duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖ ≤ C * |t| :=
    norm_duhamelCosPart_le hsrc
  have hB : ‖duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖ ≤ C * |t| :=
    norm_duhamelSinPart_le hsrc
  have hderiv := (hasDerivAt_kgPotentialFlow_apply a G₀ ξ t).deriv
  rw [hderiv]
  have hG₀ : ‖G₀ ξ‖ ≤ ‖G₀‖ := G₀.norm_coe_le_norm ξ
  have hs1 : |Real.sin (t * kgFreq ξ)| ≤ 1 := Real.abs_sin_le_one _
  have hc1 : |Real.cos (t * kgFreq ξ)| ≤ 1 := Real.abs_cos_le_one _
  have hterm1 : ‖-(((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * G₀ ξ)‖ ≤ ‖G₀‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (G₀ ξ), abs_nonneg (Real.sin (t * kgFreq ξ))]
  have hterm2 : ‖((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
      * duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖ ≤ C * |t| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t),
      abs_nonneg (Real.cos (t * kgFreq ξ))]
  have hterm3 : ‖((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
      * duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖ ≤ C * |t| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t),
      abs_nonneg (Real.sin (t * kgFreq ξ))]
  calc ‖-(((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * G₀ ξ)
        + ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t
        + ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
          * duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖
      ≤ ‖-(((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * G₀ ξ)
          + ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
            * duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖
        + ‖((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
            * duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t‖ := norm_add_le _ _
    _ ≤ (‖G₀‖ + C * |t|) + C * |t| :=
        add_le_add ((norm_add_le _ _).trans (add_le_add hterm1 hterm2)) hterm3
    _ = ‖G₀‖ + 2 * (C * |t|) := by ring

/-! ## The second time derivative -/

/-- **The second time derivative costs exactly two powers of the frequency.** -/
theorem norm_deriv_deriv_kgPotentialFlow_apply_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E)
    (t : ℝ) :
    ‖deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
      ≤ kgFreq ξ ^ (2 : ℕ) * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|))
        + kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) := by
  have hderiv := (hasDerivAt_deriv_kgPotentialFlow_apply a G₀ ξ t).deriv
  rw [hderiv]
  have hflow : ‖kgPotentialFlow a G₀ t ξ‖ ≤ ‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|) :=
    ((kgPotentialFlow a G₀ t).norm_coe_le_norm ξ).trans (norm_kgPotentialFlow_le a G₀ t)
  have hsrc := norm_kgFlowSource_le a G₀ ξ t
  have hfreq : ‖-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ) * kgPotentialFlow a G₀ t ξ)‖
      ≤ kgFreq ξ ^ (2 : ℕ) * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) := by
    rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (kgFreq_pos ξ)]
    exact mul_le_mul_of_nonneg_left hflow (by positivity)
  refine (norm_add_le _ _).trans (add_le_add hfreq ?_)
  exact hsrc

/-! ## Bounds uniform on a time interval -/

/-- The uniform bound on the evolution over a time interval. -/
noncomputable def kgFlowSize (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) : ℝ :=
  ‖G₀‖ * Real.exp (kgFlowBoundConst a * T)

theorem kgFlowSize_nonneg (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) :
    0 ≤ kgFlowSize a G₀ T :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem kgFlowSize_mono (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) {t T : ℝ} (ht : |t| ≤ T) :
    ‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|) ≤ kgFlowSize a G₀ T := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left ht (kgFlowBoundConst_nonneg a)

/-- **The first time derivative, bounded uniformly on a time interval and in the frequency.** -/
theorem norm_deriv_kgPotentialFlow_apply_le_of_abs_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) {t T : ℝ} (ht : |t| ≤ T) :
    ‖deriv (fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
      ≤ ‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T) := by
  refine (norm_deriv_kgPotentialFlow_apply_le a G₀ ξ t).trans ?_
  have hT : 0 ≤ T := le_trans (abs_nonneg t) ht
  have hsize := kgFlowSize_mono a G₀ ht
  have hM := kgFlowBoundConst_nonneg a
  have h1 : kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|))
      ≤ kgFlowBoundConst a * kgFlowSize a G₀ T := mul_le_mul_of_nonneg_left hsize hM
  have h2 : (0 : ℝ) ≤ kgFlowBoundConst a * kgFlowSize a G₀ T :=
    mul_nonneg hM (kgFlowSize_nonneg a G₀ T)
  have h3 : kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|)) * |t|
      ≤ kgFlowBoundConst a * kgFlowSize a G₀ T * T := by
    refine mul_le_mul h1 ht (abs_nonneg t) h2
  linarith

/-- **The second time derivative, bounded uniformly on a time interval**, with the two powers of the
frequency displayed. -/
theorem norm_deriv_deriv_kgPotentialFlow_apply_le_of_abs_le (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) {t T : ℝ} (ht : |t| ≤ T) :
    ‖deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
      ≤ kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T := by
  refine (norm_deriv_deriv_kgPotentialFlow_apply_le a G₀ ξ t).trans ?_
  have hsize := kgFlowSize_mono a G₀ ht
  have hM := kgFlowBoundConst_nonneg a
  have h1 : kgFreq ξ ^ (2 : ℕ) * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|))
      ≤ kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T :=
    mul_le_mul_of_nonneg_left hsize (by positivity)
  have h2 : kgFlowBoundConst a * (‖G₀‖ * Real.exp (kgFlowBoundConst a * |t|))
      ≤ kgFlowBoundConst a * kgFlowSize a G₀ T := mul_le_mul_of_nonneg_left hsize hM
  linarith

end GaloisForLFunctions.HTGeometry
