import GaloisForLFunctions.HTGeometry.KleinGordonFlowBounds

/-!
# The field of the evolution and its time derivatives

The evolution is a curve of frequency data; the field it represents is its synthesis against the
character. Two time derivatives may be taken under the frequency integral, because the derivatives of
the data are bounded uniformly in the frequency and locally uniformly in time, and the weight
`⟨ξ⟩⁻ᴺ` supplies the integrable dominating function as soon as `N` exceeds `dim E + 2`.

The measurability of the derivative in the frequency variable is obtained without any joint
continuity: a derivative is a pointwise limit of difference quotients, each of which is continuous in
the frequency, so the derivative is a pointwise limit of continuous functions.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## Measurability of a parametric derivative -/

/-- **The derivative of a continuous family is measurable**, being a pointwise limit of difference
quotients. -/
theorem aestronglyMeasurable_deriv_param {f : ℝ → E → ℂ} {t : ℝ}
    (hcont : ∀ r : ℝ, Continuous (f r))
    (hdiff : ∀ ξ : E, DifferentiableAt ℝ (fun r : ℝ => f r ξ) t) :
    AEStronglyMeasurable (fun ξ : E => deriv (fun r : ℝ => f r ξ) t) (volume : Measure E) := by
  have hstep : ∀ n : ℕ, Continuous
      (fun ξ : E => slope (fun r : ℝ => f r ξ) t (t + 1 / ((n : ℝ) + 1))) := by
    intro n
    have hfun : (fun ξ : E => slope (fun r : ℝ => f r ξ) t (t + 1 / ((n : ℝ) + 1)))
        = fun ξ : E => (((1 / ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)
          * (f (t + 1 / ((n : ℝ) + 1)) ξ - f t ξ) := by
      funext ξ
      simp only [slope, vsub_eq_sub, add_sub_cancel_left, Complex.real_smul]
    rw [hfun]
    exact continuous_const.mul ((hcont _).sub (hcont t))
  refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (fun n => (hstep n).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hslope := (hdiff ξ).hasDerivAt.tendsto_slope
  have hbase : Filter.Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds t) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := h0.const_add t
    simpa using h1
  have hne : ∀ᶠ n : ℕ in Filter.atTop, t + 1 / ((n : ℝ) + 1) ∈ ({t}ᶜ : Set ℝ) := by
    filter_upwards with n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    have : (1 : ℝ) / ((n : ℝ) + 1) = 0 := by linarith [hcontra]
    linarith
  have hseq : Filter.Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin t {t}ᶜ) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase hne
  exact hslope.comp hseq

/-! ## The field -/

/-- The character of the synthesis. -/
noncomputable def kgChar (x ξ : E) : ℂ := (𝐞 ⟪ξ, x⟫ : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgChar (x ξ : E) : ‖kgChar x ξ‖ = 1 := Circle.norm_coe _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgChar' (x : E) : Continuous (kgChar x) := by
  have hinner : Continuous fun ξ : E => ⟪ξ, x⟫ :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner)

/-- The frequency density of the evolution. -/
noncomputable def kgFlowDensity (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) : ℂ :=
  kgWeighted N (kgPotentialFlow a G₀ t) ξ

/-- Its first time derivative. -/
noncomputable def kgFlowDensityDeriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) : ℂ :=
  ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * deriv (fun r : ℝ => kgPotentialFlow a G₀ r ξ) t

/-- And its second. -/
noncomputable def kgFlowDensityDeriv2 (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) : ℂ :=
  ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t

/-- **The field**: the synthesis of the evolution against the character. -/
noncomputable def kgFlowField (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (x : E) : ℂ :=
  ∫ ξ, kgChar x ξ * kgFlowDensity a G₀ t ξ

/-! ## The density and its derivatives -/

theorem continuous_kgFlowDensity (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    Continuous (kgFlowDensity a G₀ t) := continuous_kgWeighted N _

theorem hasDerivAt_kgFlowDensity (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgFlowDensity a G₀ r ξ) (kgFlowDensityDeriv a G₀ t ξ) t := by
  have hbase := (hasDerivAt_kgPotentialFlow_apply a G₀ ξ t).const_mul
    (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹)
  refine hbase.congr_deriv ?_
  rw [kgFlowDensityDeriv, (hasDerivAt_kgPotentialFlow_apply a G₀ ξ t).deriv]

theorem hasDerivAt_kgFlowDensityDeriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgFlowDensityDeriv a G₀ r ξ) (kgFlowDensityDeriv2 a G₀ t ξ) t := by
  have hfun : (fun r : ℝ => kgFlowDensityDeriv a G₀ r ξ)
      = fun r : ℝ => ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
        * deriv (fun q : ℝ => kgPotentialFlow a G₀ q ξ) r := rfl
  rw [hfun]
  have hbase := (hasDerivAt_deriv_kgPotentialFlow_apply a G₀ ξ t).const_mul
    (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹)
  refine hbase.congr_deriv ?_
  rw [kgFlowDensityDeriv2, (hasDerivAt_deriv_kgPotentialFlow_apply a G₀ ξ t).deriv]

theorem kgFlowDensityDeriv_eq_deriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    kgFlowDensityDeriv a G₀ t ξ = deriv (fun r : ℝ => kgFlowDensity a G₀ r ξ) t :=
  (hasDerivAt_kgFlowDensity a G₀ ξ t).deriv.symm

theorem kgFlowDensityDeriv2_eq_deriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    kgFlowDensityDeriv2 a G₀ t ξ = deriv (fun r : ℝ => kgFlowDensityDeriv a G₀ r ξ) t :=
  (hasDerivAt_kgFlowDensityDeriv a G₀ ξ t).deriv.symm

theorem aestronglyMeasurable_kgFlowDensityDeriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    AEStronglyMeasurable (kgFlowDensityDeriv a G₀ t) (volume : Measure E) := by
  have hmain := aestronglyMeasurable_deriv_param (f := fun r ξ => kgFlowDensity a G₀ r ξ) (t := t)
    (fun r => continuous_kgFlowDensity a G₀ r)
    (fun ξ => (hasDerivAt_kgFlowDensity a G₀ ξ t).differentiableAt)
  refine hmain.congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact (kgFlowDensityDeriv_eq_deriv a G₀ ξ t).symm

/-- The second derivative of the density, read off the equation. -/
theorem kgFlowDensityDeriv2_eq (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) :
    kgFlowDensityDeriv2 a G₀ t ξ
      = ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
        * (-(((kgFreq ξ : ℝ) : ℂ) ^ 2 * kgPotentialFlow a G₀ t ξ) + kgFlowSource a G₀ ξ t) := by
  rw [kgFlowDensityDeriv2, (hasDerivAt_deriv_kgPotentialFlow_apply a G₀ ξ t).deriv]

theorem continuous_kgFlowDensityDeriv2 (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    Continuous (kgFlowDensityDeriv2 a G₀ t) := by
  have hfun : kgFlowDensityDeriv2 a G₀ t = fun ξ : E => ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
      * (-(((kgFreq ξ : ℝ) : ℂ) ^ 2 * kgPotentialFlow a G₀ t ξ) + kgFlowSource a G₀ ξ t) := by
    funext ξ
    exact kgFlowDensityDeriv2_eq a G₀ t ξ
  rw [hfun]
  have hinv : Continuous fun ξ : E => ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_kgFreq.pow N)) fun ξ => ?_
    exact Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos ξ) N).ne'
  have hfreq : Continuous fun ξ : E => ((kgFreq ξ : ℝ) : ℂ) ^ 2 :=
    (Complex.continuous_ofReal.comp continuous_kgFreq).pow 2
  have hsrc : Continuous fun ξ : E => kgFlowSource a G₀ ξ t :=
    continuous_kgConv (a.density t) (kgPotentialFlow a G₀ t)
  exact hinv.mul (((hfreq.mul (kgPotentialFlow a G₀ t).continuous).neg).add hsrc)

theorem aestronglyMeasurable_kgFlowDensityDeriv2 (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    AEStronglyMeasurable (kgFlowDensityDeriv2 a G₀ t) (volume : Measure E) :=
  (continuous_kgFlowDensityDeriv2 a G₀ t).aestronglyMeasurable

/-! ## Differentiating the synthesis in time -/

theorem norm_kgFlowDensityDeriv (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) :
    ‖kgFlowDensityDeriv a G₀ t ξ‖
      = (kgFreq ξ ^ N)⁻¹ * ‖deriv (fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖ := by
  rw [kgFlowDensityDeriv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (kgFreq_pos ξ) N)]

theorem norm_kgFlowDensityDeriv2 (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) :
    ‖kgFlowDensityDeriv2 a G₀ t ξ‖
      = (kgFreq ξ ^ N)⁻¹ * ‖deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖ := by
  rw [kgFlowDensityDeriv2, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (kgFreq_pos ξ) N)]

theorem integrable_kgChar_mul_kgFlowDensity (hN : (Module.finrank ℝ E : ℝ) < N)
    (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (x : E) :
    Integrable (fun ξ : E => kgChar x ξ * kgFlowDensity a G₀ t ξ) (volume : Measure E) := by
  refine (integrable_kgWeighted (E := E) hN (kgPotentialFlow a G₀ t)).bdd_mul (c := 1)
    ((continuous_kgChar' x).aestronglyMeasurable) ?_
  filter_upwards with ξ
  exact le_of_eq (norm_kgChar x ξ)

theorem abs_le_of_mem_ball {t t₀ : ℝ} (ht : t ∈ Metric.ball t₀ 1) : |t| ≤ |t₀| + 1 := by
  have h := Metric.mem_ball.mp ht
  rw [Real.dist_eq] at h
  have h1 : |t| - |t₀| ≤ |t - t₀| := abs_sub_abs_le_abs_sub t t₀
  linarith

/-- **The field is differentiable in time**, with the derivative taken under the frequency
integral. -/
theorem hasDerivAt_kgFlowField (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (x : E) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => kgFlowField a G₀ t x)
      (∫ ξ, kgChar x ξ * kgFlowDensityDeriv a G₀ t₀ ξ) t₀ := by
  have hNdim : (Module.finrank ℝ E : ℝ) < N := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    linarith
  set T : ℝ := |t₀| + 1 with hT
  set B : ℝ := ‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T) with hB
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (F := fun t ξ => kgChar x ξ * kgFlowDensity a G₀ t ξ)
    (F' := fun t ξ => kgChar x ξ * kgFlowDensityDeriv a G₀ t ξ)
    (bound := fun ξ => (kgFreq ξ ^ N)⁻¹ * B) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((continuous_kgChar' x).mul (continuous_kgFlowDensity a G₀ t)).aestronglyMeasurable)
    (integrable_kgChar_mul_kgFlowDensity hNdim a G₀ t₀ x)
    (((continuous_kgChar' x).aestronglyMeasurable).mul
      (aestronglyMeasurable_kgFlowDensityDeriv a G₀ t₀))
    ?_ ((integrable_kgFreq_inv_pow (E := E) hNdim).mul_const B) ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro t ht
    have habs : |t| ≤ T := abs_le_of_mem_ball ht
    have hd := norm_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ habs
    rw [norm_mul, norm_kgChar, one_mul, norm_kgFlowDensityDeriv]
    exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)
  · filter_upwards with ξ
    intro t _
    exact (hasDerivAt_kgFlowDensity a G₀ ξ t).const_mul (kgChar x ξ)

/-- **The field is twice differentiable in time**, and the second derivative is the synthesis of the
oscillator equation. -/
theorem hasDerivAt_deriv_kgFlowField (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (x : E) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun r : ℝ => kgFlowField a G₀ r x) t)
      (∫ ξ, kgChar x ξ * kgFlowDensityDeriv2 a G₀ t₀ ξ) t₀ := by
  have hNdim : (Module.finrank ℝ E : ℝ) < N := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    linarith
  set T : ℝ := |t₀| + 1 with hT
  set S : ℝ := kgFlowSize a G₀ T with hS
  have hfun : (fun t : ℝ => deriv (fun r : ℝ => kgFlowField a G₀ r x) t)
      = fun t : ℝ => ∫ ξ, kgChar x ξ * kgFlowDensityDeriv a G₀ t ξ := by
    funext t
    exact (hasDerivAt_kgFlowField hN a G₀ x t).deriv
  rw [hfun]
  have hbound : ∀ (t : ℝ), |t| ≤ T → ∀ ξ : E,
      ‖kgChar x ξ * kgFlowDensityDeriv2 a G₀ t ξ‖
        ≤ kgFreq ξ ^ 2 * (kgFreq ξ ^ N)⁻¹ * S + (kgFreq ξ ^ N)⁻¹ * (kgFlowBoundConst a * S) := by
    intro t ht ξ
    have hd := norm_deriv_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ ht
    rw [norm_mul, norm_kgChar, one_mul, norm_kgFlowDensityDeriv2]
    have hstep : (kgFreq ξ ^ N)⁻¹ * ‖deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
        ≤ (kgFreq ξ ^ N)⁻¹ * (kgFreq ξ ^ 2 * S + kgFlowBoundConst a * S) :=
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)
    refine hstep.trans_eq ?_
    ring
  have hbound' : ∀ ξ : E,
      ‖kgChar x ξ * kgFlowDensityDeriv a G₀ t₀ ξ‖
        ≤ (kgFreq ξ ^ N)⁻¹ * (‖G₀‖ + 2 * (kgFlowBoundConst a * S * T)) := by
    intro ξ
    have habs : |t₀| ≤ T := by
      rw [hT]
      linarith
    have hd := norm_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ habs
    rw [norm_mul, norm_kgChar, one_mul, norm_kgFlowDensityDeriv]
    exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)
  have hF_int : Integrable (fun ξ : E => kgChar x ξ * kgFlowDensityDeriv a G₀ t₀ ξ)
      (volume : Measure E) := by
    refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hNdim).mul_const
        (‖G₀‖ + 2 * (kgFlowBoundConst a * S * T)))
      (((continuous_kgChar' x).aestronglyMeasurable).mul
        (aestronglyMeasurable_kgFlowDensityDeriv a G₀ t₀)) ?_
    filter_upwards with ξ
    exact hbound' ξ
  have hbint : Integrable (fun ξ : E =>
      kgFreq ξ ^ 2 * (kgFreq ξ ^ N)⁻¹ * S + (kgFreq ξ ^ N)⁻¹ * (kgFlowBoundConst a * S))
      (volume : Measure E) :=
    ((integrable_kgFreq_pow_mul_inv_pow (E := E) (j := 2) hN).mul_const S).add
      ((integrable_kgFreq_inv_pow (E := E) hNdim).mul_const (kgFlowBoundConst a * S))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (F := fun t ξ => kgChar x ξ * kgFlowDensityDeriv a G₀ t ξ)
    (F' := fun t ξ => kgChar x ξ * kgFlowDensityDeriv2 a G₀ t ξ)
    (bound := fun ξ => kgFreq ξ ^ 2 * (kgFreq ξ ^ N)⁻¹ * S
      + (kgFreq ξ ^ N)⁻¹ * (kgFlowBoundConst a * S)) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((continuous_kgChar' x).aestronglyMeasurable).mul
        (aestronglyMeasurable_kgFlowDensityDeriv a G₀ t))
    hF_int
    (((continuous_kgChar' x).aestronglyMeasurable).mul
      (aestronglyMeasurable_kgFlowDensityDeriv2 a G₀ t₀))
    ?_ hbint ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro t ht
    exact hbound t (abs_le_of_mem_ball ht) ξ
  · filter_upwards with ξ
    intro t _
    exact (hasDerivAt_kgFlowDensityDeriv a G₀ ξ t).const_mul (kgChar x ξ)

end GaloisForLFunctions.HTGeometry
