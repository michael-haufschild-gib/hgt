import GaloisForLFunctions.HTGeometry.HillDrivenFlowBounds
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSynthesisField

/-!
# The field of the driven evolution, and its two time derivatives

The evolution of the previous files is a curve of frequency data; the field it represents is its
synthesis against the character. Two time derivatives may be taken under the frequency integral,
because the velocity of the evolution and the equation itself are bounded on windows of times
uniformly in the frequency, and the weight `⟨ξ⟩⁻ᴺ` supplies the integrable dominating function as
soon as `N` exceeds `dim E + 2`.

The second derivative is the synthesis of the equation: `-ω(t,ξ)²û + (a_t * û)`, the first term
carrying the mass and the speed, the second the potential.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section Field

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- The frequency density of the driven evolution. -/
noncomputable def hillDrivenDensity (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ)
    (ξ : E) : ℂ := kgWeighted N (hillPotentialFlow a b G₀ t) ξ

/-- Its first time derivative. -/
noncomputable def hillDrivenDensityDeriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) (ξ : E) : ℂ := ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowApplyDeriv a b G₀ ξ t

/-- And its second, read off the equation. -/
noncomputable def hillDrivenDensitySecond (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) (ξ : E) : ℂ :=
  ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ *
    (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ + hillFlowSource a b G₀ ξ t)

/-- **The field**: the synthesis of the driven evolution against the character. -/
noncomputable def hillDrivenField (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ)
    (x : E) : ℂ := ∫ ξ, kgChar x ξ * hillDrivenDensity a b G₀ t ξ

/-! ## The density and its derivatives -/

theorem continuous_hillDrivenDensity (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) : Continuous (hillDrivenDensity a b G₀ t) := continuous_kgWeighted N _

theorem hasDerivAt_hillDrivenDensity (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillDrivenDensity a b G₀ r ξ)
      (hillDrivenDensityDeriv a b G₀ t ξ) t :=
  (hasDerivAt_hillPotentialFlow_apply a b G₀ ξ t).const_mul (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹)

theorem hasDerivAt_hillDrivenDensityDeriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillDrivenDensityDeriv a b G₀ r ξ)
      (hillDrivenDensitySecond a b G₀ t ξ) t :=
  (hasDerivAt_hillFlowApplyDeriv a b G₀ ξ t).const_mul (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹)

theorem hillDrivenDensityDeriv_eq_deriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    hillDrivenDensityDeriv a b G₀ t ξ = deriv (fun r : ℝ => hillDrivenDensity a b G₀ r ξ) t :=
  (hasDerivAt_hillDrivenDensity a b G₀ ξ t).deriv.symm

theorem aestronglyMeasurable_hillDrivenDensityDeriv (a : HillSpeed) (b : WienerFamily E N)
    (G₀ : E →ᵇ ℂ) (t : ℝ) :
    AEStronglyMeasurable (hillDrivenDensityDeriv a b G₀ t) (volume : Measure E) := by
  have hmain := aestronglyMeasurable_deriv_param
    (f := fun r ξ => hillDrivenDensity a b G₀ r ξ) (t := t)
    (fun r => continuous_hillDrivenDensity a b G₀ r)
    (fun ξ => (hasDerivAt_hillDrivenDensity a b G₀ ξ t).differentiableAt)
  refine hmain.congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact (hillDrivenDensityDeriv_eq_deriv a b G₀ ξ t).symm

theorem continuous_hillDrivenDensitySecond (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) : Continuous (hillDrivenDensitySecond a b G₀ t) := by
  have hinv : Continuous fun ξ : E => ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_kgFreq.pow N)) fun ξ => ?_
    exact Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos ξ) N).ne'
  have hfreq : Continuous fun ξ : E => ((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_massiveFreq_freq a.mass a.speed t).pow 2)
  have hsrc : Continuous fun ξ : E => hillFlowSource a b G₀ ξ t :=
    continuous_kgConv (b.density t) (hillPotentialFlow a b G₀ t)
  have hprod : Continuous fun ξ : E =>
      -(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ +
        hillFlowSource a b G₀ ξ t :=
    (hfreq.neg.mul (hillPotentialFlow a b G₀ t).continuous).add hsrc
  exact hinv.mul hprod

theorem aestronglyMeasurable_hillDrivenDensitySecond (a : HillSpeed) (b : WienerFamily E N)
    (G₀ : E →ᵇ ℂ) (t : ℝ) :
    AEStronglyMeasurable (hillDrivenDensitySecond a b G₀ t) (volume : Measure E) :=
  (continuous_hillDrivenDensitySecond a b G₀ t).aestronglyMeasurable

theorem norm_hillDrivenDensityDeriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) (ξ : E) :
    ‖hillDrivenDensityDeriv a b G₀ t ξ‖
      = (kgFreq ξ ^ N)⁻¹ * ‖hillFlowApplyDeriv a b G₀ ξ t‖ := by
  rw [hillDrivenDensityDeriv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (kgFreq_pos ξ) N)]

theorem integrable_kgChar_mul_hillDrivenDensity (hN : (Module.finrank ℝ E : ℝ) < N)
    (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (x : E) :
    Integrable (fun ξ : E => kgChar x ξ * hillDrivenDensity a b G₀ t ξ) (volume : Measure E) := by
  refine (integrable_kgWeighted (E := E) hN (hillPotentialFlow a b G₀ t)).bdd_mul (c := 1)
    ((continuous_kgChar' x).aestronglyMeasurable) ?_
  filter_upwards with ξ
  exact le_of_eq (norm_kgChar x ξ)

/-! ## The dominating bounds -/

theorem norm_kgChar_mul_hillDrivenDensityDeriv_le (a : HillSpeed) (b : WienerFamily E N)
    (G₀ : E →ᵇ ℂ) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x ξ : E) :
    ‖kgChar x ξ * hillDrivenDensityDeriv a b G₀ t ξ‖
      ≤ (kgFreq ξ ^ N)⁻¹ * hillVelocitySize a b G₀ T := by
  rw [norm_mul, norm_kgChar, one_mul, norm_hillDrivenDensityDeriv]
  exact mul_le_mul_of_nonneg_left (norm_hillFlowApplyDeriv_le_window a b G₀ hT ht ξ)
    (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)

theorem norm_kgChar_mul_hillDrivenDensitySecond_le (a : HillSpeed) (b : WienerFamily E N)
    (G₀ : E →ᵇ ℂ) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x ξ : E) :
    ‖kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ‖
      ≤ kgFreq ξ ^ (2 : ℕ) * (kgFreq ξ ^ N)⁻¹ *
          ((a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * hillFlowSize a b G₀ T) +
        (kgFreq ξ ^ N)⁻¹ * hillSourceSize a b G₀ T := by
  have hinvnn : (0 : ℝ) ≤ (kgFreq ξ ^ N)⁻¹ := inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le
  have hfreqsq : a.freq ξ t ^ (2 : ℕ) ≤ (a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ) := by
    have h1 : a.freq ξ t ^ (2 : ℕ) ≤ a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) :=
      massiveFreq_sq_le a.mass_pos a.speed_sq_le le_rfl t
    have h2 : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := kgFreq_sq ξ
    nlinarith [sq_nonneg a.mass, sq_nonneg a.sizeBound, sq_nonneg ‖ξ‖]
  have hflow : ‖hillPotentialFlow a b G₀ t ξ‖ ≤ hillFlowSize a b G₀ T :=
    le_trans ((hillPotentialFlow a b G₀ t).norm_coe_le_norm ξ)
      (norm_hillPotentialFlow_le_window a b G₀ hT ht)
  have hsrc : ‖hillFlowSource a b G₀ ξ t‖ ≤ hillSourceSize a b G₀ T :=
    norm_hillFlowSource_le_window a b G₀ hT ht ξ
  have hnorm : ‖kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ‖
      = (kgFreq ξ ^ N)⁻¹ *
        ‖-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ +
          hillFlowSource a b G₀ ξ t‖ := by
    rw [norm_mul, norm_kgChar, one_mul, hillDrivenDensitySecond, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (kgFreq_pos ξ) N)]
  rw [hnorm]
  have hterm : ‖-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ +
      hillFlowSource a b G₀ ξ t‖
      ≤ (a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ) * hillFlowSize a b G₀ T +
        hillSourceSize a b G₀ T := by
    refine (norm_add_le _ _).trans (add_le_add ?_ hsrc)
    have hmul : ‖-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ‖
        = a.freq ξ t ^ (2 : ℕ) * ‖hillPotentialFlow a b G₀ t ξ‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (a.freq ξ t))]
    rw [hmul]
    exact mul_le_mul hfreqsq hflow (norm_nonneg _)
      (mul_nonneg (by positivity) (sq_nonneg (kgFreq ξ)))
  refine (mul_le_mul_of_nonneg_left hterm hinvnn).trans_eq ?_
  ring

/-! ## The two time derivatives of the field -/

/-- **The field is differentiable in time**, with the derivative taken under the frequency
integral. -/
theorem hasDerivAt_hillDrivenField (hN : (Module.finrank ℝ E : ℝ) < N) (a : HillSpeed)
    (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (x : E) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => hillDrivenField a b G₀ t x)
      (∫ ξ, kgChar x ξ * hillDrivenDensityDeriv a b G₀ t₀ ξ) t₀ := by
  set T : ℝ := |t₀| + 1 with hT
  have hTnn : (0 : ℝ) ≤ T := by
    rw [hT]
    positivity
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (F := fun t ξ => kgChar x ξ * hillDrivenDensity a b G₀ t ξ)
    (F' := fun t ξ => kgChar x ξ * hillDrivenDensityDeriv a b G₀ t ξ)
    (bound := fun ξ => (kgFreq ξ ^ N)⁻¹ * hillVelocitySize a b G₀ T)
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((continuous_kgChar' x).mul (continuous_hillDrivenDensity a b G₀ t)).aestronglyMeasurable)
    (integrable_kgChar_mul_hillDrivenDensity hN a b G₀ t₀ x)
    (((continuous_kgChar' x).aestronglyMeasurable).mul
      (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t₀))
    ?_ ((integrable_kgFreq_inv_pow (E := E) hN).mul_const (hillVelocitySize a b G₀ T)) ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro t ht
    exact norm_kgChar_mul_hillDrivenDensityDeriv_le a b G₀ hTnn (abs_le_of_mem_ball ht) x ξ
  · filter_upwards with ξ
    intro t _
    exact (hasDerivAt_hillDrivenDensity a b G₀ ξ t).const_mul (kgChar x ξ)

/-- **The field is twice differentiable in time**, and the second derivative is the synthesis of the
equation. -/
theorem hasDerivAt_deriv_hillDrivenField (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (a : HillSpeed)
    (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (x : E) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun r : ℝ => hillDrivenField a b G₀ r x) t)
      (∫ ξ, kgChar x ξ * hillDrivenDensitySecond a b G₀ t₀ ξ) t₀ := by
  have hNdim : (Module.finrank ℝ E : ℝ) < N := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    linarith
  set T : ℝ := |t₀| + 1 with hT
  have hTnn : (0 : ℝ) ≤ T := by
    rw [hT]
    positivity
  have ht₀T : |t₀| ≤ T := by
    rw [hT]
    linarith
  have hfun : (fun t : ℝ => deriv (fun r : ℝ => hillDrivenField a b G₀ r x) t)
      = fun t : ℝ => ∫ ξ, kgChar x ξ * hillDrivenDensityDeriv a b G₀ t ξ := by
    funext t
    exact (hasDerivAt_hillDrivenField hNdim a b G₀ x t).deriv
  rw [hfun]
  have hF_int : Integrable (fun ξ : E => kgChar x ξ * hillDrivenDensityDeriv a b G₀ t₀ ξ)
      (volume : Measure E) := by
    refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hNdim).mul_const
        (hillVelocitySize a b G₀ T))
      (((continuous_kgChar' x).aestronglyMeasurable).mul
        (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t₀)) ?_
    filter_upwards with ξ
    exact norm_kgChar_mul_hillDrivenDensityDeriv_le a b G₀ hTnn ht₀T x ξ
  have hbint : Integrable (fun ξ : E =>
      kgFreq ξ ^ (2 : ℕ) * (kgFreq ξ ^ N)⁻¹ *
          ((a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * hillFlowSize a b G₀ T) +
        (kgFreq ξ ^ N)⁻¹ * hillSourceSize a b G₀ T) (volume : Measure E) :=
    ((integrable_kgFreq_pow_mul_inv_pow (E := E) (j := 2) hN).mul_const
      ((a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * hillFlowSize a b G₀ T)).add
      ((integrable_kgFreq_inv_pow (E := E) hNdim).mul_const (hillSourceSize a b G₀ T))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (F := fun t ξ => kgChar x ξ * hillDrivenDensityDeriv a b G₀ t ξ)
    (F' := fun t ξ => kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ)
    (bound := fun ξ => kgFreq ξ ^ (2 : ℕ) * (kgFreq ξ ^ N)⁻¹ *
        ((a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * hillFlowSize a b G₀ T) +
      (kgFreq ξ ^ N)⁻¹ * hillSourceSize a b G₀ T)
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((continuous_kgChar' x).aestronglyMeasurable).mul
        (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t))
    hF_int
    (((continuous_kgChar' x).aestronglyMeasurable).mul
      (aestronglyMeasurable_hillDrivenDensitySecond a b G₀ t₀))
    ?_ hbint ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro t ht
    exact norm_kgChar_mul_hillDrivenDensitySecond_le a b G₀ hTnn (abs_le_of_mem_ball ht) x ξ
  · filter_upwards with ξ
    intro t _
    exact (hasDerivAt_hillDrivenDensityDeriv a b G₀ ξ t).const_mul (kgChar x ξ)

end Field

end GaloisForLFunctions.HTGeometry
