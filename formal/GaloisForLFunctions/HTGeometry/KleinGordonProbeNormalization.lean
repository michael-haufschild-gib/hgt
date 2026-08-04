import GaloisForLFunctions.HTGeometry.KleinGordonPotentialWave

/-!
# The probe does not vanish

A solution of the field equation is a clock probe only where it does not vanish, so the construction
has to produce a datum whose field is nonzero at a prescribed event. The conjugate character is such
a datum: at `t = 0` the character of the synthesis and the datum cancel exactly, and what is left is
the integral of a positive weight,

`u(0, x₀) = ∫ ⟨ξ⟩⁻ᴺ⁻¹ dξ > 0`.

Away from `t = 0` the field is continuous in both variables — the same dominated convergence that
differentiated it — so it stays nonzero on a neighbourhood of the event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## The conjugate character as a datum -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_conj_kgChar (x₀ ξ : E) : ‖(starRingEnd ℂ) (kgChar x₀ ξ)‖ ≤ 1 := by
  rw [RCLike.norm_conj]
  exact le_of_eq (norm_kgChar x₀ ξ)

/-- The datum concentrated at an event: the conjugate of the character. -/
noncomputable def kgConjChar (x₀ : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : E => (starRingEnd ℂ) (kgChar x₀ ξ))
    (Complex.continuous_conj.comp (continuous_kgChar' x₀)) 1 (norm_conj_kgChar x₀)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgConjChar_apply (x₀ ξ : E) : kgConjChar x₀ ξ = (starRingEnd ℂ) (kgChar x₀ ξ) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgChar_mul_kgConjChar (x₀ ξ : E) : kgChar x₀ ξ * kgConjChar x₀ ξ = 1 := by
  rw [kgConjChar_apply, Complex.mul_conj]
  have h : Complex.normSq (kgChar x₀ ξ) = 1 := by
    have hnorm := norm_kgChar x₀ ξ
    have := Complex.normSq_eq_norm_sq (kgChar x₀ ξ)
    rw [this, hnorm]
    norm_num
  rw [h]
  norm_num

/-! ## The value at the event -/

/-- **At the initial time the field is the integral of the weight**, a positive real number. -/
theorem kgFlowField_zero_apply (a : WienerFamily E N) (x₀ : E) :
    kgFlowField a (kgConjChar x₀) 0 x₀ = ∫ ξ : E, ((kgFreq ξ ^ (N + 1) : ℝ) : ℂ)⁻¹ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgChar x₀ ξ * kgFlowDensity a (kgConjChar x₀) 0 ξ = ((kgFreq ξ ^ (N + 1) : ℝ) : ℂ)⁻¹
  rw [kgFlowDensity, kgWeighted, kgPotentialFlow_zero]
  have hmul : kgChar x₀ ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
      * (((kgFreq ξ : ℝ) : ℂ)⁻¹ * kgConjChar x₀ ξ))
      = (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * ((kgFreq ξ : ℝ) : ℂ)⁻¹)
        * (kgChar x₀ ξ * kgConjChar x₀ ξ) := by ring
  rw [hmul, kgChar_mul_kgConjChar, mul_one, ← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, pow_succ]

theorem integrable_kgFreq_inv_pow_succ (hN : (Module.finrank ℝ E : ℝ) + 2 < N) :
    Integrable (fun ξ : E => (kgFreq ξ ^ (N + 1))⁻¹) (volume : Measure E) := by
  have hdim : (Module.finrank ℝ E : ℝ) < (N + 1 : ℕ) := by push_cast; linarith
  exact integrable_kgFreq_inv_pow (E := E) hdim

/-- The value at the event, as a real number. -/
theorem kgFlowField_zero_eq_ofReal (a : WienerFamily E N) (x₀ : E) :
    kgFlowField a (kgConjChar x₀) 0 x₀ = ((∫ ξ : E, (kgFreq ξ ^ (N + 1))⁻¹ : ℝ) : ℂ) := by
  rw [kgFlowField_zero_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ((kgFreq ξ ^ (N + 1) : ℝ) : ℂ)⁻¹ = (((kgFreq ξ ^ (N + 1))⁻¹ : ℝ) : ℂ)
  rw [Complex.ofReal_inv]

/-- **The weight integrates to a positive number.** -/
theorem integral_kgFreq_inv_pow_succ_pos (hN : (Module.finrank ℝ E : ℝ) + 2 < N) :
    0 < ∫ ξ : E, (kgFreq ξ ^ (N + 1))⁻¹ := by
  have hint := integrable_kgFreq_inv_pow_succ (E := E) hN
  refine (integral_pos_iff_support_of_nonneg_ae ?_ hint).mpr ?_
  · filter_upwards with ξ
    exact inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) (N + 1)).le
  · have hsupp : (Function.support fun ξ : E => (kgFreq ξ ^ (N + 1))⁻¹) = Set.univ := by
      ext ξ
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact inv_ne_zero (pow_pos (kgFreq_pos ξ) (N + 1)).ne'
    rw [hsupp]
    exact Measure.measure_pos_of_nonempty_interior _ (by simp)

/-- **The field at the event is a positive real number**, hence nonzero. -/
theorem kgFlowField_zero_ne_zero (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (a : WienerFamily E N)
    (x₀ : E) : kgFlowField a (kgConjChar x₀) 0 x₀ ≠ 0 := by
  rw [kgFlowField_zero_eq_ofReal]
  exact_mod_cast (integral_kgFreq_inv_pow_succ_pos (E := E) hN).ne'

/-! ## Continuity in the event -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgChar_point (ξ : E) : Continuous fun x : E => kgChar x ξ := by
  have hinner : Continuous fun x : E => ⟪ξ, x⟫ :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner)

/-- **The field is continuous in the event**, jointly in time and space. -/
theorem continuousAt_kgFlowField (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (a : WienerFamily E N)
    (G₀ : E →ᵇ ℂ) (t₀ : ℝ) (x₀ : E) :
    ContinuousAt (fun p : ℝ × E => kgFlowField a G₀ p.1 p.2) (t₀, x₀) := by
  have hdim : (Module.finrank ℝ E : ℝ) < N := by linarith
  set T : ℝ := |t₀| + 1 with hT
  set S : ℝ := kgFlowSize a G₀ T with hS
  have hTmem : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), |p.1| ≤ T := by
    have hcont : ContinuousAt (fun p : ℝ × E => |p.1|) (t₀, x₀) :=
      (continuous_abs.comp continuous_fst).continuousAt
    have hlt : |t₀| < T := by
      rw [hT]
      linarith
    exact hcont.eventually (eventually_le_nhds hlt)
  refine continuousAt_of_dominated (μ := (volume : Measure E))
    (F := fun p : ℝ × E => fun ξ : E => kgChar p.2 ξ * kgFlowDensity a G₀ p.1 ξ)
    (bound := fun ξ : E => (kgFreq ξ ^ N)⁻¹ * S)
    (Filter.Eventually.of_forall fun p =>
      ((continuous_kgChar' p.2).mul (continuous_kgFlowDensity a G₀ p.1)).aestronglyMeasurable)
    ?_ ((integrable_kgFreq_inv_pow (E := E) hdim).mul_const S) ?_
  · filter_upwards [hTmem] with p hp
    filter_upwards with ξ
    have hflow : ‖kgPotentialFlow a G₀ p.1 ξ‖ ≤ S :=
      ((kgPotentialFlow a G₀ p.1).norm_coe_le_norm ξ).trans
        ((norm_kgPotentialFlow_le a G₀ p.1).trans (kgFlowSize_mono a G₀ hp))
    rw [norm_mul, norm_kgChar, one_mul, kgFlowDensity, kgWeighted, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (kgFreq_pos ξ) N)]
    exact mul_le_mul_of_nonneg_left hflow (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)
  · filter_upwards with ξ
    have h1 : ContinuousAt (fun p : ℝ × E => kgChar p.2 ξ) (t₀, x₀) :=
      ((continuous_kgChar_point ξ).comp continuous_snd).continuousAt
    have h2 : ContinuousAt (fun p : ℝ × E => kgFlowDensity a G₀ p.1 ξ) (t₀, x₀) := by
      have hcont : Continuous fun t : ℝ => kgFlowDensity a G₀ t ξ := by
        have hflow : Continuous fun t : ℝ => kgPotentialFlow a G₀ t ξ :=
          ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous).comp
            (continuous_kgPotentialFlow a G₀)
        exact continuous_const.mul hflow
      exact (hcont.comp continuous_fst).continuousAt
    exact h1.mul h2

/-- **The probe is nonzero on a neighbourhood of the event.** -/
theorem eventually_kgFlowField_ne_zero (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (a : WienerFamily E N) (x₀ : E) :
    ∀ᶠ p : ℝ × E in nhds (0, x₀), kgFlowField a (kgConjChar x₀) p.1 p.2 ≠ 0 :=
  (continuousAt_kgFlowField hN a (kgConjChar x₀) 0 x₀).eventually_ne
    (kgFlowField_zero_ne_zero hN a x₀)

end GaloisForLFunctions.HTGeometry
