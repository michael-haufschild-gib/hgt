import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.KleinGordonSymbol

/-!
# The free Klein–Gordon propagator on the energy space

In the energy variables `(⟨D⟩u, ∂ₜu)` the free Klein–Gordon evolution is, frequency by frequency,
the rotation by the angle `t⟨ξ⟩`,

`(cos(t⟨ξ⟩), sin(t⟨ξ⟩); -sin(t⟨ξ⟩), cos(t⟨ξ⟩))`.

Both entries are bounded by one, so each is a Fourier multiplier on `L²` of norm at most one, and the
propagator is a bounded operator on `L² × L²` of norm at most two, *uniformly in time*. That uniform
bound is what an evolution equation with a bounded potential consumes: it is the reason the Duhamel
iteration converges with no smallness hypothesis.

The propagator is not continuous in the operator norm — no nontrivial propagator group is — but it is
strongly continuous, and a uniformly bounded strongly continuous family is jointly continuous in the
time and the vector. That joint continuity is the form an integral equation needs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

/-! ## Joint continuity of a uniformly bounded strongly continuous family -/

section Strong

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A uniformly bounded, strongly continuous family of operators is jointly continuous.** The
difference `T t x - T t₀ x₀` splits into `T t (x - x₀)`, which the uniform bound sends to zero, and
`T t x₀ - T t₀ x₀`, which strong continuity sends to zero. -/
theorem continuous_uncurry_of_strong {T : ℝ → X →L[𝕜] Y} {M : ℝ} (hM : ∀ t, ‖T t‖ ≤ M)
    (hstrong : ∀ x : X, Continuous fun t : ℝ => T t x) :
    Continuous fun q : ℝ × X => T q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  have h1 : Tendsto (fun q : ℝ × X => T q.1 (q.2 - x₀)) (nhds (t₀, x₀)) (nhds 0) := by
    refine squeeze_zero_norm (a := fun q : ℝ × X => M * ‖q.2 - x₀‖) (fun q => ?_) ?_
    · exact le_trans ((T q.1).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hM q.1) (norm_nonneg _))
    · have hcont : Continuous fun q : ℝ × X => M * ‖q.2 - x₀‖ := by fun_prop
      have h := hcont.tendsto (t₀, x₀)
      simpa using h
  have h2 : Tendsto (fun q : ℝ × X => T q.1 x₀) (nhds (t₀, x₀)) (nhds (T t₀ x₀)) :=
    ((hstrong x₀).tendsto t₀).comp (continuous_fst.tendsto (t₀, x₀))
  have h3 : Tendsto (fun q : ℝ × X => T q.1 (q.2 - x₀) + T q.1 x₀) (nhds (t₀, x₀))
      (nhds (0 + T t₀ x₀)) := h1.add h2
  have heq : (fun q : ℝ × X => T q.1 (q.2 - x₀) + T q.1 x₀) = fun q : ℝ × X => T q.1 q.2 := by
    funext q
    rw [← map_add, sub_add_cancel]
  rw [heq, zero_add] at h3
  exact h3

/-- The composite form: a uniformly bounded strongly continuous family evaluated along continuous
families of times and vectors is continuous. -/
theorem continuous_of_strong_comp {T : ℝ → X →L[𝕜] Y} {M : ℝ} (hM : ∀ t, ‖T t‖ ≤ M)
    (hstrong : ∀ x : X, Continuous fun t : ℝ => T t x) {ι : Type*} [TopologicalSpace ι]
    {r : ι → ℝ} {v : ι → X} (hr : Continuous r) (hv : Continuous v) :
    Continuous fun i => T (r i) (v i) :=
  (continuous_uncurry_of_strong hM hstrong).comp (hr.prodMk hv)

end Strong

/-! ## The symbols of the rotation -/

section SymbolBasics

variable {E : Type*} [NormedAddCommGroup E]

theorem continuous_kgFreq : Continuous (kgFreq (E := E)) := by
  show Continuous fun ξ : E => Real.sqrt (1 + ‖ξ‖ ^ 2)
  fun_prop

/-- The off-diagonal entry of the propagator in energy coordinates, `sin(t⟨ξ⟩)`. Unlike the sine
symbol of the field variables it carries no factor `⟨ξ⟩⁻¹`, and so is bounded by one uniformly in
time. -/
def kgSinPhase (t : ℝ) (ξ : E) : ℂ := ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)

/-- The inverse frequency, the symbol of `⟨D⟩⁻¹`. -/
def kgFreqInv (ξ : E) : ℂ := (((kgFreq ξ)⁻¹ : ℝ) : ℂ)

theorem norm_kgSinPhase_le (t : ℝ) (ξ : E) : ‖kgSinPhase t ξ‖ ≤ 1 := by
  rw [kgSinPhase, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

theorem norm_kgFreqInv_le (ξ : E) : ‖kgFreqInv ξ‖ ≤ 1 := by
  rw [kgFreqInv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (kgFreq_pos ξ))]
  exact inv_le_one_of_one_le₀ (one_le_kgFreq ξ)

theorem continuous_kgCosSymbol (t : ℝ) : Continuous (kgCosSymbol (E := E) t) := by
  show Continuous fun ξ : E => ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq))

theorem continuous_kgSinPhase (t : ℝ) : Continuous (kgSinPhase (E := E) t) := by
  show Continuous fun ξ : E => ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq))

theorem continuous_kgFreqInv : Continuous (kgFreqInv (E := E)) := by
  show Continuous fun ξ : E => (((kgFreq ξ)⁻¹ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp (continuous_kgFreq.inv₀ fun ξ => ?_)
  exact (kgFreq_pos ξ).ne'

/-- The cosine symbol is continuous in the time. -/
theorem continuous_kgCosSymbol_time (ξ : E) : Continuous fun t : ℝ => kgCosSymbol t ξ := by
  show Continuous fun t : ℝ => ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_id.mul continuous_const))

/-- The sine symbol is continuous in the time. -/
theorem continuous_kgSinPhase_time (ξ : E) : Continuous fun t : ℝ => kgSinPhase t ξ := by
  show Continuous fun t : ℝ => ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp
    (Real.continuous_sin.comp (continuous_id.mul continuous_const))

private theorem norm_cosMulCos_le (t s : ℝ) (ξ : E) :
    ‖kgCosSymbol t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

private theorem norm_sinMulSin_le (t s : ℝ) (ξ : E) :
    ‖kgSinPhase t ξ * kgSinPhase s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le s ξ)

private theorem norm_cosMulSin_le (t s : ℝ) (ξ : E) :
    ‖kgCosSymbol t ξ * kgSinPhase s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le s ξ)

private theorem norm_sinMulCos_le (t s : ℝ) (ξ : E) :
    ‖kgSinPhase t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

private theorem norm_negSinMulSin_le (t s : ℝ) (ξ : E) :
    ‖-(kgSinPhase t ξ * kgSinPhase s ξ)‖ ≤ 1 := by
  rw [norm_neg]
  exact norm_sinMulSin_le t s ξ

end SymbolBasics

section SymbolMeasurable

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_kgFreq : Measurable (kgFreq (E := E)) := continuous_kgFreq.measurable

theorem measurable_kgCosSymbol (t : ℝ) : Measurable (kgCosSymbol (E := E) t) :=
  (continuous_kgCosSymbol t).measurable

theorem measurable_kgSinPhase (t : ℝ) : Measurable (kgSinPhase (E := E) t) :=
  (continuous_kgSinPhase t).measurable

theorem measurable_kgFreqInv : Measurable (kgFreqInv (E := E)) := continuous_kgFreqInv.measurable

private theorem measurable_cosMulCos (t s : ℝ) :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgCosSymbol s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgCosSymbol s)

private theorem measurable_sinMulSin (t s : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgSinPhase s ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgSinPhase s)

private theorem measurable_cosMulSin (t s : ℝ) :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgSinPhase s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgSinPhase s)

private theorem measurable_sinMulCos (t s : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgCosSymbol s ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgCosSymbol s)

end SymbolMeasurable

/-! ## The two scalar propagators -/

section Operators

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The cosine propagator on `L²`. -/
def kgCosOp (t : ℝ) : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  fourierMulCLM (measurable_kgCosSymbol (E := E) t) zero_le_one (norm_kgCosSymbol_le t)

/-- The sine propagator on `L²`, in energy coordinates. -/
def kgSinOp (t : ℝ) : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  fourierMulCLM (measurable_kgSinPhase (E := E) t) zero_le_one (norm_kgSinPhase_le t)

/-- Multiplication by the inverse frequency, the operator `⟨D⟩⁻¹`. -/
def kgFreqInvOp : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  fourierMulCLM (measurable_kgFreqInv (E := E)) zero_le_one norm_kgFreqInv_le

theorem norm_kgCosOp_le (t : ℝ) : ‖kgCosOp (E := E) t‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgSinOp_le (t : ℝ) : ‖kgSinOp (E := E) t‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgFreqInvOp_le : ‖kgFreqInvOp (E := E)‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgCosOp_apply_le (t : ℝ) (f : Lp (α := E) ℂ 2) : ‖kgCosOp t f‖ ≤ ‖f‖ := by
  have h := (kgCosOp (E := E) t).le_of_opNorm_le (norm_kgCosOp_le t) f
  rwa [one_mul] at h

theorem norm_kgSinOp_apply_le (t : ℝ) (f : Lp (α := E) ℂ 2) : ‖kgSinOp t f‖ ≤ ‖f‖ := by
  have h := (kgSinOp (E := E) t).le_of_opNorm_le (norm_kgSinOp_le t) f
  rwa [one_mul] at h

/-- **The cosine propagator is strongly continuous.** -/
theorem continuous_kgCosOp_apply (f : Lp (α := E) ℂ 2) :
    Continuous fun t : ℝ => kgCosOp t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  exact tendsto_fourierMulCLM_apply (l := nhds t₀) (fun t => measurable_kgCosSymbol (E := E) t)
    (measurable_kgCosSymbol (E := E) t₀) zero_le_one (fun t => norm_kgCosSymbol_le t)
    (norm_kgCosSymbol_le t₀) (fun ξ => (continuous_kgCosSymbol_time ξ).continuousAt) f

/-- **The sine propagator is strongly continuous.** -/
theorem continuous_kgSinOp_apply (f : Lp (α := E) ℂ 2) :
    Continuous fun t : ℝ => kgSinOp t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  exact tendsto_fourierMulCLM_apply (l := nhds t₀) (fun t => measurable_kgSinPhase (E := E) t)
    (measurable_kgSinPhase (E := E) t₀) zero_le_one (fun t => norm_kgSinPhase_le t)
    (norm_kgSinPhase_le t₀) (fun ξ => (continuous_kgSinPhase_time ξ).continuousAt) f

theorem kgCosOp_zero : kgCosOp (E := E) 0 = ContinuousLinearMap.id ℂ (Lp (α := E) ℂ 2) := by
  refine fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.cos (0 * kgFreq ξ) : ℝ) : ℂ) = 1
  rw [zero_mul, Real.cos_zero]
  norm_num

theorem kgSinOp_zero : kgSinOp (E := E) 0 = 0 := by
  refine fourierMulCLM_eq_zero _ _ _ (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.sin (0 * kgFreq ξ) : ℝ) : ℂ) = 0
  rw [zero_mul, Real.sin_zero]
  norm_num

theorem kgCosOp_eq (t : ℝ) : kgCosOp (E := E) t
    = fourierMulCLM (measurable_kgCosSymbol (E := E) t) zero_le_one (norm_kgCosSymbol_le t) := rfl

theorem kgSinOp_eq (t : ℝ) : kgSinOp (E := E) t
    = fourierMulCLM (measurable_kgSinPhase (E := E) t) zero_le_one (norm_kgSinPhase_le t) := rfl

section Addition

variable (t s : ℝ)

/-- **The addition law for the cosine propagator.** -/
theorem kgCosOp_add :
    kgCosOp (E := E) (t + s)
      = (kgCosOp t).comp (kgCosOp s) - (kgSinOp t).comp (kgSinOp s) := by
  have hcc := measurable_cosMulCos (E := E) t s
  have hss := measurable_sinMulSin (E := E) t s
  have hnss : Measurable fun ξ : E => -(kgSinPhase t ξ * kgSinPhase s ξ) := hss.neg
  have hc1 : (kgCosOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hcc zero_le_one (norm_cosMulCos_le t s) := by
    rw [kgCosOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hcc _ _ _ _ _ (norm_cosMulCos_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hc2 : (kgSinOp (E := E) t).comp (kgSinOp s)
      = fourierMulCLM hss zero_le_one (norm_sinMulSin_le t s) := by
    rw [kgSinOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hss _ _ _ _ _ (norm_sinMulSin_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hneg : fourierMulCLM hnss zero_le_one (norm_negSinMulSin_le t s)
      = -fourierMulCLM hss zero_le_one (norm_sinMulSin_le t s) :=
    fourierMulCLM_neg hss hnss zero_le_one (norm_sinMulSin_le t s) zero_le_one
      (norm_negSinMulSin_le t s) (Filter.Eventually.of_forall fun _ => rfl)
  have hadd : kgCosOp (E := E) (t + s)
      = fourierMulCLM hcc zero_le_one (norm_cosMulCos_le t s)
        + fourierMulCLM hnss zero_le_one (norm_negSinMulSin_le t s) := by
    rw [kgCosOp_eq]
    refine fourierMulCLM_add hcc hnss (measurable_kgCosSymbol (E := E) (t + s)) zero_le_one
      (norm_cosMulCos_le t s) zero_le_one (norm_negSinMulSin_le t s) zero_le_one
      (norm_kgCosSymbol_le (t + s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.cos ((t + s) * kgFreq ξ) : ℝ) : ℂ)
        = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
          + -(((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) : ℝ) : ℂ))
    rw [add_mul, Real.cos_add]
    push_cast
    ring
  rw [hadd, hneg, hc1, hc2, sub_eq_add_neg]

/-- **The addition law for the sine propagator.** -/
theorem kgSinOp_add :
    kgSinOp (E := E) (t + s)
      = (kgCosOp t).comp (kgSinOp s) + (kgSinOp t).comp (kgCosOp s) := by
  have hcs := measurable_cosMulSin (E := E) t s
  have hsc := measurable_sinMulCos (E := E) t s
  have hc1 : (kgCosOp (E := E) t).comp (kgSinOp s)
      = fourierMulCLM hcs zero_le_one (norm_cosMulSin_le t s) := by
    rw [kgCosOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hcs _ _ _ _ _ (norm_cosMulSin_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hc2 : (kgSinOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hsc zero_le_one (norm_sinMulCos_le t s) := by
    rw [kgSinOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hsc _ _ _ _ _ (norm_sinMulCos_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hadd : kgSinOp (E := E) (t + s)
      = fourierMulCLM hcs zero_le_one (norm_cosMulSin_le t s)
        + fourierMulCLM hsc zero_le_one (norm_sinMulCos_le t s) := by
    rw [kgSinOp_eq]
    refine fourierMulCLM_add hcs hsc (measurable_kgSinPhase (E := E) (t + s)) zero_le_one
      (norm_cosMulSin_le t s) zero_le_one (norm_sinMulCos_le t s) zero_le_one
      (norm_kgSinPhase_le (t + s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.sin ((t + s) * kgFreq ξ) : ℝ) : ℂ)
        = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) : ℝ) : ℂ)
          + ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
    rw [add_mul, Real.sin_add]
    push_cast
    ring
  rw [hadd, hc1, hc2]

end Addition

end Operators

/-! ## The propagator on the energy space -/

section Energy

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- The energy space of the Klein–Gordon evolution: the pair `(⟨D⟩u, ∂ₜu)`. -/
abbrev KGEnergy : Type _ := (Lp (α := E) ℂ 2) × (Lp (α := E) ℂ 2)

/-- **The free Klein–Gordon propagator on the energy space**, the rotation by `t⟨ξ⟩`. -/
def kgPropagator (t : ℝ) : KGEnergy E →L[ℂ] KGEnergy E :=
  ((kgCosOp t).coprod (kgSinOp t)).prod ((-(kgSinOp t)).coprod (kgCosOp t))

theorem kgPropagator_apply (t : ℝ) (v : KGEnergy E) :
    kgPropagator t v = (kgCosOp t v.1 + kgSinOp t v.2, -(kgSinOp t v.1) + kgCosOp t v.2) := rfl

theorem norm_kgPropagator_apply_le (t : ℝ) (v : KGEnergy E) : ‖kgPropagator t v‖ ≤ 2 * ‖v‖ := by
  have h1 : ‖v.1‖ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖v.2‖ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  rw [kgPropagator_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans (norm_add_le _ _) ?_
    have ha := norm_kgCosOp_apply_le t v.1
    have hb := norm_kgSinOp_apply_le t v.2
    linarith
  · refine le_trans (norm_add_le _ _) ?_
    have ha := norm_kgSinOp_apply_le t v.1
    have hb := norm_kgCosOp_apply_le t v.2
    rw [norm_neg]
    linarith

/-- **The propagator is bounded uniformly in time.** -/
theorem norm_kgPropagator_le (t : ℝ) : ‖kgPropagator (E := E) t‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_kgPropagator_apply_le t)

/-- **The propagator is strongly continuous.** -/
theorem continuous_kgPropagator_apply (v : KGEnergy E) :
    Continuous fun t : ℝ => kgPropagator t v := by
  have h1 : Continuous fun t : ℝ => kgCosOp t v.1 + kgSinOp t v.2 :=
    (continuous_kgCosOp_apply v.1).add (continuous_kgSinOp_apply v.2)
  have h2 : Continuous fun t : ℝ => -(kgSinOp t v.1) + kgCosOp t v.2 :=
    (continuous_kgSinOp_apply v.1).neg.add (continuous_kgCosOp_apply v.2)
  exact (h1.prodMk h2).congr fun t => (kgPropagator_apply t v).symm

/-- **The propagator is jointly continuous in the time and the vector.** -/
theorem continuous_kgPropagator_uncurry :
    Continuous fun q : ℝ × KGEnergy E => kgPropagator q.1 q.2 :=
  continuous_uncurry_of_strong norm_kgPropagator_le continuous_kgPropagator_apply

/-- **The propagator evaluated along continuous families is continuous.** -/
theorem continuous_kgPropagator_comp {ι : Type*} [TopologicalSpace ι] {r : ι → ℝ}
    {v : ι → KGEnergy E} (hr : Continuous r) (hv : Continuous v) :
    Continuous fun i => kgPropagator (r i) (v i) :=
  continuous_of_strong_comp norm_kgPropagator_le continuous_kgPropagator_apply hr hv

/-- **The propagator is a one-parameter group.** -/
theorem kgPropagator_add (t s : ℝ) :
    kgPropagator (E := E) (t + s) = (kgPropagator t).comp (kgPropagator s) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, kgPropagator_apply, kgCosOp_add, kgSinOp_add,
    sub_apply, add_apply, map_add, map_neg, Prod.mk.injEq]
  constructor <;> abel

/-- **The propagator starts at the identity.** -/
theorem kgPropagator_zero_apply (v : KGEnergy E) : kgPropagator 0 v = v := by
  rw [kgPropagator_apply, kgCosOp_zero, kgSinOp_zero]
  simp

end Energy

end GaloisForLFunctions.HTGeometry
