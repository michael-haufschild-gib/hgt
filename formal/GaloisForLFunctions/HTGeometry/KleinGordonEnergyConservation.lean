import GaloisForLFunctions.HTGeometry.KleinGordonL2Propagator

/-!
# Exact conservation of the free Klein–Gordon energy

The propagator bound `‖U(t)‖ ≤ 2` is enough to run a perturbation series, but it is not the truth:
the free evolution conserves the energy exactly. On the Fourier side the propagator is, frequency by
frequency, a rotation of `ℂ²`, and a rotation preserves `|a|² + |b|²`.

This file proves that at the operator level, with no integral computation. The two ingredients are
that a multiplier with a real symbol is self-adjoint, and the two operator identities

`C_t² + S_t² = 1`,  `C_t S_t = S_t C_t`,

which are the Pythagorean identity and the commutativity of multiplication, read through Plancherel.
Expanding `‖C v₁ + S v₂‖² + ‖-S v₁ + C v₂‖²` by the parallelogram expansion, the cross terms cancel
by commutativity and the diagonal terms collapse by the Pythagorean identity.
-/

noncomputable section

namespace MeasureTheory

section Adjoint

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **A multiplication operator with a real symbol is self-adjoint on `L²`.** -/
theorem inner_lpBoundedMulCLM_real {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hreal : ∀ x, (starRingEnd ℂ) (φ x) = φ x) (f g : Lp ℂ 2 μ) :
    inner ℂ (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f) g
      = inner ℂ f (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, hreal x]
  ring

end Adjoint

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Self-adjointness of a real Fourier multiplier -/

theorem inner_fourierL2 (f g : Lp (α := E) ℂ 2) :
    inner ℂ (fourierL2 E f) (fourierL2 E g) = inner ℂ f g :=
  Lp.inner_fourier_eq f g

/-- **A Fourier multiplier with a real symbol is self-adjoint on `L²`.** -/
theorem inner_fourierMulCLM_real {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hreal : ∀ ξ, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (f g : Lp (α := E) ℂ 2) :
    inner ℂ (fourierMulCLM hφ hC0 hC f) g = inner ℂ f (fourierMulCLM hφ hC0 hC g) := by
  have hleft : inner ℂ (fourierMulCLM hφ hC0 hC f) g
      = inner ℂ (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC (fourierL2 E f))
        (fourierL2 E g) := by
    rw [← inner_fourierL2 (fourierMulCLM hφ hC0 hC f) g, fourierMulCLM_apply,
      fourierL2_fourierL2inv]
  have hright : inner ℂ f (fourierMulCLM hφ hC0 hC g)
      = inner ℂ (fourierL2 E f)
        (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC (fourierL2 E g)) := by
    rw [← inner_fourierL2 f (fourierMulCLM hφ hC0 hC g), fourierMulCLM_apply,
      fourierL2_fourierL2inv]
  rw [hleft, hright]
  exact inner_lpBoundedMulCLM_real hφ hC0 hC hreal _ _

/-! ## The two scalar propagators are self-adjoint and commute -/

theorem inner_kgCosOp (t : ℝ) (f g : Lp (α := E) ℂ 2) :
    inner ℂ (kgCosOp t f) g = inner ℂ f (kgCosOp t g) := by
  rw [kgCosOp_eq]
  refine inner_fourierMulCLM_real _ _ _ (fun ξ => ?_) f g
  show (starRingEnd ℂ) ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.conj_ofReal _

theorem inner_kgSinOp (t : ℝ) (f g : Lp (α := E) ℂ 2) :
    inner ℂ (kgSinOp t f) g = inner ℂ f (kgSinOp t g) := by
  rw [kgSinOp_eq]
  refine inner_fourierMulCLM_real _ _ _ (fun ξ => ?_) f g
  show (starRingEnd ℂ) ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) = ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
  exact Complex.conj_ofReal _

private theorem measurable_cosSq (t : ℝ) :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgCosSymbol t ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgCosSymbol t)

private theorem measurable_sinSq (t : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgSinPhase t ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgSinPhase t)

private theorem measurable_cosSin (t : ℝ) :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgSinPhase t ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgSinPhase t)

private theorem measurable_sinCos (t : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgCosSymbol t ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgCosSymbol t)

private theorem norm_cosSq_le (t : ℝ) (ξ : E) : ‖kgCosSymbol t ξ * kgCosSymbol t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le t ξ)

private theorem norm_sinSq_le (t : ℝ) (ξ : E) : ‖kgSinPhase t ξ * kgSinPhase t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le t ξ)

private theorem norm_cosSin_le (t : ℝ) (ξ : E) : ‖kgCosSymbol t ξ * kgSinPhase t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le t ξ)

private theorem norm_sinCos_le (t : ℝ) (ξ : E) : ‖kgSinPhase t ξ * kgCosSymbol t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le t ξ)

/-- **The Pythagorean identity, at the operator level.** -/
theorem kgCosOp_sq_add_kgSinOp_sq (t : ℝ) :
    (kgCosOp (E := E) t).comp (kgCosOp t) + (kgSinOp t).comp (kgSinOp t)
      = ContinuousLinearMap.id ℂ (Lp (α := E) ℂ 2) := by
  have hcc := measurable_cosSq (E := E) t
  have hss := measurable_sinSq (E := E) t
  have hone : Measurable fun _ : E => (1 : ℂ) := measurable_const
  have honeb : ∀ _ξ : E, ‖(1 : ℂ)‖ ≤ 1 := fun _ => le_of_eq norm_one
  have hc1 : (kgCosOp (E := E) t).comp (kgCosOp t)
      = fourierMulCLM hcc zero_le_one (norm_cosSq_le t) := by
    rw [kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hcc _ _ _ _ _ (norm_cosSq_le t)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hc2 : (kgSinOp (E := E) t).comp (kgSinOp t)
      = fourierMulCLM hss zero_le_one (norm_sinSq_le t) := by
    rw [kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hss _ _ _ _ _ (norm_sinSq_le t)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsum : fourierMulCLM hone zero_le_one honeb
      = fourierMulCLM hcc zero_le_one (norm_cosSq_le t)
        + fourierMulCLM hss zero_le_one (norm_sinSq_le t) := by
    refine fourierMulCLM_add hcc hss hone zero_le_one (norm_cosSq_le t) zero_le_one
      (norm_sinSq_le t) zero_le_one honeb (Filter.Eventually.of_forall fun ξ => ?_)
    show (1 : ℂ)
        = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
          + ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
    have h := Real.sin_sq_add_cos_sq (t * kgFreq ξ)
    have hc : (Real.cos (t * kgFreq ξ)) ^ 2 + (Real.sin (t * kgFreq ξ)) ^ 2 = 1 := by linarith
    have hcast : ((((Real.cos (t * kgFreq ξ)) ^ 2 + (Real.sin (t * kgFreq ξ)) ^ 2 : ℝ)) : ℂ)
        = ((1 : ℝ) : ℂ) := by rw [hc]
    push_cast at hcast
    rw [← hcast]
    ring
  have hid : fourierMulCLM hone zero_le_one honeb
      = ContinuousLinearMap.id ℂ (Lp (α := E) ℂ 2) :=
    fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [hc1, hc2, ← hsum, hid]

/-- **The two propagators commute.** -/
theorem kgCosOp_comp_kgSinOp_comm (t : ℝ) :
    (kgCosOp (E := E) t).comp (kgSinOp t) = (kgSinOp t).comp (kgCosOp t) := by
  have hcs := measurable_cosSin (E := E) t
  have hsc := measurable_sinCos (E := E) t
  have h1 : (kgCosOp (E := E) t).comp (kgSinOp t)
      = fourierMulCLM hcs zero_le_one (norm_cosSin_le t) := by
    rw [kgCosOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hcs _ _ _ _ _ (norm_cosSin_le t)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgSinOp (E := E) t).comp (kgCosOp t)
      = fourierMulCLM hsc zero_le_one (norm_sinCos_le t) := by
    rw [kgSinOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hsc _ _ _ _ _ (norm_sinCos_le t)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h3 : fourierMulCLM hcs zero_le_one (norm_cosSin_le t)
      = fourierMulCLM hsc zero_le_one (norm_sinCos_le t) := by
    refine fourierMulCLM_comp (φ := kgCosSymbol (E := E) t) (ψ := kgSinPhase (E := E) t)
      (measurable_kgCosSymbol t) (measurable_kgSinPhase t) hsc zero_le_one
      (norm_kgCosSymbol_le t) zero_le_one (norm_kgSinPhase_le t) zero_le_one (norm_sinCos_le t)
      (Filter.Eventually.of_forall fun ξ => mul_comm _ _) |>.symm.trans ?_
    rw [← kgCosOp_eq, ← kgSinOp_eq, h1]
  rw [h1, h2, h3]

/-! ## The conserved energy -/

/-- The energy of a state of the Klein–Gordon evolution: the sum of the squared `L²` norms of the
two components. -/
def kgEnergy (v : KGEnergy E) : ℝ := ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2

theorem kgEnergy_nonneg (v : KGEnergy E) : 0 ≤ kgEnergy v := by
  have h1 : (0 : ℝ) ≤ ‖v.1‖ ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v.2‖ ^ 2 := sq_nonneg _
  exact add_nonneg h1 h2

/-- The Pythagorean identity, read on a single vector. -/
theorem norm_kgCosOp_sq_add_norm_kgSinOp_sq (t : ℝ) (v : Lp (α := E) ℂ 2) :
    ‖kgCosOp t v‖ ^ 2 + ‖kgSinOp t v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hc : ‖kgCosOp (E := E) t v‖ ^ 2 = RCLike.re (inner ℂ v (kgCosOp t (kgCosOp t v))) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_kgCosOp]
  have hs : ‖kgSinOp (E := E) t v‖ ^ 2 = RCLike.re (inner ℂ v (kgSinOp t (kgSinOp t v))) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_kgSinOp]
  have hsum : kgCosOp (E := E) t (kgCosOp t v) + kgSinOp t (kgSinOp t v) = v := by
    have h := kgCosOp_sq_add_kgSinOp_sq (E := E) t
    have happ := congrArg
      (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T v) h
    simpa using happ
  rw [hc, hs, ← map_add, ← inner_add_right, hsum, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- The cross terms of the two components are equal. -/
theorem inner_kgCosOp_kgSinOp_comm (t : ℝ) (a b : Lp (α := E) ℂ 2) :
    inner ℂ (kgCosOp t a) (kgSinOp t b) = inner ℂ (kgSinOp t a) (kgCosOp t b) := by
  rw [inner_kgCosOp, inner_kgSinOp]
  congr 1
  have h := kgCosOp_comp_kgSinOp_comm (E := E) t
  have happ := congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T b) h
  simpa using happ

/-- **The free Klein–Gordon evolution conserves the energy exactly.** -/
theorem kgEnergy_kgPropagator (t : ℝ) (v : KGEnergy E) :
    kgEnergy (kgPropagator t v) = kgEnergy v := by
  rw [kgPropagator_apply, kgEnergy, kgEnergy]
  have h1 : ‖kgCosOp (E := E) t v.1 + kgSinOp t v.2‖ ^ 2
      = ‖kgCosOp (E := E) t v.1‖ ^ 2
        + 2 * RCLike.re (inner ℂ (kgCosOp (E := E) t v.1) (kgSinOp t v.2))
        + ‖kgSinOp (E := E) t v.2‖ ^ 2 := norm_add_sq (𝕜 := ℂ) _ _
  have h2 : ‖-(kgSinOp (E := E) t v.1) + kgCosOp t v.2‖ ^ 2
      = ‖kgSinOp (E := E) t v.1‖ ^ 2
        - 2 * RCLike.re (inner ℂ (kgSinOp (E := E) t v.1) (kgCosOp t v.2))
        + ‖kgCosOp (E := E) t v.2‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), norm_neg, inner_neg_left]
    simp only [map_neg, RCLike.re_to_complex]
    ring
  have hcross := inner_kgCosOp_kgSinOp_comm (E := E) t v.1 v.2
  have hd1 := norm_kgCosOp_sq_add_norm_kgSinOp_sq (E := E) t v.1
  have hd2 := norm_kgCosOp_sq_add_norm_kgSinOp_sq (E := E) t v.2
  rw [h1, h2, hcross]
  linarith

end GaloisForLFunctions.HTGeometry
