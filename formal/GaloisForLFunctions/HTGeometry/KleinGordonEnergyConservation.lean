import GaloisForLFunctions.HTGeometry.KleinGordonL2Propagator

/-!
# Exact conservation of the free Klein–Gordon energy

The propagator bound `‖U(t)‖ ≤ 2` is enough to run a perturbation series, but it is not the truth:
the free evolution conserves the energy exactly. On the Fourier side the propagator is, frequency by
frequency, a rotation of `ℂ²`, and a rotation preserves `|a|² + |b|²`.

This file proves that at the operator level, with no integral computation. The ingredients are that a
multiplier with a real symbol is self-adjoint, and the two operator identities

`C_t² + S_t² = 1`,  `C_t S_t = S_t C_t`,

which are the Pythagorean identity and the commutativity of multiplication, read through Plancherel.
Expanding `‖C v₁ + S v₂‖² + ‖-S v₁ + C v₂‖²`, the cross terms cancel by commutativity and the
diagonal terms collapse by the Pythagorean identity.
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

/-! ## Bounds and measurability of the quadratic symbols -/

section SymbolSquares

variable {E : Type*} [NormedAddCommGroup E]

private theorem norm_cosSq_le (t : ℝ) (ξ : E) : ‖kgCosSymbol t ξ * kgCosSymbol t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le t ξ)

private theorem norm_sinSq_le (t : ℝ) (ξ : E) : ‖kgSinPhase t ξ * kgSinPhase t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le t ξ)

private theorem norm_sinCos_le (t : ℝ) (ξ : E) : ‖kgSinPhase t ξ * kgCosSymbol t ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le t ξ)

end SymbolSquares

section SymbolSquaresMeasurable

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

private theorem measurable_cosSq (t : ℝ) :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgCosSymbol t ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgCosSymbol t)

private theorem measurable_sinSq (t : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgSinPhase t ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgSinPhase t)

private theorem measurable_sinCos (t : ℝ) :
    Measurable fun ξ : E => kgSinPhase t ξ * kgCosSymbol t ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgCosSymbol t)

end SymbolSquaresMeasurable

section Main

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

/-- **The Pythagorean identity, at the operator level.** -/
theorem kgCosOp_sq_add_kgSinOp_sq (t : ℝ) :
    (kgCosOp (E := E) t).comp (kgCosOp t) + (kgSinOp t).comp (kgSinOp t)
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) := by
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
    have hreal : Real.cos (t * kgFreq ξ) * Real.cos (t * kgFreq ξ)
        + Real.sin (t * kgFreq ξ) * Real.sin (t * kgFreq ξ) = 1 := by
      have h0 := Real.sin_sq_add_cos_sq (t * kgFreq ξ)
      rw [pow_two, pow_two] at h0
      linarith
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, hreal,
      Complex.ofReal_one]
  have hid : fourierMulCLM hone zero_le_one honeb
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
    fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [hc1, hc2, ← hsum, hid]

/-- **The two propagators commute.** -/
theorem kgCosOp_comp_kgSinOp_comm (t : ℝ) :
    (kgCosOp (E := E) t).comp (kgSinOp t) = (kgSinOp t).comp (kgCosOp t) := by
  have hsc := measurable_sinCos (E := E) t
  have h1 : (kgCosOp (E := E) t).comp (kgSinOp t)
      = fourierMulCLM hsc zero_le_one (norm_sinCos_le t) := by
    rw [kgCosOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hsc _ _ _ _ _ (norm_sinCos_le t)
      (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have h2 : (kgSinOp (E := E) t).comp (kgCosOp t)
      = fourierMulCLM hsc zero_le_one (norm_sinCos_le t) := by
    rw [kgSinOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hsc _ _ _ _ _ (norm_sinCos_le t)
      (Filter.Eventually.of_forall fun _ => rfl)
  rw [h1, h2]

/-! ## The conserved energy -/

/-- The energy of a state of the Klein–Gordon evolution: the sum of the squared `L²` norms of the
two components. It is the square of the norm of the energy space. -/
def kgEnergy (v : KGEnergy E) : ℝ := ‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2

theorem kgEnergy_eq_norm_sq (v : KGEnergy E) : kgEnergy v = ‖v‖ ^ 2 :=
  (WithLp.prod_norm_sq_eq_of_L2 v).symm

theorem kgEnergy_nonneg (v : KGEnergy E) : 0 ≤ kgEnergy v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The Pythagorean identity, read on a single vector. -/
theorem norm_kgCosOp_sq_add_norm_kgSinOp_sq (t : ℝ) (v : Lp (α := E) ℂ 2) :
    ‖kgCosOp t v‖ ^ 2 + ‖kgSinOp t v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hsum : kgCosOp (E := E) t (kgCosOp t v) + kgSinOp t (kgSinOp t v) = v := by
    have happ := congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T v)
      (kgCosOp_sq_add_kgSinOp_sq (E := E) t)
    simpa using happ
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (kgCosOp (E := E) t v),
    norm_sq_eq_re_inner (𝕜 := ℂ) (kgSinOp (E := E) t v), inner_kgCosOp, inner_kgSinOp,
    ← map_add, ← inner_add_right, hsum, ← norm_sq_eq_re_inner (𝕜 := ℂ) v]

/-- The cross terms of the two components agree. -/
theorem inner_kgCosOp_kgSinOp_comm (t : ℝ) (a b : Lp (α := E) ℂ 2) :
    inner ℂ (kgCosOp t a) (kgSinOp t b) = inner ℂ (kgSinOp t a) (kgCosOp t b) := by
  rw [inner_kgCosOp, inner_kgSinOp]
  congr 1
  have happ := congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T b)
    (kgCosOp_comp_kgSinOp_comm (E := E) t)
  simpa using happ

/-- **The free Klein–Gordon evolution conserves the energy exactly.** -/
theorem kgEnergy_kgPropagator (t : ℝ) (v : KGEnergy E) :
    kgEnergy (kgPropagator t v) = kgEnergy v := by
  have h1 := norm_add_sq (𝕜 := ℂ) (kgCosOp (E := E) t v.fst) (kgSinOp t v.snd)
  have h2 := norm_add_sq (𝕜 := ℂ) (-(kgSinOp (E := E) t v.fst)) (kgCosOp t v.snd)
  rw [norm_neg, inner_neg_left, map_neg] at h2
  have hcross : RCLike.re (inner ℂ (kgCosOp (E := E) t v.fst) (kgSinOp t v.snd))
      = RCLike.re (inner ℂ (kgSinOp (E := E) t v.fst) (kgCosOp t v.snd)) :=
    congrArg RCLike.re (inner_kgCosOp_kgSinOp_comm (E := E) t v.fst v.snd)
  have hd1 := norm_kgCosOp_sq_add_norm_kgSinOp_sq (E := E) t v.fst
  have hd2 := norm_kgCosOp_sq_add_norm_kgSinOp_sq (E := E) t v.snd
  simp only [kgEnergy, kgPropagator_apply, kgPair_fst, kgPair_snd]
  rw [h1, h2]
  linarith

/-- **The propagator is an isometry of the energy space.** -/
theorem norm_kgPropagator_apply (t : ℝ) (v : KGEnergy E) : ‖kgPropagator t v‖ = ‖v‖ := by
  have h := kgEnergy_kgPropagator (E := E) t v
  rw [kgEnergy_eq_norm_sq, kgEnergy_eq_norm_sq] at h
  have h1 : (0 : ℝ) ≤ ‖kgPropagator (E := E) t v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h, h1, h2]

/-- **The propagator has operator norm at most one**, the sharp form of the uniform bound. -/
theorem norm_kgPropagator_le_one (t : ℝ) : ‖kgPropagator (E := E) t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul, norm_kgPropagator_apply]

end Main

end GaloisForLFunctions.HTGeometry
