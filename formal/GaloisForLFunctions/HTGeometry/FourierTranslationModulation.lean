import GaloisForLFunctions.HTGeometry.L2FourierIntegralBridge
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

noncomputable section

/-!
# Translation and modulation on `L²(ℝ)`

The unitary `L²` Fourier transform exchanges translation for modulation:

```text
𝖥(f(· + a))(ξ) = e^{2πi a ξ} 𝖥f(ξ).
```

Both sides are continuous linear maps of `f`, so it is enough to check the identity on the dense
image of Schwartz space.  There the `L²` transform is the convergent Fourier integral, where the
identity is a change of variables.
-/

open MeasureTheory FourierTransform Complex

namespace GaloisForLFunctions.HTGeometry

/-- Right translation `f ↦ f(· + a)` on `L²(ℝ)`. -/
def translateL2 (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + a)
    (measurePreserving_add_right volume a)

theorem coeFn_translateL2 (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (translateL2 a f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (f : ℝ → ℂ) (x + a) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)

/-- The modulation symbol `ξ ↦ e^{2πi a ξ}`. -/
def modulationSymbol (a ξ : ℝ) : ℂ := Complex.exp ((2 * Real.pi * (a * ξ) : ℝ) * Complex.I)

theorem measurable_modulationSymbol (a : ℝ) : Measurable (modulationSymbol a) := by
  unfold modulationSymbol
  fun_prop

theorem norm_modulationSymbol (a ξ : ℝ) : ‖modulationSymbol a ξ‖ = 1 := by
  rw [modulationSymbol, Complex.norm_exp]
  simp

theorem norm_modulationSymbol_le (a ξ : ℝ) : ‖modulationSymbol a ξ‖ ≤ 1 :=
  le_of_eq (norm_modulationSymbol a ξ)

/-- Multiplication by the modulation symbol on `L²(ℝ)`. -/
def modulationMul (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (measurable_modulationSymbol a)
    (by norm_num : (0:ℝ) ≤ 1) (norm_modulationSymbol_le a)

theorem coeFn_modulationMul (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (modulationMul a f : ℝ → ℂ) =ᵐ[volume] fun ξ : ℝ => modulationSymbol a ξ * (f : ℝ → ℂ) ξ :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) (measurable_modulationSymbol a)
    (by norm_num) (norm_modulationSymbol_le a) f

theorem fourierChar_eq_modulationSymbol (a ξ : ℝ) :
    ((Real.fourierChar (a * ξ) : Circle) : ℂ) = modulationSymbol a ξ := by
  rw [Real.fourierChar_apply, modulationSymbol]

/-- The classical Fourier integral turns translation into modulation. -/
theorem fourierIntegral_comp_add (a : ℝ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => g (x + a)) ξ = modulationSymbol a ξ * 𝓕 g ξ := by
  have h := VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
    Real.fourierChar volume (innerₗ ℝ) g a
  have happ := congrFun h ξ
  have hL : ((innerₗ ℝ) a) ξ = a * ξ := by
    show ((innerₛₗ ℝ) a) ξ = a * ξ
    rw [innerₛₗ_apply_apply, RCLike.inner_apply]
    simp [mul_comm]
  rw [hL] at happ
  have hlhs : VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (g ∘ fun v : ℝ => v + a) ξ = 𝓕 (fun x : ℝ => g (x + a)) ξ := rfl
  have hrhs : VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g ξ = 𝓕 g ξ := rfl
  rw [hlhs, hrhs] at happ
  rw [happ, Circle.smul_def, smul_eq_mul, fourierChar_eq_modulationSymbol]

/-- The `L²` Fourier transform of an integrable representative is its Fourier integral. -/
theorem coeFn_fourierTransform_eq_fourierIntegral (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) :
    ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
  refine (coeFn_fourierTransform_ae_eq_fourierIntegral f hf).trans ?_
  filter_upwards with ξ
  rw [Real.Lp.fourierTransform_apply]
  exact Real.fourier_congr_ae (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)) ξ

/-- **Translation-modulation exchange, integrable case.** -/
theorem fourierTransform_translateL2_of_integrable (a : ℝ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : Integrable (f : ℝ → ℂ)) :
    (𝓕 (translateL2 a f) : Lp ℂ 2 (volume : Measure ℝ))
      = modulationMul a (𝓕 f) := by
  have hint : Integrable ((translateL2 a f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    ((hf.comp_add_right a).congr (coeFn_translateL2 a f).symm)
  refine MeasureTheory.Lp.ext ?_
  have h1 := coeFn_fourierTransform_eq_fourierIntegral _ hint
  have h2 := coeFn_fourierTransform_eq_fourierIntegral f hf
  have h3 := coeFn_modulationMul a (𝓕 f)
  filter_upwards [h1, h2, h3] with ξ k1 k2 k3
  rw [k1, k3]
  have hcong : 𝓕 ((translateL2 a f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ
      = 𝓕 (fun x : ℝ => (f : ℝ → ℂ) (x + a)) ξ :=
    Real.fourier_congr_ae (coeFn_translateL2 a f) ξ
  rw [hcong, fourierIntegral_comp_add, k2]

/-- **Translation-modulation exchange on `L²(ℝ)`.**  The Fourier transform of a translate is the
modulated transform.  Both sides are continuous and agree on the dense image of Schwartz space,
where the transform is a convergent integral. -/
theorem fourierTransform_translateL2 (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (𝓕 (translateL2 a f) : Lp ℂ 2 (volume : Measure ℝ)) = modulationMul a (𝓕 f) := by
  have hA : Continuous fun g : Lp ℂ 2 (volume : Measure ℝ) =>
      (𝓕 (translateL2 a g) : Lp ℂ 2 (volume : Measure ℝ)) :=
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (translateL2 a).continuous
  have hB : Continuous fun g : Lp ℂ 2 (volume : Measure ℝ) =>
      modulationMul a (𝓕 g) :=
    (modulationMul a).continuous.comp (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  have hdense : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ))) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  have heq : Set.EqOn (fun g : Lp ℂ 2 (volume : Measure ℝ) =>
        (𝓕 (translateL2 a g) : Lp ℂ 2 (volume : Measure ℝ)))
      (fun g : Lp ℂ 2 (volume : Measure ℝ) => modulationMul a (𝓕 g))
      (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ))) := by
    rintro _ ⟨φ, rfl⟩
    refine fourierTransform_translateL2_of_integrable a ?_
    exact φ.integrable.congr (SchwartzMap.coeFn_toLp φ 2 (volume : Measure ℝ)).symm
  exact congrFun (Continuous.ext_on hdense hA hB heq) f


/-! ## Group laws -/

theorem modulationSymbol_add (a b ξ : ℝ) :
    modulationSymbol (a + b) ξ = modulationSymbol a ξ * modulationSymbol b ξ := by
  rw [modulationSymbol, modulationSymbol, modulationSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem modulationSymbol_zero (ξ : ℝ) : modulationSymbol 0 ξ = 1 := by
  rw [modulationSymbol]
  norm_num

theorem conj_modulationSymbol (a ξ : ℝ) :
    (starRingEnd ℂ) (modulationSymbol a ξ) = modulationSymbol (-a) ξ := by
  rw [modulationSymbol, modulationSymbol, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem modulationMul_modulationMul (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modulationMul a (modulationMul b f) = modulationMul (a + b) f := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_modulationMul a (modulationMul b f), coeFn_modulationMul b f,
    coeFn_modulationMul (a + b) f] with ξ h1 h2 h3
  rw [h1, h2, h3, modulationSymbol_add, mul_assoc]

theorem modulationMul_zero_apply (f : Lp ℂ 2 (volume : Measure ℝ)) : modulationMul 0 f = f := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_modulationMul 0 f] with ξ h1
  rw [h1, modulationSymbol_zero, one_mul]

theorem modulationMul_neg_modulationMul (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modulationMul (-a) (modulationMul a f) = f := by
  rw [modulationMul_modulationMul, neg_add_cancel, modulationMul_zero_apply]

theorem translateL2_translateL2 (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    translateL2 b (translateL2 a f) = translateL2 (a + b) f := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_translateL2 b (translateL2 a f), coeFn_translateL2 (a + b) f,
    (coeFn_translateL2 a f).comp_tendsto
      (measurePreserving_add_right (volume : Measure ℝ) b).quasiMeasurePreserving.tendsto_ae]
    with x h1 h2 h3
  rw [h1, h2]
  have h3' : (translateL2 a f : ℝ → ℂ) (x + b) = (f : ℝ → ℂ) (x + b + a) := h3
  rw [h3']
  ring_nf

theorem translateL2_neg_translateL2 (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    translateL2 (-a) (translateL2 a f) = f := by
  rw [translateL2_translateL2, add_neg_cancel]
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_translateL2 (0 : ℝ) f] with x h1
  rw [h1, add_zero]


end GaloisForLFunctions.HTGeometry
