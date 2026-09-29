import GaloisForLFunctions.HTGeometry.ExponentialWallQuantileTransport
import GaloisForLFunctions.HTGeometry.GradedRowSynthesis
import GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit

/-!
# The quantile landing of the Burnol wall kernel

For a probability law `μ` on `ℝ` with quantile `Q_μ`, the kernel `κ(Q_μ u, Q_μ v)` on the unit
interval, `κ(x, y) = 8 (xy)^{3/2}/(x + y)³`, is the Gram kernel of the Burnol features
`v_x(r) = 2 x^{3/2} r e^{-xr}`: with the quantile synthesis `(S_μ f)(r) = ∫ v_{Q_μ u}(r) f(u) du`,

`A_μ = S_μ* S_μ`,  `‖S_μ‖²_HS = ∫ ‖v_{Q_μ u}‖² du ≤ 1`.

The landing is the conjugate `A_μ = U K_μ U*` of the kernel operator `K_μ` of `κ` on `L²(μ)` by the
quantile isometry `U f = f ∘ Q_μ`.  For the atomic wall laws `μ_d` the syntheses converge in
Hilbert–Schmidt norm to the exponential synthesis as `d → 0⁺`, since
`‖S_d - S_0‖²_HS = ∫ ‖v_{Q_d u} - v_{Q_0 u}‖² du` and `Q_d → Q_0` pointwise; hence the landings
converge in trace norm, `‖A_d - A_0‖₁ ≤ 2 ‖S_d - S_0‖_HS → 0`.  The limit `A_0` is positive with
trace one, `tr A_0² = ‖A_0‖²_HS = 16/35`, and `‖A_0‖ ≤ 4/√35 < 1`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Kernels pulled back in one variable -/

section OneVariable

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
  {μ : Measure α} {ν : Measure β} {m : Measure δ}

/-- A linear isometry `U f = f ∘ σ` satisfies `U* U = 1`. -/
theorem adjoint_compL2_comp_compL2 {σ : δ → α} (hσ : MeasurePreserving σ m μ) :
    adjoint (compL2 hσ) ∘L compL2 hσ = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  refine ext_inner_right ℂ fun g => ?_
  rw [comp_apply, adjoint_inner_left, id_apply]
  exact (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).inner_map_map f g

namespace SqIntKernel

/-- The kernel `k(y, σ u)` pulled back in its input variable. -/
def pullbackRight [SFinite μ] (k : SqIntKernel ν μ) {σ : δ → α} (hσ : MeasurePreserving σ m μ) :
    SqIntKernel ν m where
  toFun y u := k.toFun y (σ u)
  measurable := k.measurable.comp (measurable_id.prodMap hσ.measurable)
  energy_lt_top := by
    have hin : ∀ y, ∫⁻ u, ‖k.toFun y (σ u)‖ₑ ^ 2 ∂m = k.rowEnergy y := fun y =>
      hσ.lintegral_comp ((k.measurable_left y).enorm.pow_const 2)
    simp_rw [hin]
    exact k.energy_lt_top

theorem energy_pullbackRight [SFinite μ] (k : SqIntKernel ν μ) {σ : δ → α}
    (hσ : MeasurePreserving σ m μ) : (k.pullbackRight hσ).energy = k.energy :=
  lintegral_congr fun y => hσ.lintegral_comp ((k.measurable_left y).enorm.pow_const 2)

/-- The kernel `k(σ u, x)` pulled back in its output variable. -/
def pullbackLeft [SFinite μ] (k : SqIntKernel ν μ) {σ : δ → β} (hσ : MeasurePreserving σ m ν) :
    SqIntKernel m μ where
  toFun u x := k.toFun (σ u) x
  measurable := k.measurable.comp (hσ.measurable.prodMap measurable_id)
  energy_lt_top := by
    change ∫⁻ u, k.rowEnergy (σ u) ∂m < ∞
    rw [hσ.lintegral_comp k.measurable_rowEnergy]
    exact k.energy_lt_top

/-- **Output transport.**  `U K = K_σ` for `U f = f ∘ σ` acting on the output. -/
theorem compL2_comp_op_eq [SFinite μ] (k : SqIntKernel ν μ) {σ : δ → β}
    (hσ : MeasurePreserving σ m ν) : compL2 hσ ∘L k.op = (k.pullbackLeft hσ).op := by
  ext1 f
  refine Lp.ext ?_
  have h1 := compL2_coeFn hσ (k.op f)
  have h2 : ((k.op f : β → ℂ) ∘ σ) =ᵐ[m] (k.apply f) ∘ σ :=
    (k.op_coeFn f).comp_tendsto hσ.quasiMeasurePreserving.tendsto_ae
  have h3 := (k.pullbackLeft hσ).op_coeFn f
  filter_upwards [h1, h2, h3] with u h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3]
  rfl

/-- **Input transport.**  `K_σ = K U*` for the kernel `k(y, σ u)`. -/
theorem op_pullbackRight [SFinite μ] [SFinite ν] [SFinite m] (k : SqIntKernel ν μ) {σ : δ → α}
    (hσ : MeasurePreserving σ m μ) :
    (k.pullbackRight hσ).op = k.op ∘L ContinuousLinearMap.adjoint (compL2 hσ) := by
  refine ContinuousLinearMap.adjoint.injective ?_
  rw [(k.pullbackRight hσ).adjoint_op, ContinuousLinearMap.adjoint_comp, adjoint_adjoint,
    k.adjoint_op, compL2_comp_op_eq]
  exact op_congr _ (Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl)

/-- **Two-sided transport.**  `K_σ = U K U*` for the kernel `k(σ u, σ v)`. -/
theorem op_pullback [SFinite μ] [SFinite m] (k : SqIntKernel μ μ) {σ : δ → α}
    (hσ : MeasurePreserving σ m μ) :
    (k.pullback hσ).op = compL2 hσ ∘L k.op ∘L ContinuousLinearMap.adjoint (compL2 hσ) := by
  rw [← op_pullbackRight, compL2_comp_op_eq]
  exact op_congr _ (Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl)

theorem energy_pullback [SFinite μ] (k : SqIntKernel μ μ) {σ : δ → α}
    (hσ : MeasurePreserving σ m μ) : (k.pullback hσ).energy = k.energy := by
  have hin : ∀ u, ∫⁻ v, ‖k.toFun (σ u) (σ v)‖ₑ ^ 2 ∂m = k.rowEnergy (σ u) := fun u =>
    hσ.lintegral_comp ((k.measurable_left (σ u)).enorm.pow_const 2)
  change ∫⁻ u, ∫⁻ v, ‖k.toFun (σ u) (σ v)‖ₑ ^ 2 ∂m ∂m = k.energy
  simp_rw [hin]
  exact hσ.lintegral_comp k.measurable_rowEnergy

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := norm_sub_le a b
  nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-- The difference kernel `k₁ - k₂`. -/
def sub [SFinite μ] (k₁ k₂ : SqIntKernel ν μ) : SqIntKernel ν μ where
  toFun y x := k₁.toFun y x - k₂.toFun y x
  measurable := k₁.measurable.sub k₂.measurable
  energy_lt_top := by
    calc ∫⁻ y, ∫⁻ x, ‖k₁.toFun y x - k₂.toFun y x‖ₑ ^ 2 ∂μ ∂ν
        ≤ ∫⁻ y, 2 * (k₁.rowEnergy y + k₂.rowEnergy y) ∂ν := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ x, ‖k₁.toFun y x - k₂.toFun y x‖ₑ ^ 2 ∂μ
              ≤ ∫⁻ x, 2 * (‖k₁.toFun y x‖ₑ ^ 2 + ‖k₂.toFun y x‖ₑ ^ 2) ∂μ :=
                lintegral_mono fun x => enorm_sub_sq_le _ _
            _ = 2 * (k₁.rowEnergy y + k₂.rowEnergy y) := by
                rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left
                  ((k₁.measurable_left y).enorm.pow_const 2)]
                rfl
      _ = 2 * (k₁.energy + k₂.energy) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left k₁.measurable_rowEnergy]
          rfl
      _ < ∞ := ENNReal.mul_lt_top (by norm_num)
          (ENNReal.add_lt_top.mpr ⟨k₁.energy_lt_top, k₂.energy_lt_top⟩)

theorem op_sub [SFinite μ] (k₁ k₂ : SqIntKernel ν μ) : (k₁.sub k₂).op = k₁.op - k₂.op := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [(k₁.sub k₂).op_coeFn f, Lp.coeFn_sub (k₁.op f) (k₂.op f), k₁.op_coeFn f,
    k₂.op_coeFn f, k₁.ae_integrable f, k₂.ae_integrable f] with y h h' h1 h2 hi1 hi2
  rw [sub_apply, h', Pi.sub_apply, h1, h2, h]
  change ∫ x, (k₁.toFun y x - k₂.toFun y x) * f x ∂μ
    = ∫ x, k₁.toFun y x * f x ∂μ - ∫ x, k₂.toFun y x * f x ∂μ
  simp_rw [sub_mul]
  exact integral_sub hi1 hi2

end SqIntKernel

end OneVariable

/-! ## Burnol features over an arbitrary law -/

theorem burnolFeature_of_nonpos {x : ℝ} (hx : x ≤ 0) (r : ℝ) : burnolFeature r x = 0 := by
  rw [burnolFeature, Real.sqrt_eq_zero'.mpr hx]
  ring

theorem wallCubicKernel_of_nonpos_left {x : ℝ} (hx : x ≤ 0) (y : ℝ) : wallCubicKernel x y = 0 := by
  rw [wallCubicKernel, routePPrimitiveGammaJuliaStokesWallCubicKernel, Real.sqrt_eq_zero'.mpr hx]
  ring

theorem wallCubicKernel_of_nonpos_right (x : ℝ) {y : ℝ} (hy : y ≤ 0) : wallCubicKernel x y = 0 := by
  rw [wallCubicKernel, routePPrimitiveGammaJuliaStokesWallCubicKernel, Real.sqrt_eq_zero'.mpr hy]
  ring

/-- `⟨v_x, v_y⟩ = κ(x, y)` for all real `x, y`. -/
theorem integral_burnolFeature_mul_eq (x y : ℝ) :
    ∫ r in Ioi (0 : ℝ), burnolFeature r x * burnolFeature r y = wallCubicKernel x y := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · exact integral_burnolFeature_mul (by linarith)
    · simp only [burnolFeature_of_nonpos (not_lt.mp hy), mul_zero, integral_zero]
      exact (wallCubicKernel_of_nonpos_right x (not_lt.mp hy)).symm
  · simp only [burnolFeature_of_nonpos (not_lt.mp hx), zero_mul, integral_zero]
    exact (wallCubicKernel_of_nonpos_left (not_lt.mp hx) y).symm

theorem integrableOn_burnolFeature_mul (x y : ℝ) :
    IntegrableOn (fun r => burnolFeature r x * burnolFeature r y) (Ioi 0) := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · have h : IntegrableOn (fun r => 4 * (Real.sqrt x ^ 3 * Real.sqrt y ^ 3)
          * (r ^ 2 * Real.exp (-((x + y) * r)))) (Ioi 0) :=
        (integrableOn_pow_mul_exp_neg_mul_Ioi 2 (by linarith : 0 < x + y)).const_mul _
      exact h.congr_fun (fun r _ => burnolFeature_mul_left.symm) measurableSet_Ioi
    · simp only [burnolFeature_of_nonpos (not_lt.mp hy), mul_zero]
      exact integrableOn_zero
  · simp only [burnolFeature_of_nonpos (not_lt.mp hx), zero_mul]
    exact integrableOn_zero

theorem abs_wallCubicKernel_le_one (x y : ℝ) : |wallCubicKernel x y| ≤ 1 := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have h := routePPrimitiveGammaJuliaStokesWallCubicKernel_zero_le_one hx hy
      rw [wallCubicKernel]
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
    · rw [wallCubicKernel_of_nonpos_right x (le_of_lt (not_le.mp hy)), abs_zero]
      exact zero_le_one
  · rw [wallCubicKernel_of_nonpos_left (le_of_lt (not_le.mp hx)), abs_zero]
    exact zero_le_one

/-- The squared feature distance `‖v_x - v_y‖² = κ(x, x) - 2κ(x, y) + κ(y, y)`. -/
def burnolGap (x y : ℝ) : ℝ := wallCubicKernel x x - 2 * wallCubicKernel x y + wallCubicKernel y y

theorem burnolGap_le_four (x y : ℝ) : burnolGap x y ≤ 4 := by
  have h1 := abs_le.mp (abs_wallCubicKernel_le_one x x)
  have h2 := abs_le.mp (abs_wallCubicKernel_le_one x y)
  have h3 := abs_le.mp (abs_wallCubicKernel_le_one y y)
  rw [burnolGap]
  linarith [h1.2, h2.1, h3.2]

theorem measurable_wallCubicKernel_comp {γ : Type*} [MeasurableSpace γ] {f g : γ → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun t => wallCubicKernel (f t) (g t) := by
  have h : Measurable ((fun p : ℝ × ℝ => wallCubicKernel p.1 p.2) ∘ fun t => (f t, g t)) :=
    continuous_wallCubicKernel_sq.comp (hf.prodMk hg)
  exact h

theorem measurable_burnolGap_comp {γ : Type*} [MeasurableSpace γ] {f g : γ → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun t => burnolGap (f t) (g t) :=
  ((measurable_wallCubicKernel_comp hf hf).sub
    (measurable_const.mul (measurable_wallCubicKernel_comp hf hg))).add
    (measurable_wallCubicKernel_comp hg hg)

/-- **`‖v_x - v_y‖² = κ(x, x) - 2κ(x, y) + κ(y, y)`** in `L²((0, ∞), dr)`. -/
theorem lintegral_burnolFeature_sub_sq (x y : ℝ) :
    ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ) - ((burnolFeature r y : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure
      = ENNReal.ofReal (burnolGap x y) := by
  simp_rw [← Complex.ofReal_sub, enorm_ofReal_sq]
  have hxx := integrableOn_burnolFeature_mul x x
  have hxy := (integrableOn_burnolFeature_mul x y).const_mul 2
  have hyy := integrableOn_burnolFeature_mul y y
  have hsplit : ∀ r, (burnolFeature r x - burnolFeature r y) ^ 2
      = burnolFeature r x * burnolFeature r x - 2 * (burnolFeature r x * burnolFeature r y)
        + burnolFeature r y * burnolFeature r y := fun r => by ring
  have hint : IntegrableOn (fun r => (burnolFeature r x - burnolFeature r y) ^ 2) (Ioi 0) :=
    ((hxx.sub hxy).add hyy).congr_fun (fun r _ => (hsplit r).symm) measurableSet_Ioi
  rw [halfLineMeasure, setLIntegral_congr Ioi_ae_eq_Ici.symm,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun r => sq_nonneg _)]
  congr 1
  simp_rw [hsplit]
  have hsub : Integrable (fun r => burnolFeature r x * burnolFeature r x
      - 2 * (burnolFeature r x * burnolFeature r y)) (volume.restrict (Ioi 0)) := hxx.sub hxy
  rw [integral_add hsub hyy, integral_sub hxx hxy, integral_const_mul,
    integral_burnolFeature_mul_eq, integral_burnolFeature_mul_eq, integral_burnolFeature_mul_eq,
    burnolGap]

theorem lintegral_burnolFeature_sq_le (x : ℝ) :
    ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure ≤ 1 := by
  rcases lt_or_ge 0 x with hx | hx
  · exact (lintegral_burnolFeature_sq hx).le
  · simp [burnolFeature_of_nonpos hx]

section General

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- The Burnol feature kernel `(r, x) ↦ v_x(r)` from `L²(μ)` to `L²((0, ∞), dr)`. -/
def burnolKernelOf : SqIntKernel halfLineMeasure μ where
  toFun r x := (burnolFeature r x : ℂ)
  measurable := (Complex.continuous_ofReal.comp continuous_burnolFeature).measurable
  energy_lt_top := by
    have hm : Measurable (Function.uncurry fun (r x : ℝ) =>
        ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2) :=
      ((Complex.continuous_ofReal.comp continuous_burnolFeature).measurable.enorm).pow_const 2
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc ∫⁻ x, ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure ∂μ
        ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x => lintegral_burnolFeature_sq_le x
      _ < ∞ := by rw [lintegral_const, one_mul]; exact measure_lt_top _ _

theorem energy_burnolKernelOf_le : (burnolKernelOf μ).energy ≤ μ univ := by
  have hm : Measurable (Function.uncurry fun (r x : ℝ) =>
      ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2) :=
    ((Complex.continuous_ofReal.comp continuous_burnolFeature).measurable.enorm).pow_const 2
  change ∫⁻ r, ∫⁻ x, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂μ ∂halfLineMeasure ≤ μ univ
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ x, ∫⁻ r, ‖((burnolFeature r x : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure ∂μ
      ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun x => lintegral_burnolFeature_sq_le x
    _ = μ univ := by rw [lintegral_const, one_mul]

/-- The wall kernel `κ` on `L²(μ)`. -/
def wallKernelOf : SqIntKernel μ μ where
  toFun x y := (wallCubicKernel x y : ℂ)
  measurable := Complex.measurable_ofReal.comp continuous_wallCubicKernel_sq
  energy_lt_top := by
    have hpt : ∀ x y, ‖((wallCubicKernel x y : ℝ) : ℂ)‖ₑ ^ 2 ≤ 1 := fun x y => by
      rw [enorm_ofReal_sq, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (sq_le_one_iff_abs_le_one _ |>.mpr (abs_wallCubicKernel_le_one x y))
    calc ∫⁻ x, ∫⁻ y, ‖((wallCubicKernel x y : ℝ) : ℂ)‖ₑ ^ 2 ∂μ ∂μ
        ≤ ∫⁻ _, ∫⁻ _, 1 ∂μ ∂μ := lintegral_mono fun x => lintegral_mono fun y => hpt x y
      _ < ∞ := by
          simp only [lintegral_const, one_mul]
          exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)

/-- **`K_μ = G_μ* G_μ`** for the Burnol synthesis `G_μ` over `μ`. -/
theorem op_wallKernelOf :
    (wallKernelOf μ).op = adjoint (burnolKernelOf μ).op ∘L (burnolKernelOf μ).op := by
  rw [(burnolKernelOf μ).adjoint_op, ← SqIntKernel.op_comp]
  refine SqIntKernel.op_congr _ (Eventually.of_forall fun x => Eventually.of_forall fun y => ?_)
  change (wallCubicKernel x y : ℂ)
    = ∫ r, (starRingEnd ℂ) ((burnolFeature r x : ℝ) : ℂ) * ((burnolFeature r y : ℝ) : ℂ)
      ∂halfLineMeasure
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, halfLineMeasure, integral_Ici_eq_integral_Ioi,
    integral_burnolFeature_mul_eq]

end General

/-! ## The quantile landing -/

section Quantile

local instance factTwoNeTopQuantileLanding : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- **Inverse transform sampling.**  `Q_μ` pushes the uniform law on `(0, 1)` to `μ`. -/
theorem measurePreserving_quantile :
    MeasurePreserving (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) μ :=
  ⟨measurable_quantile _, map_quantile_eq _⟩

/-- The quantile Burnol kernel `(r, u) ↦ v_{Q_μ u}(r)`. -/
def quantileBurnolKernel : SqIntKernel halfLineMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (burnolKernelOf μ).pullbackRight (measurePreserving_quantile μ)

/-- The quantile synthesis `(S_μ f)(r) = ∫ v_{Q_μ u}(r) f(u) du`. -/
def quantileBurnolSynthesis :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  (quantileBurnolKernel μ).op

/-- The quantile landing kernel `(u, v) ↦ κ(Q_μ u, Q_μ v)`. -/
def quantileLandingKernel :
    SqIntKernel (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (wallKernelOf μ).pullback (measurePreserving_quantile μ)

/-- The quantile landing `A_μ` on `L²(0, 1)`. -/
def quantileLandingOp :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (quantileLandingKernel μ).op

/-- **(SCIN.13).**  The landing kernel is the quantile-pulled wall kernel. -/
theorem quantileLandingKernel_toFun {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    (quantileLandingKernel μ).toFun u v
      = ((routePPrimitiveGammaJuliaStokesWallQuantileKernel μ (u, v) : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesWallQuantileKernel, if_pos ⟨hu, hv⟩]
  rfl

/-- `A_μ = U K_μ U*` for the quantile isometry `U f = f ∘ Q_μ`. -/
theorem quantileLandingOp_eq_conj :
    quantileLandingOp μ = compL2 (measurePreserving_quantile μ) ∘L (wallKernelOf μ).op ∘L
      adjoint (compL2 (measurePreserving_quantile μ)) :=
  SqIntKernel.op_pullback _ _

/-- **`A_μ = S_μ* S_μ`.** -/
theorem quantileLandingOp_eq_adjoint_comp :
    quantileLandingOp μ = adjoint (quantileBurnolSynthesis μ) ∘L quantileBurnolSynthesis μ := by
  rw [quantileLandingOp_eq_conj, op_wallKernelOf, quantileBurnolSynthesis, quantileBurnolKernel,
    SqIntKernel.op_pullbackRight, ContinuousLinearMap.adjoint_comp, adjoint_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

theorem isHilbertSchmidt_quantileBurnolSynthesis :
    IsHilbertSchmidt (quantileBurnolSynthesis μ) :=
  (quantileBurnolKernel μ).isHilbertSchmidt_op

theorem hsNormSq_quantileBurnolSynthesis :
    ContinuousLinearMap.hsNormSq (quantileBurnolSynthesis μ)
      = (burnolKernelOf μ).energy.toReal := by
  rw [quantileBurnolSynthesis, SqIntKernel.hsNormSq_op, quantileBurnolKernel,
    SqIntKernel.energy_pullbackRight]

theorem hsNorm_quantileBurnolSynthesis_le :
    ContinuousLinearMap.hsNorm (quantileBurnolSynthesis μ) ≤ 1 := by
  rw [ContinuousLinearMap.hsNorm, hsNormSq_quantileBurnolSynthesis, Real.sqrt_le_one]
  have h := energy_burnolKernelOf_le μ
  rw [measure_univ] at h
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

theorem isPositive_quantileLandingOp : (quantileLandingOp μ).IsPositive := by
  rw [quantileLandingOp_eq_adjoint_comp]
  exact isPositive_adjoint_comp_self _

theorem memSchattenClass_one_quantileLandingOp : MemSchattenClass 1 (quantileLandingOp μ) := by
  rw [quantileLandingOp_eq_adjoint_comp]
  exact memSchattenClass_one_comp (isHilbertSchmidt_quantileBurnolSynthesis μ).adjoint
    (isHilbertSchmidt_quantileBurnolSynthesis μ)

theorem opTrace_quantileLandingOp :
    opTrace (quantileLandingOp μ) = ((burnolKernelOf μ).energy.toReal : ℂ) := by
  rw [quantileLandingOp_eq_adjoint_comp, opTrace_adjoint_comp_self,
    hsInner_self_eq_ofReal_hsNormSq', hsNormSq_quantileBurnolSynthesis]

end Quantile

/-! ## The exponential landing `A_0` -/

section Exponential

local instance factTwoNeTopExponentialLanding : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

local instance isProbabilityMeasure_expMeasure_one_landing : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The exponential landing is the comoving wall operator `A_0` of the quantile chart. -/
theorem quantileLandingOp_expMeasure_one :
    quantileLandingOp (expMeasure 1) = quantileWallOperator :=
  SqIntKernel.op_congr _ (Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl)

theorem energy_burnolKernelOf_expMeasure_one : (burnolKernelOf (expMeasure 1)).energy = 1 :=
  lintegral_lintegral_burnolFeature

/-- **(SCIN.17).**  `tr A_0 = 1`. -/
theorem opTrace_quantileWallOperator : opTrace quantileWallOperator = 1 := by
  rw [← quantileLandingOp_expMeasure_one, opTrace_quantileLandingOp,
    energy_burnolKernelOf_expMeasure_one, ENNReal.toReal_one, Complex.ofReal_one]

/-- **The comoving charge.**  `½ (tr A_0 - tr(-A_0)) = 1`. -/
theorem half_opTrace_quantileWallOperator_sub_neg :
    (1 / 2 : ℂ) * (opTrace quantileWallOperator - opTrace (-quantileWallOperator)) = 1 := by
  rw [← neg_one_smul ℂ quantileWallOperator, GaloisForLFunctions.HTGeometry.opTrace_smul,
    opTrace_quantileWallOperator]
  norm_num

theorem isPositive_quantileWallOperator : quantileWallOperator.IsPositive := by
  rw [← quantileLandingOp_expMeasure_one]
  exact isPositive_quantileLandingOp _

theorem memSchattenClass_one_quantileWallOperator : MemSchattenClass 1 quantileWallOperator := by
  rw [← quantileLandingOp_expMeasure_one]
  exact memSchattenClass_one_quantileLandingOp _

theorem adjoint_quantileWallOperator : adjoint quantileWallOperator = quantileWallOperator := by
  rw [← quantileLandingOp_expMeasure_one, quantileLandingOp_eq_adjoint_comp,
    ContinuousLinearMap.adjoint_comp, adjoint_adjoint]

theorem isHilbertSchmidt_quantileWallOperator : IsHilbertSchmidt quantileWallOperator :=
  quantileWallKernel.isHilbertSchmidt_op

/-- **(8A).**  `‖A_0‖²_HS = 16/35`. -/
theorem hsNormSq_quantileWallOperator :
    ContinuousLinearMap.hsNormSq quantileWallOperator = 16 / 35 := by
  rw [quantileWallOperator, SqIntKernel.hsNormSq_op, quantileWallKernel,
    SqIntKernel.energy_pullback, wallKernel_energy, ENNReal.toReal_ofReal (by norm_num)]

/-- **(8A).**  `tr A_0² = 16/35`. -/
theorem opTrace_quantileWallOperator_sq :
    opTrace (quantileWallOperator ∘L quantileWallOperator) = 16 / 35 := by
  have h : quantileWallOperator ∘L quantileWallOperator
      = adjoint quantileWallOperator ∘L quantileWallOperator := by
    rw [adjoint_quantileWallOperator]
  rw [h, opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq',
    hsNormSq_quantileWallOperator]
  push_cast
  ring

/-- **(8A).**  `‖A_0‖ ≤ 4/√35 < 1`: the comoving landing is a strict contraction. -/
theorem norm_quantileWallOperator_le : ‖quantileWallOperator‖ ≤ 4 / Real.sqrt 35 ∧
    4 / Real.sqrt 35 < 1 := by
  refine ⟨(opNorm_le_hsNorm isHilbertSchmidt_quantileWallOperator).trans_eq ?_, ?_⟩
  · rw [ContinuousLinearMap.hsNorm, hsNormSq_quantileWallOperator, Real.sqrt_div' _ (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num)), Real.lt_sqrt (by norm_num)]
    norm_num

/-- The exponential quantile synthesis is the Burnol synthesis read in the quantile chart. -/
theorem quantileBurnolSynthesis_expMeasure_one :
    quantileBurnolSynthesis (expMeasure 1)
      = burnolSynthesis ∘L adjoint (compL2 measurePreserving_quantile_expMeasure_one) := by
  rw [quantileBurnolSynthesis, quantileBurnolKernel, SqIntKernel.op_pullbackRight]
  rfl

/-- **(8A).**  The opposite-order product `S_0 S_0*` is the Burnol partner with kernel
`24 r s/(1 + r + s)⁴`. -/
theorem quantileBurnolSynthesis_comp_adjoint_expMeasure_one :
    quantileBurnolSynthesis (expMeasure 1) ∘L adjoint (quantileBurnolSynthesis (expMeasure 1))
      = partnerOperator := by
  rw [quantileBurnolSynthesis_expMeasure_one, ContinuousLinearMap.adjoint_comp, adjoint_adjoint,
    ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ _ (adjoint burnolSynthesis),
    adjoint_compL2_comp_compL2, ContinuousLinearMap.id_comp]
  rfl

end Exponential

/-! ## Trace-norm landing of the atomic wall laws -/

section WallLanding

local instance factTwoNeTopWallLanding : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

local instance isProbabilityMeasure_expMeasure_one_wallLanding :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The wall landing `A_d` of the atomic Stokes wall law `μ_d`. -/
def wallLandingOp (d : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  quantileLandingOp (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)

/-- `‖S_μ - S_ν‖²_HS = ∫ ‖v_{Q_μ u} - v_{Q_ν u}‖² du`. -/
theorem energy_quantileBurnolKernel_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ((quantileBurnolKernel μ).sub (quantileBurnolKernel ν)).energy
      = ∫⁻ u, ENNReal.ofReal (burnolGap (quantile μ u) (quantile ν u))
          ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hm : Measurable (Function.uncurry fun r u =>
      ‖((quantileBurnolKernel μ).sub (quantileBurnolKernel ν)).toFun r u‖ₑ ^ 2) :=
    ((quantileBurnolKernel μ).sub (quantileBurnolKernel ν)).measurable.enorm.pow_const 2
  rw [SqIntKernel.energy, lintegral_lintegral_swap hm.aemeasurable]
  exact lintegral_congr fun u => lintegral_burnolFeature_sub_sq _ _

/-- **Hilbert–Schmidt landing.**  `‖S_d - S_0‖_HS → 0` as `d → 0⁺`. -/
theorem tendsto_hsNorm_wallSynthesis_sub :
    Tendsto (fun d => ContinuousLinearMap.hsNorm
      (quantileBurnolSynthesis (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        - quantileBurnolSynthesis (expMeasure 1))) (𝓝[>] 0) (𝓝 0) := by
  have henergy : Tendsto (fun d => ((quantileBurnolKernel
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)).sub
        (quantileBurnolKernel (expMeasure 1))).energy) (𝓝[>] 0) (𝓝 0) := by
    simp_rw [energy_quantileBurnolKernel_sub]
    have hlim := tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun _ => (0 : ℝ≥0∞))
      (F := fun d u => ENNReal.ofReal (burnolGap
        (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) u)
        (quantile (expMeasure 1) u))) (fun _ => 4)
      (Eventually.of_forall fun d => (measurable_burnolGap_comp (measurable_quantile _)
        (measurable_quantile _)).ennreal_ofReal)
      (Eventually.of_forall fun d => Eventually.of_forall fun u => by
        rw [← ENNReal.ofReal_ofNat 4]
        exact ENNReal.ofReal_le_ofReal (burnolGap_le_four _ _))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hq : 0 < quantile (expMeasure 1) u := by
          rw [quantile_expMeasure_one hu.1 hu.2]
          exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hu.2) (by linarith [hu.1]))
        have hQ := tendsto_wallHalfLineQuantile_nhdsGT_zero hu.1 hu.2
        have hc := tendsto_const_nhds (x := quantile (expMeasure 1) u) (f := 𝓝[>] (0 : ℝ))
        have h1 := tendsto_routePPrimitiveGammaJuliaStokesWallCubicKernel hQ hQ hq hq
        have h2 := tendsto_routePPrimitiveGammaJuliaStokesWallCubicKernel hQ hc hq hq
        have h3 := ((h1.sub (h2.const_mul 2)).add
          (tendsto_const_nhds (x := wallCubicKernel (quantile (expMeasure 1) u)
            (quantile (expMeasure 1) u))))
        have h4 := ENNReal.tendsto_ofReal h3
        convert h4 using 2
        · rfl
        · rw [← wallCubicKernel]
          ring_nf
          simp)
    simpa using hlim
  have hreal : Tendsto (fun d => ((quantileBurnolKernel
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)).sub
        (quantileBurnolKernel (expMeasure 1))).energy.toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henergy
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hreal
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun d => ?_
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.hsNorm, quantileBurnolSynthesis, quantileBurnolSynthesis,
    ← SqIntKernel.op_sub, SqIntKernel.hsNormSq_op]

/-- **(SCIN.15).**  `‖A_d - A_0‖₁ → 0` as `d → 0⁺`. -/
theorem tendsto_traceNorm_wallLandingOp_sub :
    Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
      (wallLandingOp d - quantileWallOperator)) (𝓝[>] 0) (𝓝 0) := by
  have hup := tendsto_hsNorm_wallSynthesis_sub.const_mul 2
  rw [mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => traceNorm_nonneg _) fun d => ?_
  set μ := routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
  have h := traceNorm_adjoint_comp_self_sub_le (isHilbertSchmidt_quantileBurnolSynthesis μ)
    (isHilbertSchmidt_quantileBurnolSynthesis (expMeasure 1))
  rw [← quantileLandingOp_eq_adjoint_comp, ← quantileLandingOp_eq_adjoint_comp,
    quantileLandingOp_expMeasure_one] at h
  have h1 := hsNorm_quantileBurnolSynthesis_le μ
  have h2 := hsNorm_quantileBurnolSynthesis_le (expMeasure 1)
  have h3 := ContinuousLinearMap.hsNorm_nonneg
    (quantileBurnolSynthesis μ - quantileBurnolSynthesis (expMeasure 1))
  change traceNorm _ (quantileLandingOp μ - quantileWallOperator) ≤ _
  nlinarith

/-- The landings converge in Hilbert–Schmidt norm, `‖A_d - A_0‖_HS ≤ 2 ‖S_d - S_0‖_HS`. -/
theorem hsNorm_wallLandingOp_sub_le (d : ℝ) :
    ContinuousLinearMap.hsNorm (wallLandingOp d - quantileWallOperator)
      ≤ 2 * ContinuousLinearMap.hsNorm
        (quantileBurnolSynthesis (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
          - quantileBurnolSynthesis (expMeasure 1)) := by
  set μ := routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
  set S := quantileBurnolSynthesis μ
  set S₀ := quantileBurnolSynthesis (expMeasure 1)
  have hS := isHilbertSchmidt_quantileBurnolSynthesis μ
  have hS₀ := isHilbertSchmidt_quantileBurnolSynthesis (expMeasure 1)
  have hD := hS.sub hS₀
  have hsplit : wallLandingOp d - quantileWallOperator
      = adjoint S ∘L (S - S₀) + adjoint (S - S₀) ∘L S₀ := by
    rw [wallLandingOp, ← quantileLandingOp_expMeasure_one, quantileLandingOp_eq_adjoint_comp,
      quantileLandingOp_eq_adjoint_comp, map_sub, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
    abel
  have hA : ContinuousLinearMap.hsNorm (adjoint S ∘L (S - S₀))
      ≤ ContinuousLinearMap.hsNorm (S - S₀) := by
    have h := ContinuousLinearMap.hsNormSq_comp_left_le hD (adjoint S)
    have hn : ‖adjoint S‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact (opNorm_le_hsNorm hS).trans (hsNorm_quantileBurnolSynthesis_le μ)
    have hsq : ContinuousLinearMap.hsNormSq (adjoint S ∘L (S - S₀))
        ≤ ContinuousLinearMap.hsNormSq (S - S₀) := by
      have h0 := ContinuousLinearMap.hsNormSq_nonneg (S - S₀)
      have : ‖adjoint S‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (adjoint S)]
      nlinarith
    exact Real.sqrt_le_sqrt hsq
  have hB : ContinuousLinearMap.hsNorm (adjoint (S - S₀) ∘L S₀)
      ≤ ContinuousLinearMap.hsNorm (S - S₀) := by
    have h := ContinuousLinearMap.hsNormSq_comp_right_le hD.adjoint S₀
    have hn : ‖S₀‖ ≤ 1 :=
      (opNorm_le_hsNorm hS₀).trans (hsNorm_quantileBurnolSynthesis_le (expMeasure 1))
    have hsq : ContinuousLinearMap.hsNormSq (adjoint (S - S₀) ∘L S₀)
        ≤ ContinuousLinearMap.hsNormSq (S - S₀) := by
      have h0 := ContinuousLinearMap.hsNormSq_nonneg (adjoint (S - S₀))
      have : ‖S₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg S₀]
      rw [hD.hsNormSq_adjoint] at h h0
      nlinarith
    exact Real.sqrt_le_sqrt hsq
  rw [hsplit]
  refine (ContinuousLinearMap.hsNorm_add_le (hD.comp_left _) (hS₀.comp_left _)).trans ?_
  linarith

end WallLanding

end GaloisForLFunctions.HTGeometry
