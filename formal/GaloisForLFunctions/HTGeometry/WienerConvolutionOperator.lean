import GaloisForLFunctions.HTGeometry.WienerWeightedMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Convolution as a bounded operator on weighted frequency data

The evolution with a potential is a convolution equation on the frequency side, so the space the
iteration runs in must be one where convolution by a fixed density is a bounded operator. The choice
here is the weighted sup-norm space: `G` bounded continuous, standing for the density
`⟨ξ⟩⁻ᴺ G(ξ)`. It is a Banach space for free — it *is* the space of bounded continuous functions —
and Peetre's inequality makes convolution bounded on it with no integral inequality beyond the
triangle inequality for the integral:

`⟨ξ⟩ᴺ |(a ⋆ g)(ξ)| ≤ √2ᴺ (∫ ⟨η⟩ᴺ |a(η)| dη) · sup ⟨·⟩ᴺ|g|`.

The weight is carried by the operator rather than by the space, which is what keeps the analysis
elementary: no `Lᵖ` quotients, no Fubini, and the elements are genuine functions.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Admissible convolution densities -/

/-- A density integrable against the weight of order `N`: the class of potentials whose transform
convolves boundedly. -/
structure WienerDensity (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (N : ℕ) where
  /-- The density itself. -/
  toFun : E → ℂ
  /-- It is measurable. -/
  aestronglyMeasurable : AEStronglyMeasurable toFun (volume : Measure E)
  /-- And integrable against the weight of order `N`. -/
  integrable_weight : Integrable (fun η => kgFreq η ^ N * ‖toFun η‖) (volume : Measure E)

namespace WienerDensity

variable {N : ℕ}

instance : CoeFun (WienerDensity E N) fun _ => E → ℂ := ⟨toFun⟩

/-- The weighted `L¹` norm of the density. -/
noncomputable def norm' (a : WienerDensity E N) : ℝ := ∫ η, kgFreq η ^ N * ‖a η‖

theorem norm'_nonneg (a : WienerDensity E N) : 0 ≤ a.norm' := by
  refine integral_nonneg fun η => ?_
  exact mul_nonneg (pow_nonneg (kgFreq_pos η).le N) (norm_nonneg _)

end WienerDensity

/-! ## The convolution integrand -/

variable {N : ℕ}

/-- The integrand of the weighted convolution: the weight ratio makes the operator act on the
representative `G` of the density `⟨ξ⟩⁻ᴺ G(ξ)`. -/
noncomputable def kgConvIntegrand (N : ℕ) (a : E → ℂ) (G : E →ᵇ ℂ) (ξ η : E) : ℂ :=
  a η * ((kgFreq ξ ^ N / kgFreq (ξ - η) ^ N : ℝ) : ℂ) * G (ξ - η)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgConvIntegrand_le (a : E → ℂ) (G : E →ᵇ ℂ) (ξ η : E) :
    ‖kgConvIntegrand N a G ξ η‖ ≤ Real.sqrt 2 ^ N * ‖G‖ * (kgFreq η ^ N * ‖a η‖) := by
  have hden : 0 < kgFreq (ξ - η) ^ N := pow_pos (kgFreq_pos _) N
  have hratio : kgFreq ξ ^ N / kgFreq (ξ - η) ^ N ≤ Real.sqrt 2 ^ N * kgFreq η ^ N := by
    rw [div_le_iff₀ hden]
    have hp := kgFreq_pow_le_peetre N ξ η
    calc kgFreq ξ ^ N ≤ Real.sqrt 2 ^ N * (kgFreq (ξ - η) ^ N * kgFreq η ^ N) := hp
      _ = Real.sqrt 2 ^ N * kgFreq η ^ N * kgFreq (ξ - η) ^ N := by ring
  have hratio_nonneg : 0 ≤ kgFreq ξ ^ N / kgFreq (ξ - η) ^ N :=
    div_nonneg (pow_nonneg (kgFreq_pos ξ).le N) hden.le
  have hG : ‖G (ξ - η)‖ ≤ ‖G‖ := G.norm_coe_le_norm _
  have hw : (0 : ℝ) ≤ Real.sqrt 2 ^ N * kgFreq η ^ N :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) (pow_nonneg (kgFreq_pos η).le N)
  calc ‖kgConvIntegrand N a G ξ η‖
      = ‖a η‖ * (kgFreq ξ ^ N / kgFreq (ξ - η) ^ N) * ‖G (ξ - η)‖ := by
        rw [kgConvIntegrand, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hratio_nonneg]
    _ ≤ ‖a η‖ * (Real.sqrt 2 ^ N * kgFreq η ^ N) * ‖G‖ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hratio (norm_nonneg _)) hG (norm_nonneg _) ?_
        exact mul_nonneg (norm_nonneg _) hw
    _ = Real.sqrt 2 ^ N * ‖G‖ * (kgFreq η ^ N * ‖a η‖) := by ring

theorem aestronglyMeasurable_kgConvIntegrand (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    AEStronglyMeasurable (kgConvIntegrand N a G ξ) (volume : Measure E) := by
  have hcont : Continuous fun η : E => ((kgFreq ξ ^ N / kgFreq (ξ - η) ^ N : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    refine continuous_const.div ((continuous_kgFreq.comp (continuous_const.sub continuous_id)).pow N)
      fun η => ?_
    exact (pow_pos (kgFreq_pos _) N).ne'
  have hG : Continuous fun η : E => G (ξ - η) :=
    G.continuous.comp (continuous_const.sub continuous_id)
  exact (a.aestronglyMeasurable.mul hcont.aestronglyMeasurable).mul hG.aestronglyMeasurable

theorem integrable_kgConvIntegrand (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    Integrable (kgConvIntegrand N a G ξ) (volume : Measure E) := by
  refine Integrable.mono' (((a.integrable_weight).const_mul (Real.sqrt 2 ^ N * ‖G‖)))
    (aestronglyMeasurable_kgConvIntegrand a G ξ) ?_
  filter_upwards with η
  exact norm_kgConvIntegrand_le a G ξ η

/-! ## The convolution operator -/

/-- The weighted convolution of the representative `G` by the density `a`. -/
noncomputable def kgConv (N : ℕ) (a : E → ℂ) (G : E →ᵇ ℂ) (ξ : E) : ℂ :=
  ∫ η, kgConvIntegrand N a G ξ η

theorem norm_kgConv_le (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    ‖kgConv N a G ξ‖ ≤ Real.sqrt 2 ^ N * a.norm' * ‖G‖ := by
  have hbound := norm_integral_le_of_norm_le
    (a.integrable_weight.const_mul (Real.sqrt 2 ^ N * ‖G‖))
    (Filter.Eventually.of_forall fun η => norm_kgConvIntegrand_le a.toFun G ξ η)
  rw [kgConv]
  refine hbound.trans_eq ?_
  rw [integral_const_mul, WienerDensity.norm']
  ring

theorem continuous_kgConv (a : WienerDensity E N) (G : E →ᵇ ℂ) :
    Continuous (kgConv N a G) := by
  refine continuous_of_dominated
    (F := fun ξ : E => kgConvIntegrand N a G ξ)
    (bound := fun η => Real.sqrt 2 ^ N * ‖G‖ * (kgFreq η ^ N * ‖a η‖))
    (fun ξ => aestronglyMeasurable_kgConvIntegrand a G ξ)
    (fun ξ => Filter.Eventually.of_forall fun η => norm_kgConvIntegrand_le a G ξ η)
    ((a.integrable_weight).const_mul _) ?_
  filter_upwards with η
  refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.div ((continuous_kgFreq).pow N)
      ((continuous_kgFreq.comp (continuous_id.sub continuous_const)).pow N) fun ξ => ?_
    exact (pow_pos (kgFreq_pos _) N).ne'
  · exact G.continuous.comp (continuous_id.sub continuous_const)

/-- The convolution operator on the weighted space, as a bounded continuous function. -/
noncomputable def kgConvBCF (a : WienerDensity E N) (G : E →ᵇ ℂ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (kgConv N a G) (continuous_kgConv a G)
    (Real.sqrt 2 ^ N * a.norm' * ‖G‖) (norm_kgConv_le a G)

theorem kgConvBCF_apply (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    kgConvBCF a G ξ = kgConv N a G ξ := rfl

theorem norm_kgConvBCF_le (a : WienerDensity E N) (G : E →ᵇ ℂ) :
    ‖kgConvBCF a G‖ ≤ Real.sqrt 2 ^ N * a.norm' * ‖G‖ := by
  refine BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ ?_ _
  have h1 : (0 : ℝ) ≤ Real.sqrt 2 ^ N * a.norm' :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.norm'_nonneg
  exact mul_nonneg h1 (norm_nonneg _)

theorem kgConvBCF_add (a : WienerDensity E N) (G H : E →ᵇ ℂ) :
    kgConvBCF a (G + H) = kgConvBCF a G + kgConvBCF a H := by
  ext ξ
  have hsplit : ∀ η : E, kgConvIntegrand N a (G + H) ξ η
      = kgConvIntegrand N a G ξ η + kgConvIntegrand N a H ξ η := by
    intro η
    simp only [kgConvIntegrand, BoundedContinuousFunction.add_apply]
    ring
  show kgConv N a (G + H) ξ = kgConv N a G ξ + kgConv N a H ξ
  rw [kgConv, kgConv, kgConv, ← integral_add (integrable_kgConvIntegrand a G ξ)
    (integrable_kgConvIntegrand a H ξ)]
  exact integral_congr_ae (Filter.Eventually.of_forall hsplit)

theorem kgConvBCF_smul (a : WienerDensity E N) (c : ℝ) (G : E →ᵇ ℂ) :
    kgConvBCF a (c • G) = c • kgConvBCF a G := by
  ext ξ
  have hsplit : ∀ η : E, kgConvIntegrand N a (c • G) ξ η
      = (c : ℂ) • kgConvIntegrand N a G ξ η := by
    intro η
    simp only [kgConvIntegrand, BoundedContinuousFunction.smul_apply, Complex.real_smul]
    ring
  show kgConv N a (c • G) ξ = c • kgConv N a G ξ
  rw [kgConv, kgConv]
  rw [show (∫ η, kgConvIntegrand N a (c • G) ξ η) = ∫ η, (c : ℂ) • kgConvIntegrand N a G ξ η from
    integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_smul]
  simp [Complex.real_smul]

/-- **Convolution by an admissible density is a bounded operator** on the weighted space, with norm
at most `√2ᴺ` times the weighted `L¹` norm of the density. -/
noncomputable def kgConvCLM (a : WienerDensity E N) : (E →ᵇ ℂ) →L[ℝ] (E →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := kgConvBCF a
      map_add' := kgConvBCF_add a
      map_smul' := fun c G => kgConvBCF_smul a c G }
    (Real.sqrt 2 ^ N * a.norm') fun G => by
      simpa [mul_assoc] using norm_kgConvBCF_le a G

theorem kgConvCLM_apply (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    kgConvCLM a G ξ = kgConv N a G ξ := rfl

theorem norm_kgConvCLM_le (a : WienerDensity E N) :
    ‖kgConvCLM a‖ ≤ Real.sqrt 2 ^ N * a.norm' := by
  refine LinearMap.mkContinuous_norm_le _ ?_ _
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.norm'_nonneg

end GaloisForLFunctions.HTGeometry
