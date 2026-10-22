import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonChartGeneric

/-!
# The density families of the second-order calculus

Three families of densities occur in the chart calculus: the density of the evolution, the density of
its time derivative, and the densities derived from them by a spatial direction. This file collects
what the generic chart lemmas ask of each: a weight bound uniform on time intervals, and the
integrability that follows from it.

The weight bookkeeping is the whole content. The time derivative costs nothing — the Volterra bound
is uniform in the frequency — a spatial derivative costs one power, and the second time derivative
costs two; so a weight exceeding the dimension by two carries the entire second-order calculus.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## Integrability from a weight bound -/

theorem integrable_of_weight_bound {f : E → ℂ} {B : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < N)
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hb : ∀ ξ : E, ‖f ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B) : Integrable f (volume : Measure E) := by
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hdim).mul_const B) hmeas ?_
  filter_upwards with ξ
  exact hb ξ

theorem integrable_kgFreq_mul_of_weight_bound {f : E → ℂ} {B : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) + 1 < N)
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hb : ∀ ξ : E, ‖f ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B) :
    Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E) := by
  have hcast : (Module.finrank ℝ E : ℝ) + ((1 : ℕ) : ℝ) < N := by push_cast; linarith
  refine Integrable.mono'
    ((integrable_kgFreq_pow_mul_inv_pow (E := E) (j := 1) hcast).mul_const B)
    ((continuous_kgFreq.aestronglyMeasurable).mul hmeas.norm) ?_
  filter_upwards with ξ
  have hpos : (0 : ℝ) < kgFreq ξ := kgFreq_pos ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (norm_nonneg _))]
  calc kgFreq ξ * ‖f ξ‖
      ≤ kgFreq ξ * ((kgFreq ξ ^ N)⁻¹ * B) := mul_le_mul_of_nonneg_left (hb ξ) hpos.le
    _ = kgFreq ξ ^ (1 : ℕ) * (kgFreq ξ ^ N)⁻¹ * B := by rw [pow_one]; ring

/-! ## The family of the evolution -/

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

theorem norm_kgFlowDensityDeriv_le_weight {T t : ℝ} (ht : |t| ≤ T) (ξ : E) :
    ‖kgFlowDensityDeriv a G₀ t ξ‖
      ≤ (kgFreq ξ ^ N)⁻¹ * (‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T)) := by
  rw [norm_kgFlowDensityDeriv]
  exact mul_le_mul_of_nonneg_left (norm_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ ht)
    (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)

theorem integrable_kgFlowDensityDeriv (hdim : (Module.finrank ℝ E : ℝ) < N) (t : ℝ) :
    Integrable (kgFlowDensityDeriv a G₀ t) (volume : Measure E) :=
  integrable_of_weight_bound hdim
    (continuous_kgFlowDensityDeriv_freq a G₀ t).aestronglyMeasurable
    (fun ξ => norm_kgFlowDensityDeriv_le_weight a G₀ (le_refl |t|) ξ)

theorem integrable_kgFreq_mul_kgFlowDensityDeriv (hdim : (Module.finrank ℝ E : ℝ) + 1 < N)
    (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ * ‖kgFlowDensityDeriv a G₀ t ξ‖) (volume : Measure E) :=
  integrable_kgFreq_mul_of_weight_bound hdim
    (continuous_kgFlowDensityDeriv_freq a G₀ t).aestronglyMeasurable
    (fun ξ => norm_kgFlowDensityDeriv_le_weight a G₀ (le_refl |t|) ξ)

/-! ## The second time derivative -/

theorem norm_kgFlowDensityDeriv2_le_weight {K : ℕ} (hNK : N = K + 2) {T t : ℝ} (ht : |t| ≤ T)
    (ξ : E) :
    ‖kgFlowDensityDeriv2 a G₀ t ξ‖
      ≤ (kgFreq ξ ^ K)⁻¹
        * (kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T) := by
  subst hNK
  have hpos : (0 : ℝ) < kgFreq ξ := kgFreq_pos ξ
  have hone : (1 : ℝ) ≤ kgFreq ξ := one_le_kgFreq ξ
  have hbound := norm_deriv_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ ht
  rw [norm_kgFlowDensityDeriv2]
  have hsplit : (kgFreq ξ ^ (K + 2))⁻¹ = (kgFreq ξ ^ K)⁻¹ * (kgFreq ξ ^ (2 : ℕ))⁻¹ := by
    rw [pow_add, mul_inv]
  have hstep : (kgFreq ξ ^ (K + 2))⁻¹
      * ‖deriv (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ) t‖
      ≤ (kgFreq ξ ^ (K + 2))⁻¹
        * (kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T) :=
    mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_pos hpos (K + 2)).le)
  refine hstep.trans ?_
  rw [hsplit]
  have hsq : (0 : ℝ) < kgFreq ξ ^ (2 : ℕ) := pow_pos hpos 2
  have hsqone : (1 : ℝ) ≤ kgFreq ξ ^ (2 : ℕ) := one_le_pow₀ hone
  have hKpos : (0 : ℝ) < (kgFreq ξ ^ K)⁻¹ := inv_pos.mpr (pow_pos hpos K)
  have hsize : (0 : ℝ) ≤ kgFlowSize a G₀ T := kgFlowSize_nonneg a G₀ T
  have hM : (0 : ℝ) ≤ kgFlowBoundConst a := kgFlowBoundConst_nonneg a
  have hinner : (kgFreq ξ ^ (2 : ℕ))⁻¹
      * (kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T)
      ≤ kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T := by
    have hone' : (kgFreq ξ ^ (2 : ℕ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hsqone
    have hexp : (kgFreq ξ ^ (2 : ℕ))⁻¹ * (kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T)
        = kgFlowSize a G₀ T := by
      field_simp
    rw [mul_add, hexp]
    have : (kgFreq ξ ^ (2 : ℕ))⁻¹ * (kgFlowBoundConst a * kgFlowSize a G₀ T)
        ≤ kgFlowBoundConst a * kgFlowSize a G₀ T := by
      nlinarith [mul_nonneg hM hsize]
    linarith
  calc (kgFreq ξ ^ K)⁻¹ * (kgFreq ξ ^ (2 : ℕ))⁻¹
        * (kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T)
      = (kgFreq ξ ^ K)⁻¹ * ((kgFreq ξ ^ (2 : ℕ))⁻¹
        * (kgFreq ξ ^ (2 : ℕ) * kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T)) := by
        ring
    _ ≤ (kgFreq ξ ^ K)⁻¹ * (kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T) :=
        mul_le_mul_of_nonneg_left hinner hKpos.le

theorem continuous_kgFlowDensityDeriv2_time (ξ : E) :
    Continuous fun t : ℝ => kgFlowDensityDeriv2 a G₀ t ξ := by
  have hfun : (fun t : ℝ => kgFlowDensityDeriv2 a G₀ t ξ)
      = fun t : ℝ => ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
        * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ) * kgPotentialFlow a G₀ t ξ) + kgFlowSource a G₀ ξ t) := by
    funext t
    exact kgFlowDensityDeriv2_eq a G₀ t ξ
  rw [hfun]
  have hflow : Continuous fun t : ℝ => kgPotentialFlow a G₀ t ξ :=
    ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous).comp
      (continuous_kgPotentialFlow a G₀)
  exact continuous_const.mul (((continuous_const.mul hflow).neg).add
    (continuous_kgFlowSource a G₀ ξ))

theorem integrable_kgFlowDensityDeriv2 {K : ℕ} (hNK : N = K + 2)
    (hdim : (Module.finrank ℝ E : ℝ) < K) (t : ℝ) :
    Integrable (kgFlowDensityDeriv2 a G₀ t) (volume : Measure E) :=
  integrable_of_weight_bound (N := K) hdim
    (continuous_kgFlowDensityDeriv2 a G₀ t).aestronglyMeasurable
    (fun ξ => norm_kgFlowDensityDeriv2_le_weight a G₀ hNK (le_refl |t|) ξ)

end GaloisForLFunctions.HTGeometry
