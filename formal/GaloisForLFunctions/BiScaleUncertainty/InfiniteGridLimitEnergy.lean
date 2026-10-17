import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridCorrelationCompactness
import GaloisForLFunctions.BiScaleUncertainty.LocalCorrelationEnergyStability
import GaloisForLFunctions.BiScaleUncertainty.MultiCosetGramPackingAndNyquistDensity
import GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Positive-definite correlation limits with finite singular energy

Finite Gram positivity and the full logarithmic grid survive global uniform convergence.
Fatou's lemma preserves the normalized Lévy energy ceiling and proves actual integrability
of the limiting singular integrand. The limit need not have a compact source representation.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Extended normalized kernel energy, valid also before integrability is known. -/
def correlationLevyEnergy (H : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - H x) * archLevySinhWeight x)

variable {K : ℝ}

private theorem InfiniteGridEnergySource.correlation_integrand_eq (f : InfiniteGridEnergySource K) :
    (fun x => (1 - f.correlation x) * archLevySinhWeight x) =
      fun x => (autocorr f.source 0 - autocorr f.source x) * archLevySinhWeight x /
        autocorr f.source 0 := by
  funext x
  dsimp [InfiniteGridEnergySource.correlation]
  field_simp [f.mass_pos.ne']

theorem InfiniteGridEnergySource.integrable_correlationLevyIntegrand (f : InfiniteGridEnergySource K) :
    IntegrableOn (fun x => (1 - f.correlation x) * archLevySinhWeight x) (Ioi 0) := by
  rw [f.correlation_integrand_eq]
  exact (integrableOn_biScaleLevyIntegrand f.smooth f.source.hasCompactSupport).div_const _

/-- The extended kernel energy agrees exactly with the actual source's normalized energy. -/
theorem InfiniteGridEnergySource.correlationLevyEnergy_eq (f : InfiniteGridEnergySource K) :
    correlationLevyEnergy f.correlation = ENNReal.ofReal (normalizedArchEnergy f.source) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => (1 - f.correlation x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sub_nonneg.mpr ((le_abs_self _).trans (f.abs_correlation_le_one x)))
      (archLevySinhWeight_pos hx).le
  rw [correlationLevyEnergy,
    ← ofReal_integral_eq_lintegral_ofReal f.integrable_correlationLevyIntegrand hn]
  congr 1
  rw [f.correlation_integrand_eq, ← normalizedArchEnergy_eq_integral]

/-- The nonnegative singular energy is lower semicontinuous under pointwise convergence. -/
theorem correlationLevyEnergy_le_liminf {F : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    (hF : ∀ n, Measurable (F n)) (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (H x))) :
    correlationLevyEnergy H ≤ liminf (fun n => correlationLevyEnergy (F n)) atTop := by
  have hp (x : ℝ) : Tendsto
      (fun n => ENNReal.ofReal ((1 - F n x) * archLevySinhWeight x)) atTop
      (𝓝 (ENNReal.ofReal ((1 - H x) * archLevySinhWeight x))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds.sub (h x)).mul tendsto_const_nhds)
  unfold correlationLevyEnergy
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ),
        liminf (fun n => ENNReal.ofReal ((1 - F n x) * archLevySinhWeight x)) atTop := by
      congr 1
      funext x
      exact (hp x).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le fun n =>
      ((measurable_const.sub (hF n)).mul measurable_archLevySinhWeight).ennreal_ofReal

/-- Even pointwise source-correlation limits retain the extended energy ceiling. -/
theorem infiniteGrid_pointwise_limit_energy_le (f : ℕ → InfiniteGridEnergySource K)
    {H : ℝ → ℝ} (h : ∀ x, Tendsto (fun n => (f n).correlation x) atTop (𝓝 (H x))) :
    correlationLevyEnergy H ≤ ENNReal.ofReal K := by
  apply (correlationLevyEnergy_le_liminf (fun n => (f n).continuous_correlation.measurable) h).trans
  apply Filter.liminf_le_of_frequently_le'
  apply (Eventually.of_forall _).frequently
  intro n
  rw [(f n).correlationLevyEnergy_eq]
  exact ENNReal.ofReal_le_ofReal (f n).energy_le

/-- Uniform limits have an ordinary integrable Lévy density with the same energy ceiling. -/
theorem infiniteGrid_uniform_limit_integrable_energy (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop) :
    IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0) ∧
      (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) ≤ K := by
  have hc := h.continuous (Eventually.of_forall fun n => (f n).continuous_correlation).frequently
  have hm : AEStronglyMeasurable (fun x => (1 - H x) * archLevySinhWeight x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_const.sub hc.measurable).mul measurable_archLevySinhWeight).aestronglyMeasurable
  have hb (x : ℝ) : H x ≤ 1 := le_of_tendsto' (h.tendsto_at x) fun n =>
    (le_abs_self _).trans ((f n).abs_correlation_le_one x)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => (1 - H x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sub_nonneg.mpr (hb x)) (archLevySinhWeight_pos hx).le
  have he := infiniteGrid_pointwise_limit_energy_le f h.tendsto_at
  have hi : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp
      (ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hK).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  exact he

/-- Every finite normalized correlation Gram form is an actual nonnegative square integral. -/
theorem InfiniteGridEnergySource.gram_nonneg (f : InfiniteGridEnergySource K)
    (m : ℕ) (c t : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * f.correlation (t i - t j) := by
  have hp : 0 ≤ ∑ i, ∑ j, c i * c j * autocorr f.source (t i - t j) := by
    rw [← integral_finset_sum_shift_sq_eq (f := (f.source : ℝ → ℝ))
      f.source.continuous f.source.hasCompactSupport Finset.univ c t]
    exact integral_nonneg fun u => sq_nonneg _
  have hd := div_nonneg hp f.mass_pos.le
  simpa only [InfiniteGridEnergySource.correlation, Finset.sum_div, mul_div_assoc] using hd

/-- Every real finite Gram inequality survives uniform source-correlation limits. -/
theorem infiniteGrid_uniform_limit_gram_nonneg (f : ℕ → InfiniteGridEnergySource K)
    {H : ℝ → ℝ} (h : TendstoUniformly (fun n => (f n).correlation) H atTop)
    (m : ℕ) (c t : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * H (t i - t j) := by
  have hs : Tendsto (fun n => ∑ i, ∑ j, c i * c j * (f n).correlation (t i - t j))
      atTop (𝓝 (∑ i, ∑ j, c i * c j * H (t i - t j))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul (h.tendsto_at (t i - t j))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hs
    (Eventually.of_forall fun n => (f n).gram_nonneg m c t)

/-- Compact correlation relaxation of the actual infinite-grid energy class, retaining
the complete grid, every finite real Gram inequality, and an integrable singular density. -/
theorem exists_infiniteGrid_finite_energy_limit (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) :
    ∃ (φ : ℕ → ℕ) (H : ℝ → ℝ), StrictMono φ ∧
      TendstoUniformly (fun n => (f (φ n)).correlation) H atTop ∧
      Continuous H ∧ H 0 = 1 ∧ Function.Even H ∧ (∀ x, |H x| ≤ 1) ∧
      (∀ n : ℕ, 2 ≤ n → H (Real.log (n : ℝ)) = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A ≤ |x| → |H x| < ε) ∧
      (∀ (m : ℕ) (c t : Fin m → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * H (t i - t j)) ∧
      IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0) ∧
      (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) ≤ K := by
  obtain ⟨φ, H, hφ, hc, hu⟩ := exists_uniform_limit_infiniteGrid_correlations hK f
  obtain ⟨_, h0, heven, hbound, hzero, htail⟩ :=
    infiniteGrid_uniform_limit_geometry hK (fun n => f (φ n)) hu
  obtain ⟨hi, hE⟩ := infiniteGrid_uniform_limit_integrable_energy hK (fun n => f (φ n)) hu
  exact ⟨φ, H, hφ, hu, hc, h0, heven, hbound, hzero, htail,
    infiniteGrid_uniform_limit_gram_nonneg (fun n => f (φ n)) hu, hi, hE⟩

end

end GaloisForLFunctions.BiScaleUncertainty
