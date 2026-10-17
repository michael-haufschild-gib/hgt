import GaloisForLFunctions.BiScaleUncertainty.DyadicSchurSupport
import GaloisForLFunctions.BiScaleUncertainty.FullGridCappedCollarHierarchy

/-!
# Physical source-energy certificates from dyadic Schur splitting

The optimized four-coordinate Schur kernel is measurable, nonnegative and
bounded by allocated physical mass. Its maximum with the full capped kernel
retains all previous certificates. Exact signed transport yields an extended
energy bound, with no supplied Bessel, Schur or analytic-energy interface.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

private theorem dyadic_selected_le_sum {n : ℕ} (hn : 2 ≤ n) (a b : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    a 0 + b 0 + a 2 ≤ ∑ k ∈ Finset.range (n + 1), (a k + b k) := by
  have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ (a 0 + b 0) + (a 2 + b 2) := by linarith [hb 2]
    _ = ∑ k ∈ ({0, 2} : Finset ℕ), (a k + b k) := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => add_nonneg (ha k) (hb k))

namespace PhysicalCollarPartition
variable {n : ℕ}

def dyadicSchurKernel (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  archLevySinhWeight y + ρ.weight false 0 y + ρ.weight false 2 y + ρ.weight true 0 y -
    DyadicSchur.optimizedSupport (archLevySinhWeight y) (ρ.weight false 0 y)
      (ρ.weight false 2 y) (ρ.weight true 0 y)

def schurCappedKernel (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  max (ρ.cappedKernel (productAdmittedCutoff n) y) (ρ.dyadicSchurKernel y)

def schurCappedCoefficient (ρ : PhysicalCollarPartition n) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.schurCappedKernel y

theorem dyadicSchurKernel_bounds (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ρ.dyadicSchurKernel y ∧ ρ.dyadicSchurKernel y ≤ ρ.mass y := by
  have hl := DyadicSchur.origin_le_optimizedSupport (archLevySinhWeight y)
    (ρ.weight false 0 y) (ρ.weight false 2 y) (ρ.weight true 0 y)
  have hu := DyadicSchur.optimizedSupport_le_mass (archLevySinhWeight_nonneg hy)
    (ρ.weight_nonneg false 0 y) (ρ.weight_nonneg false 2 y) (ρ.weight_nonneg true 0 y)
  have hm := dyadic_selected_le_sum hn (fun k => ρ.weight false k y) (fun k => ρ.weight true k y)
    (fun k => ρ.weight_nonneg false k y) (fun k => ρ.weight_nonneg true k y)
  change _ ≤ ρ.mass y at hm
  unfold dyadicSchurKernel
  constructor <;> linarith

theorem schurCappedKernel_bounds (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ρ.schurCappedKernel y ∧ ρ.schurCappedKernel y ≤ ρ.mass y :=
  ⟨(ρ.cappedKernel_bounds (productAdmittedCutoff_le n) hy).1.trans (le_max_left _ _),
    max_le (ρ.cappedKernel_bounds (productAdmittedCutoff_le n) hy).2
      (ρ.dyadicSchurKernel_bounds hn hy).2⟩

theorem measurable_dyadicSchurKernel (ρ : PhysicalCollarPartition n) : Measurable ρ.dyadicSchurKernel := by
  have hm : Measurable (fun y => (archLevySinhWeight y,
      ρ.weight false 0 y, ρ.weight false 2 y, ρ.weight true 0 y)) :=
    measurable_archLevySinhWeight.prodMk ((ρ.measurable_weight false 0).prodMk
      ((ρ.measurable_weight false 2).prodMk (ρ.measurable_weight true 0)))
  have hs : Measurable (fun y => DyadicSchur.optimizedSupport (archLevySinhWeight y)
      (ρ.weight false 0 y) (ρ.weight false 2 y) (ρ.weight true 0 y)) := by
    change Measurable ((fun q : ℝ × ℝ × ℝ × ℝ =>
      DyadicSchur.optimizedSupport q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
        (fun y => (archLevySinhWeight y, ρ.weight false 0 y, ρ.weight false 2 y, ρ.weight true 0 y)))
    exact DyadicSchur.continuous_optimizedSupport.measurable.comp hm
  exact (((measurable_archLevySinhWeight.add (ρ.measurable_weight false 0)).add
    (ρ.measurable_weight false 2)).add (ρ.measurable_weight true 0)).sub hs

theorem measurable_schurCappedKernel (ρ : PhysicalCollarPartition n) : Measurable ρ.schurCappedKernel :=
  (ρ.measurable_cappedKernel (productAdmittedCutoff n)).max ρ.measurable_dyadicSchurKernel

theorem integrableOn_schurCappedKernel (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n) :
    IntegrableOn ρ.schurCappedKernel (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ρ.measurable_schurCappedKernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := ρ.schurCappedKernel_bounds hn hy.1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (ρ.mass_le_bound y)

theorem cappedCoefficient_le_schurCappedCoefficient (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n) :
    ρ.cappedCoefficient (productAdmittedCutoff n) ≤ ρ.schurCappedCoefficient :=
  integral_mono_ae (ρ.integrableOn_cappedKernel (productAdmittedCutoff_le n))
    (ρ.integrableOn_schurCappedKernel hn) (Filter.Eventually.of_forall fun _ => le_max_left _ _)

theorem schurCappedCoefficient_le_tailMass (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n) :
    ρ.schurCappedCoefficient ≤ collarTailMass := by
  have hm : ρ.schurCappedCoefficient ≤ ∫ y in Ioo 0 logarithmicCollarRadius, ρ.mass y := by
    apply integral_mono_ae (ρ.integrableOn_schurCappedKernel hn) ρ.integrableOn_mass
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (ρ.schurCappedKernel_bounds hn hy.1.le).2
  rw [ρ.integral_mass] at hm
  refine hm.trans ?_
  apply setIntegral_mono_set integrableOn_archWeight_collar_tail
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx)).le
  · exact Filter.Eventually.of_forall fun _ hx => hx.1

/-- Literal grid zeros through four control the four selected signed physical costs. -/
theorem dyadicSchurKernel_source_pointwise (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    (f : LogarithmicGridSource n) (y : ℝ) :
    ρ.dyadicSchurKernel y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j - y)) +
         ρ.weight true j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j + y))) := by
  have hnode : logarithmicCollarNode 2 = 2 * Real.log 2 := by
    change Real.log (4 : ℝ) = _
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hnode0 : logarithmicCollarNode 0 = Real.log 2 := by norm_num [logarithmicCollarNode]
  have h := DyadicSchur.source_weighted_bound hn f y (archLevySinhWeight y)
    (ρ.weight false 0 y) (ρ.weight false 2 y) (ρ.weight true 0 y)
  have hd (x : ℝ) : 0 ≤ autocorr f.1 0 - autocorr f.1 x :=
    autocorr_sub_nonneg f.1.hasCompactSupport f.1.continuous x
  have hm := dyadic_selected_le_sum hn
    (fun j => ρ.weight false j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j - y)))
    (fun j => ρ.weight true j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j + y)))
    (fun j => mul_nonneg (ρ.weight_nonneg false j y) (hd _))
    (fun j => mul_nonneg (ρ.weight_nonneg true j y) (hd _))
  rw [hnode, hnode0] at hm
  unfold dyadicSchurKernel
  nlinarith

theorem schurCappedKernel_source_pointwise (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    (f : LogarithmicGridSource n) (y : ℝ) :
    ρ.schurCappedKernel y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j - y)) +
         ρ.weight true j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j + y))) := by
  unfold schurCappedKernel
  by_cases h : ρ.cappedKernel (productAdmittedCutoff n) y ≤ ρ.dyadicSchurKernel y
  · rw [max_eq_right h]
    exact ρ.dyadicSchurKernel_source_pointwise hn f y
  · rw [max_eq_left (le_of_not_ge h)]
    exact ρ.cappedKernel_source_pointwise f (productAdmittedCutoff_admitted hn) y

/-- Exact signed transport, including zero and infinite source energies. -/
theorem schurCappedCoefficient_source_energy (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    (f : LogarithmicGridSource n) :
    ENNReal.ofReal (ρ.schurCappedCoefficient * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hint := (ρ.integrableOn_schurCappedKernel hn).mul_const (autocorr f.1 0)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)]
      (fun y => ρ.schurCappedKernel y * autocorr f.1 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (ρ.schurCappedKernel_bounds hn hy.1.le).1 (autocorr_zero_nonneg f.1)
  change ENNReal.ofReal ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.schurCappedKernel y) * _) ≤ _
  rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f.1 y := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro y hy
      rw [ρ.sourceFibre_eq_ofReal f.1 hy.1.le]
      exact ENNReal.ofReal_le_ofReal (ρ.schurCappedKernel_source_pointwise hn f y)
    _ = _ := ρ.lintegral_sourceFibre f.1

theorem schurCappedCoefficient_le_normalized_energy (ρ : PhysicalCollarPartition n) (hn : 2 ≤ n)
    (f : SmoothLogarithmicGridSource n) :
    ρ.schurCappedCoefficient ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hb := (ρ.schurCappedCoefficient_source_energy hn f.1).trans
    (lintegral_mono_set (show Ioo 0 (logarithmicCollarEndpoint n) ⊆ Ioi 0 from fun _ hx => hx.1))
  have hi := integrableOn_biScaleLevyIntegrand f.2.1 f.1.1.hasCompactSupport
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => (autocorr f.1.1 0 - autocorr f.1.1 x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.1.1.hasCompactSupport f.1.1.continuous x)
      (archLevySinhWeight_pos hx).le
  have he : ENNReal.ofReal (biScaleLevyEnergy f.1.1) =
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1.1) x :=
    ofReal_integral_eq_lintegral_ofReal hi hnonneg
  rw [← he] at hb
  exact (le_div_iff₀ f.2.2).2 ((ENNReal.ofReal_le_ofReal_iff
    (biScaleLevyEnergy_nonneg f.1.1.hasCompactSupport f.1.1.continuous)).1 hb)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
