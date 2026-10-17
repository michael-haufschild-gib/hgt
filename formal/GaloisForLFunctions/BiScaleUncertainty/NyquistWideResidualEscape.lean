import GaloisForLFunctions.BiScaleUncertainty.NyquistWideResidualLimit
import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightProducer

/-! # Supercritical escape by one actual low-energy smooth source family -/

open Set Filter Topology MeasureTheory
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem eventually_nyquistWideResidual_prefix_lower {β : ℝ} (hβ : 0 ≤ β) (m N M : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * (∑ k ∈ Finset.range M, nyquistWeightCellMass β m (N + k)) ≤
        nyquistWideResidual β m N j := by
  obtain ⟨r, hr, hplateau⟩ := exists_nyquistWideCorrelation_plateau
  have hn : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hn.eventually (eventually_ge_atTop (nyquistResidualNode (N + M) / r))]
    with j hj
  have hj' : nyquistResidualNode (N + M) ≤ r * ((j : ℝ) + 1) := by
    simpa only [mul_comm] using (div_le_iff₀ hr).mp hj
  have herror (k : ℕ) : 0 ≤ nyquistWeightCellError β m (nyquistWideCorrelationMap j) (N + k) := by
    rw [nyquistWeightCellError_eq_integral_kernel β m N k]
    exact integral_nonneg (fun x => mul_nonneg (nyquistWideCorrelation_nonneg j x)
      (nyquistWeightKernel_nonneg hβ m N x))
  have hs := hasSum_nyquistWeightCellError_compact hβ m N (nyquistWideCorrelationMap j)
    (hasCompactSupport_nyquistWideCorrelation j)
  have htotal := hs.summable.sum_le_tsum (Finset.range M) (fun k _ => herror k)
  rw [hs.tsum_eq] at htotal
  change (∑ k ∈ Finset.range M, nyquistWeightCellError β m (nyquistWideCorrelationMap j) (N + k)) ≤
    nyquistWideResidual β m N j at htotal
  have hcell (k : ℕ) (hk : k ∈ Finset.range M) :
      (1 / 2 : ℝ) * nyquistWeightCellMass β m (N + k) ≤
        nyquistWeightCellError β m (nyquistWideCorrelationMap j) (N + k) := by
    rw [nyquistWeightCellError_eq_integral_kernel β m N k]
    calc
      _ = ∫ x in nyquistResidualCell (N + k), (1 / 2 : ℝ) * nyquistWeightKernel β m N x := by
        rw [integral_const_mul, integral_nyquistWeightKernel_cell]
      _ ≤ ∫ x in nyquistResidualCell (N + k),
          nyquistWideCorrelationMap j x * nyquistWeightKernel β m N x := by
        apply integral_mono_ae ((integrableOn_nyquistWeightKernel_cell β m N k).const_mul (1 / 2))
          (integrable_nyquistWideResidual hβ m N j).integrableOn
        filter_upwards [ae_restrict_mem (measurableSet_nyquistResidualCell (N + k))] with x hx
        apply mul_le_mul_of_nonneg_right _ (nyquistWeightKernel_nonneg hβ m N x)
        apply hplateau j x
        · exact (nyquistResidualNode_nonneg (N + k)).trans hx.1.le
        · exact (hx.2.trans (strictMono_nyquistResidualNode.monotone
            (by have hk' := Finset.mem_range.mp hk; omega : N + k + 1 ≤ N + M))).trans hj'
  have hsum := Finset.sum_le_sum hcell
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans htotal

theorem tendsto_nyquistWideResidual_supercritical {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hcrit : (m : ℝ) + 1 ≤ β) : Tendsto (nyquistWideResidual β m N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro L
  obtain ⟨M, hM⟩ := ((tendsto_sum_nyquistWeightCellMass_atTop hβ m N hcrit).eventually
    (eventually_gt_atTop (2 * L))).exists
  filter_upwards [eventually_nyquistWideResidual_prefix_lower hβ.le m N M] with j hj
  linarith

theorem exists_nyquistWideResidual_above {β ε C : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hcrit : (m : ℝ) + 1 ≤ β) (hε : 0 < ε) :
    ∃ j : ℕ, normalizedArchEnergy (nyquistWideSource j) < ε ∧
      C < nyquistWideResidual β m N j := by
  exact ((tendsto_nyquistWideSource_energy.eventually_lt_const hε).and
    ((tendsto_nyquistWideResidual_supercritical hβ m N hcrit).eventually
      (eventually_gt_atTop C))).exists

theorem not_nyquistWideResidual_bounded_under_energy_ceiling {β ε : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hcrit : (m : ℝ) + 1 ≤ β) (hε : 0 < ε) :
    ¬ ∃ C : ℝ, ∀ j : ℕ, normalizedArchEnergy (nyquistWideSource j) ≤ ε →
      nyquistWideResidual β m N j ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨j, hj, hjC⟩ := exists_nyquistWideResidual_above hβ m N hcrit hε (C := C)
  exact (not_lt_of_ge (hC j hj.le)) hjC

end
end GaloisForLFunctions.BiScaleUncertainty
