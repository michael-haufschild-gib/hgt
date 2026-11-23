import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.EdgeProfiles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.EndpointStability

/-! # Uniform complex recovery from a single real endpoint measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- A bounded frequency window at positive distance from the imaginary axis. -/
def temperatureWindow (δ : GibbsExponent) (M : ℝ) := {z : ℂ | δ.val ≤ z.re ∧ ‖z‖ ≤ M}

/-- A vanishing real reading forces uniform convergence to zero throughout every temperature window. -/
theorem uniform_zero_of_reading {ι : Type*} {r : ℕ} (b : ι → SpectralBand r) (l : Filter ι)
    (f : SpectralResponse) (h : Tendsto (relativeReading f ∘ b) l (𝓝 0)) (δ : GibbsExponent) (M : ℝ) :
    TendstoUniformlyOn (fun i => relativePartition (b i)) (fun _ => 0) l (temperatureWindow δ M) := by
  have hδ := (relativeReading_tendsto_zero_iff (powerResponse δ) b l).mpr ((relativeReading_tendsto_zero_iff f b l).mp h)
  have ht : Tendsto (fun i => M / δ.val * relativeReading (powerResponse δ) (b i)) l (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_const_nhds (x := M / δ.val)).mul hδ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with i hi z hz
  rw [dist_zero_left]
  exact ((relativePartition_norm_le (b i) δ hz.1).trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hz.2 δ.property.le) (relativeReading_bounds _ _).1)).trans_lt hi

/-- A saturated real reading forces uniform recovery of the finite shifted Dirichlet polynomial. -/
theorem uniform_prefix_of_reading {ι : Type*} {r : ℕ} (b : ι → SpectralBand r) (l : Filter ι)
    (f : SpectralResponse) (h : Tendsto (relativeReading f ∘ b) l (𝓝 (relativeHead f r)))
    (δ : GibbsExponent) (M : ℝ) :
    TendstoUniformlyOn (fun i => relativePartition (b i))
      (fun z => ∑ j ∈ Finset.range r, (occupationWeight j : ℂ)^z) l (temperatureWindow δ M) := by
  let g := powerResponse δ
  have hδ := (relativeReading_tendsto_head_iff g b l).mpr ((relativeReading_tendsto_head_iff f b l).mp h)
  have ht : Tendsto (fun i => M / δ.val * (relativeHead g r - relativeReading g (b i))) l (𝓝 0) := by
    simpa only [sub_self,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := M / δ.val)).mul ((tendsto_const_nhds (x := relativeHead g r)).sub hδ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with i hi z hz
  rw [← relativePartition_cold r (δ.property.trans_le hz.1),dist_eq_norm]
  have hc := norm_relativePartition_sub_le (coldEdge r) (b i) (fun n => (b i n).property.1) δ hz.1
  rw [relativeReading_cold] at hc
  exact (hc.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hz.2 δ.property.le)
    (sub_nonneg.mpr (relativeReading_bounds g (b i)).2))).trans_lt hi

#print axioms uniform_zero_of_reading
#print axioms uniform_prefix_of_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
