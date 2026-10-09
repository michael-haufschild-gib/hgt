import GaloisForLFunctions.RHTower.XiPeripheralTargetCharts
import GaloisForLFunctions.HTGeometry.PuncturedSourceDisk
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Isolated punctures in the actual Xi source

The identity principle and xi(0)=1/2 show that both marked fibers are locally
isolated. At each deleted point a connected punctured source disk maps into
the corresponding explicit target chart and contains no other deleted point.
-/

open Topology Set Function Filter

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

@[simp] theorem mem_untwisted_sourceSet (z : ℂ) :
    z ∈ sourceSet ({0} : Finset ℝ) ↔ xi z ≠ 0 ∧ xi z ≠ -1 := by
  simp [sourceSet, value]

/-- Every actual marked fiber is locally isolated, using the identity principle
and the unmarked value xi(0)=1/2. -/
theorem eventually_xi_ne_peripheralCenter (b : Bool) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, xi z ≠ peripheralCenter b := by
  have hf : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => peripheralCenter b) univ :=
    fun _ _ => analyticAt_const
  by_contra hn
  have hfreq : ∃ᶠ z in 𝓝[≠] a, xi z = peripheralCenter b := by
    simpa only [not_ne_iff] using (not_eventually.mp hn)
  have he := hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ a) hfreq
  have h0 := he (mem_univ (0 : ℂ))
  rw [xi_zero] at h0
  cases b <;> norm_num [peripheralCenter] at h0

/-- Around every source point, a punctured neighborhood lies in the old source. -/
theorem untwisted_sourceSet_mem_punctured_nhds (a : ℂ) :
    sourceSet ({0} : Finset ℝ) ∈ 𝓝[≠] a := by
  filter_upwards [eventually_xi_ne_peripheralCenter false a,
    eventually_xi_ne_peripheralCenter true a] with z h0 h1
  exact (mem_untwisted_sourceSet z).mpr ⟨h0, h1⟩

/-- A deleted source point has a connected punctured disk mapping into its
chosen target chart and containing no other deleted source point. -/
theorem exists_punctured_source_disk_at_mark (b : Bool) (a : ℂ)
    (ha : xi a = peripheralCenter b) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ puncturedSourceDisk a r,
      z ∈ sourceSet ({0} : Finset ℝ) ∧ ‖xi z - peripheralCenter b‖ < 1 / 4 := by
  have hv : {z : ℂ | ‖xi z - peripheralCenter b‖ < 1 / 4} ∈ 𝓝 a :=
    (isOpen_lt (xi_differentiable.continuous.sub continuous_const).norm continuous_const).mem_nhds
      (by simp [ha])
  have hu : sourceSet ({0} : Finset ℝ) ∩ {z : ℂ | ‖xi z - peripheralCenter b‖ < 1 / 4} ∈ 𝓝[≠] a :=
    Filter.inter_mem (untwisted_sourceSet_mem_punctured_nhds a) (nhdsWithin_le_nhds hv)
  obtain ⟨r, hr, hsub⟩ := exists_puncturedSourceDisk_subset hu
  exact ⟨r, hr, fun z hz => hsub hz⟩

end RHTower.XiMarkedMonodromy
