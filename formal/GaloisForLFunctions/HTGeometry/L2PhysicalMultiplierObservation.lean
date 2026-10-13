import GaloisForLFunctions.HTGeometry.L2PhysicalSolidObservation
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Exact physical-hull observations of multiplication operators

The input itself attains the largest response, even when its physical hull is
not compact. Recovery at this input is equivalent to uniform hull recovery;
no uniform operator-norm bound on a multiplier family is needed.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology MeasureTheory
variable {α A : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter A}

theorem norm_ae_mul_le_of_mem_l2PhysicalSolidHull
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w : α → ℂ)
    (hT : ∀ y, (T y : α → ℂ) =ᵐ[μ] fun t => w t * y t)
    {x y : Lp ℂ 2 μ} (hy : y ∈ l2PhysicalSolidHull x) : ‖T y‖ ≤ ‖T x‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hy, hT y, hT x] with t ht hty htx
  rw [hty, htx, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem l2PhysicalObservation_eq_norm_of_ae_mul
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w : α → ℂ)
    (hT : ∀ y, (T y : α → ℂ) =ᵐ[μ] fun t => w t * y t) (x : Lp ℂ 2 μ) :
    l2PhysicalObservation T x = ‖T x‖ := by
  apply le_antisymm
  · apply csSup_le ((show (l2PhysicalSolidHull x).Nonempty from
      ⟨x, mem_l2PhysicalSolidHull_self x⟩).image _)
    rintro _ ⟨y, hy, rfl⟩
    exact norm_ae_mul_le_of_mem_l2PhysicalSolidHull T w hT hy
  · exact norm_apply_le_l2PhysicalObservation T (mem_l2PhysicalSolidHull_self x)

theorem tendstoUniformlyOn_l2PhysicalSolidHull_ae_mul_iff
    (T : A → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w : A → α → ℂ)
    (hT : ∀ a y, (T a y : α → ℂ) =ᵐ[μ] fun t => w a t * y t) (x : Lp ℂ 2 μ) :
    TendstoUniformlyOn (fun a y => T a y) (fun _ => 0) l (l2PhysicalSolidHull x) ↔
      Tendsto (fun a => T a x) l (𝓝 0) := by
  constructor
  · exact fun h => h.tendsto_at (mem_l2PhysicalSolidHull_self x)
  · intro h
    have hn : Tendsto (fun a => ‖T a x‖) l (𝓝 0) := by simpa only [norm_zero] using h.norm
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hn.eventually_lt_const hε] with a ha
    intro y hy
    simpa only [dist_zero_left] using
      (norm_ae_mul_le_of_mem_l2PhysicalSolidHull (T a) (w a) (hT a) hy).trans_lt ha

end
end GaloisForLFunctions.HTGeometry
