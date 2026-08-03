import GaloisForLFunctions.HTGeometry.ComplexExponentialSeriesCarrier
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The hull of an exponential series is a compact phase torus

The entire carriers of a fixed amplitude family, indexed by unimodular phases, form a continuous
image of the phase torus in the compact-open topology: on a compact set the tail of the series is
uniformly small in the phases, while the remaining head depends continuously on finitely many phase
coordinates.

Since the phase torus is compact and the space of continuous functions is Hausdorff, injectivity --
Bohr--Fourier uniqueness -- upgrades the continuous hull map to a closed embedding, so the hull is a
homeomorphic copy of the phase torus.
-/

open Filter Topology Set
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*}

/-- The hull map: the entire carrier of a unimodular phase family. -/
def bohrHullMap (a : ι → ℂ) (omega : ι → ℝ) (h : ExpSeriesNormallySummable a omega)
    (lam : ι → Circle) : C(ℂ, ℂ) :=
  ⟨cexpSeriesCarrier (fun i => a i * (lam i : ℂ)) omega,
    (differentiable_cexpSeriesCarrier
      (expSeriesNormallySummable_phase h fun i => le_of_eq (Circle.norm_coe (lam i)))).continuous⟩

theorem bohrHullMap_apply (a : ι → ℂ) (omega : ι → ℝ) (h : ExpSeriesNormallySummable a omega)
    (lam : ι → Circle) (z : ℂ) :
    bohrHullMap a omega h lam z = cexpSeriesCarrier (fun i => a i * (lam i : ℂ)) omega z := rfl

/-- **The hull map is continuous** for the topology of uniform convergence on compacts. -/
theorem continuous_bohrHullMap {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) : Continuous (bohrHullMap a omega h) := by
  classical
  rw [continuous_iff_continuousAt]
  intro lam₀
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt_real (h R) (show (0 : ℝ) < ε / 4 by linarith)
  set g : (ι → Circle) → ℝ :=
    fun lam => ∑ i ∈ S, ‖a i‖ * ‖((lam₀ i : ℂ) - (lam i : ℂ))‖ * Real.exp (R * |omega i|) with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ continuous_const
    refine Continuous.mul continuous_const ?_
    exact (continuous_const.sub ((continuous_subtype_val).comp (continuous_apply i))).norm
  have hg0 : g lam₀ = 0 := by
    simp [hg]
  have hev : ∀ᶠ lam in 𝓝 lam₀, g lam < ε / 2 := by
    have htend : Filter.Tendsto g (𝓝 lam₀) (nhds (0 : ℝ)) := by
      have hcont := hgc.tendsto lam₀
      rwa [hg0] at hcont
    exact htend.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)
  filter_upwards [hev] with lam hlam z hz
  have hzball : z ∈ Metric.closedBall (0 : ℂ) R := hR hz
  have hbound := norm_cexpSeriesCarrier_phase_sub_phase_le h
    (lam := fun i => (lam₀ i : ℂ)) (mu := fun i => (lam i : ℂ))
    (fun i => le_of_eq (Circle.norm_coe (lam₀ i))) (fun i => le_of_eq (Circle.norm_coe (lam i)))
    S hzball
  have htail := hS S (le_refl S)
  rw [Complex.dist_eq]
  calc ‖bohrHullMap a omega h lam₀ z - bohrHullMap a omega h lam z‖
      ≤ g lam + 2 * ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ * Real.exp (R * |omega i|) := hbound
    _ < ε / 2 + 2 * (ε / 4) := by
        refine add_lt_add hlam ?_
        linarith [htail]
    _ = ε := by ring

/-- **The hull map is injective** when the amplitudes are nonzero and the frequencies distinct. -/
theorem injective_bohrHullMap {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (hane : ∀ i, a i ≠ 0)
    (hinj : Function.Injective omega) : Function.Injective (bohrHullMap a omega h) := by
  intro lam mu hlm
  have hnorm := summable_norm_of_expSeriesNormallySummable h
  have hphase : (fun i => (lam i : ℂ)) = fun i => (mu i : ℂ) := by
    refine cexpSeriesCarrier_phase_injective ?_ ?_ hane hinj ?_
    · refine hnorm.congr fun i => ?_
      rw [norm_mul, Circle.norm_coe, mul_one]
    · refine hnorm.congr fun i => ?_
      rw [norm_mul, Circle.norm_coe, mul_one]
    · funext z
      exact congrArg (fun f : C(ℂ, ℂ) => f z) hlm
  funext i
  exact Subtype.ext (congrFun hphase i)

/-- **The hull is a homeomorphic copy of the phase torus.**  A continuous injection of the compact
phase torus into the Hausdorff space of continuous functions is a closed embedding. -/
theorem isClosedEmbedding_bohrHullMap {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (hane : ∀ i, a i ≠ 0)
    (hinj : Function.Injective omega) :
    Topology.IsClosedEmbedding (bohrHullMap a omega h) :=
  (continuous_bohrHullMap h).isClosedEmbedding (injective_bohrHullMap h hane hinj)

end

end GaloisForLFunctions
