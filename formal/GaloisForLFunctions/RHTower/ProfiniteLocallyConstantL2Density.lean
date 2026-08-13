import GaloisForLFunctions.RHTower.L2SeparatedProductDensity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.Separation.Profinite

/-!
# Locally constant functions are dense in `L²` on a profinite space

On a compact Hausdorff totally disconnected space, regularity inserts a clopen set between
compact inner and open outer approximants of every measurable set.  Hence clopen indicators,
and therefore locally constant complex functions, are dense in `L²` for every finite regular
Borel measure.

This is the exact angular density input in Connes--Marcolli Proposition 2.30.
-/

open scoped ENNReal symmDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function MeasureTheory Set Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.Regular]

/-- Every measurable set in a profinite space is approximated in measure by a clopen set. -/
theorem profinite_exists_clopen_symmDiff_lt
    {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, IsClopen C ∧ μ (C ∆ s) < ε := by
  have hμs : μ s ≠ ∞ := measure_ne_top μ s
  have hhalf : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_sdiff_lt hμs hhalf with
    ⟨K, hKs, hKc, hμK⟩
  rcases hs.exists_isOpen_sdiff_lt hμs hhalf with
    ⟨U, hsU, hUo, _hμUtop, hμU⟩
  rcases exists_clopen_of_closed_subset_open hKc.isClosed hUo
      (hKs.trans hsU) with
    ⟨C, hC, hKC, hCU⟩
  refine ⟨C, hC, ?_⟩
  rw [measure_symmDiff_eq hC.2.measurableSet.nullMeasurableSet
    hs.nullMeasurableSet]
  rw [← ENNReal.add_halves ε]
  exact ENNReal.add_lt_add
    (lt_of_le_of_lt
      (measure_mono (sdiff_subset_sdiff_left hCU)) hμU)
    (lt_of_le_of_lt
      (measure_mono (sdiff_subset_sdiff_right hKC)) hμK)

/-- The canonical complex-linear realization of locally constant functions in `L²`. -/
def profiniteLocallyConstantToL2 :
    LocallyConstant X ℂ →ₗ[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp
    (LocallyConstant.toContinuousMapLinearMap ℂ)

/-- Clopen locally constant indicators realize the canonical `Lp` indicators exactly. -/
theorem profiniteLocallyConstantIndicatorToL2_eq
    (C : Set X) (hC : IsClopen C) (c : ℂ) :
    profiniteLocallyConstantToL2
        ((LocallyConstant.const X c).indicator hC) =
      indicatorConstLp 2 hC.2.measurableSet (measure_ne_top μ C) c := by
  apply Lp.ext
  filter_upwards [
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
      (((LocallyConstant.const X c).indicator hC : LocallyConstant X ℂ) : C(X, ℂ)),
    indicatorConstLp_coeFn
      (p := 2) (μ := μ) (hs := hC.2.measurableSet)
      (hμs := measure_ne_top μ C) (c := c)] with x hleft hright
  change
    (ContinuousMap.toLp 2 μ ℂ
      (((LocallyConstant.const X c).indicator hC :
        LocallyConstant X ℂ) : C(X, ℂ))) x = _
  rw [hright]
  rw [hleft]
  classical
  exact LocallyConstant.indicator_apply_eq_if _ _ hC

/-- Locally constant complex functions have dense image in `L²` on every profinite space. -/
theorem profiniteLocallyConstantToL2_denseRange :
    DenseRange
      (profiniteLocallyConstantToL2 :
        LocallyConstant X ℂ →ₗ[ℂ] Lp ℂ 2 μ) := by
  let T : LocallyConstant X ℂ →ₗ[ℂ] Lp ℂ 2 μ :=
    profiniteLocallyConstantToL2
  let V : Submodule ℂ (Lp ℂ 2 μ) := LinearMap.range T
  have hindicator
      (c : ℂ) {s : Set X} (hs : MeasurableSet s) :
      indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
        V.topologicalClosure := by
    change
      indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
        (V.topologicalClosure : Set (Lp ℂ 2 μ))
    rw [Submodule.topologicalClosure_coe]
    apply EMetric.mem_closure_iff.2
    intro ε hε
    by_cases hεtop : ε = ∞
    · refine ⟨0, SetLike.coe_mem 0, ?_⟩
      rw [hεtop]
      exact edist_lt_top _ _
    have hhalf : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
    obtain ⟨η, hηpos, hηbound⟩ :=
      exists_eLpNorm_indicator_le
        (α := X) (E := ℂ) (p := 2) (μ := μ)
        (by norm_num) c hhalf
    rcases profinite_exists_clopen_symmDiff_lt (μ := μ) hs
        (ε := (η : ℝ≥0∞)) (ENNReal.coe_ne_zero.mpr hηpos.ne') with
      ⟨C, hC, hμC⟩
    let g := (LocallyConstant.const X c).indicator hC
    refine ⟨T g, ⟨g, rfl⟩, ?_⟩
    rw [show T g = profiniteLocallyConstantToL2 g from rfl,
      profiniteLocallyConstantIndicatorToL2_eq]
    rw [edist_indicatorConstLp_eq_enorm]
    calc
      ‖indicatorConstLp 2
          (hs.symmDiff hC.2.measurableSet)
          (measure_ne_top μ (s ∆ C)) c‖ₑ =
          eLpNorm ((s ∆ C).indicator fun _ => c) 2 μ := by
        rw [indicatorConstLp, Lp.enorm_toLp]
      _ ≤ ε / 2 := hηbound _ (by
        rw [symmDiff_comm]
        exact hμC.le)
      _ < ε := ENNReal.half_lt_self hε.ne' hεtop
  have hall : ∀ f : Lp ℂ 2 μ, f ∈ V.topologicalClosure := by
    intro f
    apply Lp.induction
      (p := 2) (μ := μ)
      (motive := fun u => u ∈ V.topologicalClosure)
      (by norm_num)
    · intro c s hs hμs
      simpa only [Lp.simpleFunc.coe_indicatorConst, V] using
        hindicator c hs
    · intro u v hu hv huv hu' hv'
      exact V.topologicalClosure.add_mem hu' hv'
    · exact Submodule.isClosed_topologicalClosure V
  have htop : V.topologicalClosure = ⊤ :=
    eq_top_iff.mpr (fun f _ => hall f)
  rw [denseRange_iff_closure_range]
  simpa only [T, V, Submodule.topologicalClosure_coe,
    Submodule.top_coe, LinearMap.coe_range] using
    congrArg
      (fun U : Submodule ℂ (Lp ℂ 2 μ) => (U : Set (Lp ℂ 2 μ)))
      htop

end

end GaloisForLFunctions.RHTower
