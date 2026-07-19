import GaloisForLFunctions.HTGeometry.WeakLimitTransfer
import GaloisForLFunctions.HTGeometry.ParameterMotion

/-!
# Weak continuity of the leaf in the parameter

Tightness makes the leaf family relatively compact, so along any sequence of parameters some
subsequence of leaves converges weakly.  The limit represents the sequence, because every leaf does,
and it is carried by the fiber of the limiting parameter, because nearby parameters have no fiber
point on a compact set away from it.  Uniqueness then identifies the limit as the leaf there, and
since every subsequential limit is the same point the whole family converges.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A leaf of a nearby parameter misses a compact set away from the fiber.** -/
theorem exists_param_radius_nevLeaf_eq_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (t₀ : ℝ) {L : Set ℝ} (hL : IsCompact L)
    (hLF : ∀ x ∈ L, nevBrealInf s x * t₀ - nevDrealInf s x ≠ 0) :
    ∃ ρ > 0, ∀ t : ℝ, |t - t₀| < ρ →
      (nevLeaf h h0b h0 (t : OnePoint ℝ) : Measure ℝ) L = 0 := by
  obtain ⟨ρ, hρ, hall⟩ := exists_param_radius_no_zero h h0b t₀ hL hLF
  refine ⟨ρ, hρ, fun t ht => ?_⟩
  have hsub : L ⊆ ((nevMatrixDataInf h h0b).finiteDenominatorFiber t)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
      nevMatrixDataInf]
    exact hall t ht x hx
  exact le_antisymm
    (le_trans (measure_mono hsub) (le_of_eq (nevLeaf_finite_carried h h0b h0 t))) zero_le

/-- The leaf family has compact closure. -/
theorem isCompact_closure_range_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    IsCompact (closure (Set.range fun t : OnePoint ℝ => nevLeaf h h0b h0 t)) := by
  refine isCompact_closure_of_isTightMeasureSet ?_
  have hcoe : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) |
        μ ∈ Set.range fun t : OnePoint ℝ => nevLeaf h h0b h0 t}
      = Set.range fun t : OnePoint ℝ => (nevLeaf h h0b h0 t : Measure ℝ) := by
    ext W
    constructor
    · rintro ⟨μ, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨nevLeaf h h0b h0 t, ⟨t, rfl⟩, rfl⟩
  rw [hcoe]
  exact isTightMeasureSet_nevLeaf h h0b h0

/-- **The leaf is weakly continuous in a finite parameter.** -/
theorem continuousAt_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ => nevLeaf h h0b h0 (t : OnePoint ℝ)) t₀ := by
  rw [ContinuousAt]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hmem : ∀ k, nevLeaf h h0b h0 ((ns k : ℝ) : OnePoint ℝ)
      ∈ closure (Set.range fun t : OnePoint ℝ => nevLeaf h h0b h0 t) :=
    fun k => subset_closure (Set.mem_range_self _)
  obtain ⟨ν, -, ms, hms, hlim⟩ :=
    (isCompact_closure_range_nevLeaf h h0b h0).tendsto_subseq hmem
  refine ⟨ms, ?_⟩
  -- the limit represents the sequence
  have hmomν : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (ν : Measure ℝ) :=
    hasHamburgerMoments_of_tendsto h h0
      (fun k => nevLeaf_hasHamburgerMoments h h0b h0 ((ns (ms k) : ℝ) : OnePoint ℝ)) hlim
  -- the limit is carried by the fiber of t₀
  have hcarν : (ν : Measure ℝ)
      {x : ℝ | nevBrealInf s x * t₀ - nevDrealInf s x ≠ 0} = 0 := by
    refine measure_eq_zero_of_tendsto hlim (isOpen_denominator_ne_zero h h0b t₀) ?_
    intro L hLc hLU
    obtain ⟨ρ, hρ, hall⟩ := exists_param_radius_nevLeaf_eq_zero h h0b h0 t₀ hLc
      (fun x hx => hLU hx)
    have hns' : Tendsto (fun k => ns (ms k)) atTop (nhds t₀) :=
      hns.comp hms.tendsto_atTop
    have hclose : ∀ᶠ k in atTop, |ns (ms k) - t₀| < ρ := by
      have := Metric.tendsto_atTop.mp hns' ρ hρ
      obtain ⟨N, hN⟩ := this
      refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have := hN k hk
      rwa [Real.dist_eq] at this
    filter_upwards [hclose] with k hk
    exact hall _ hk
  have hcarν' : (ν : Measure ℝ)
      ((nevMatrixDataInf h h0b).finiteDenominatorFiber t₀)ᶜ = 0 := by
    have hset : ((nevMatrixDataInf h h0b).finiteDenominatorFiber t₀)ᶜ
        = {x : ℝ | nevBrealInf s x * t₀ - nevDrealInf s x ≠ 0} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
        GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
        nevMatrixDataInf]
    rw [hset]
    exact hcarν
  haveI : IsProbabilityMeasure (ν : Measure ℝ) := ν.prop
  have hνeq : (ν : Measure ℝ) = (nevLeaf h h0b h0 (t₀ : OnePoint ℝ) : Measure ℝ) :=
    nevLeaf_unique h h0b h0 t₀ hmomν hcarν'
  have hsub : ν = nevLeaf h h0b h0 (t₀ : OnePoint ℝ) := Subtype.ext hνeq
  rw [← hsub]
  exact hlim

end HTGeometry
