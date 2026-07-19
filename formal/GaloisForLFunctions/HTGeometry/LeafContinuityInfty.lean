import GaloisForLFunctions.HTGeometry.LeafContinuity

/-!
# Weak continuity at the parameter infinity

A fiber point of `t` in a compact set where `B` does not vanish forces `|t| = |D(x)|/|B(x)|`, which is
bounded there.  So large parameters have no fiber point on such a set, and the argument of the finite
case runs with "large `|t|`" in place of "`t` near `t₀`", closing with uniqueness at infinity.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Large parameters have no fiber point where `B` does not vanish.** -/
theorem exists_param_bound_no_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {L : Set ℝ} (hL : IsCompact L) (hLB : ∀ x ∈ L, nevBrealInf s x ≠ 0) :
    ∃ M > 0, ∀ t : ℝ, M < |t| → ∀ x ∈ L, nevBrealInf s x * t - nevDrealInf s x ≠ 0 := by
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · exact ⟨1, one_pos, fun t _ x hx => absurd hx (Set.notMem_empty x)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hL.exists_isMinOn hLne
    (continuous_nevBrealInf h h0b).abs.continuousOn
  obtain ⟨x₁, hx₁, hmax⟩ := hL.exists_isMaxOn hLne
    (continuous_nevDrealInf h h0b).abs.continuousOn
  set b : ℝ := |nevBrealInf s x₀| with hbdef
  set d : ℝ := |nevDrealInf s x₁| with hddef
  have hb : 0 < b := abs_pos.mpr (hLB x₀ hx₀)
  refine ⟨d / b + 1, by positivity, fun t ht x hx hzero => ?_⟩
  have hBx : b ≤ |nevBrealInf s x| := hmin hx
  have hDx : |nevDrealInf s x| ≤ d := hmax hx
  have heq : nevBrealInf s x * t = nevDrealInf s x := by linarith
  have habs : |nevBrealInf s x| * |t| = |nevDrealInf s x| := by
    rw [← abs_mul, heq]
  have h1 : b * |t| ≤ d := by
    calc b * |t| ≤ |nevBrealInf s x| * |t| := mul_le_mul_of_nonneg_right hBx (abs_nonneg t)
      _ = |nevDrealInf s x| := habs
      _ ≤ d := hDx
  have h2 : |t| ≤ d / b := by
    rw [le_div_iff₀ hb]
    linarith
  linarith

/-- A leaf of a large parameter misses a compact set where `B` does not vanish. -/
theorem exists_param_bound_nevLeaf_eq_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {L : Set ℝ} (hL : IsCompact L) (hLB : ∀ x ∈ L, nevBrealInf s x ≠ 0) :
    ∃ M > 0, ∀ t : ℝ, M < |t| →
      (nevLeaf h h0b h0 (t : OnePoint ℝ) : Measure ℝ) L = 0 := by
  obtain ⟨M, hM, hall⟩ := exists_param_bound_no_zero h h0b hL hLB
  refine ⟨M, hM, fun t ht => ?_⟩
  have hsub : L ⊆ ((nevMatrixDataInf h h0b).finiteDenominatorFiber t)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
      nevMatrixDataInf]
    exact hall t ht x hx
  exact le_antisymm
    (le_trans (measure_mono hsub) (le_of_eq (nevLeaf_finite_carried h h0b h0 t))) zero_le

/-- **The leaf tends to the leaf at infinity as the parameter escapes every compact set.** -/
theorem tendsto_nevLeaf_cocompact (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Tendsto (fun t : ℝ => nevLeaf h h0b h0 (t : OnePoint ℝ)) (coclosedCompact ℝ)
      (nhds (nevLeaf h h0b h0 ∞)) := by
  rw [coclosedCompact_eq_cocompact]
  haveI : (Filter.cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]
    infer_instance
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hmem : ∀ k, nevLeaf h h0b h0 ((ns k : ℝ) : OnePoint ℝ)
      ∈ closure (Set.range fun t : OnePoint ℝ => nevLeaf h h0b h0 t) :=
    fun k => subset_closure (Set.mem_range_self _)
  obtain ⟨ν, -, ms, hms, hlim⟩ :=
    (isCompact_closure_range_nevLeaf h h0b h0).tendsto_subseq hmem
  refine ⟨ms, ?_⟩
  have hmomν : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (ν : Measure ℝ) :=
    hasHamburgerMoments_of_tendsto h h0
      (fun k => nevLeaf_hasHamburgerMoments h h0b h0 ((ns (ms k) : ℝ) : OnePoint ℝ)) hlim
  have hcarν : (ν : Measure ℝ) {x : ℝ | nevBrealInf s x ≠ 0} = 0 := by
    refine measure_eq_zero_of_tendsto hlim (isOpen_nevBrealInf_ne_zero h h0b) ?_
    intro L hLc hLU
    obtain ⟨M, hM, hall⟩ := exists_param_bound_nevLeaf_eq_zero h h0b h0 hLc (fun x hx => hLU hx)
    have hIcc : ((Set.Icc (-M) M)ᶜ) ∈ cocompact ℝ :=
      mem_cocompact.mpr ⟨Set.Icc (-M) M, isCompact_Icc, subset_rfl⟩
    have hns' : Tendsto (fun k => ns (ms k)) atTop (cocompact ℝ) :=
      hns.comp hms.tendsto_atTop
    have hbig : ∀ᶠ k in atTop, M < |ns (ms k)| := by
      filter_upwards [hns' hIcc] with k hk
      have hk' : ns (ms k) ∉ Set.Icc (-M) M := hk
      rw [Set.mem_Icc] at hk'
      push Not at hk'
      rcases lt_or_ge (ns (ms k)) (-M) with hlt | hge
      · rw [lt_abs]
        right
        linarith
      · have hgt := hk' hge
        rw [lt_abs]
        left
        linarith
    filter_upwards [hbig] with k hk
    exact hall _ hk
  have hcarν' : (ν : Measure ℝ)
      (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 := by
    have hset : (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ
        = {x : ℝ | nevBrealInf s x ≠ 0} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
        GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.infinityDenominatorFiber,
        nevMatrixDataInf]
    rw [hset]
    exact hcarν
  haveI : IsProbabilityMeasure (ν : Measure ℝ) := ν.prop
  have hνeq : (ν : Measure ℝ) = (nevLeaf h h0b h0 ∞ : Measure ℝ) :=
    nevLeaf_infinity_unique h h0b h0 hmomν hcarν'
  have hsub : ν = nevLeaf h h0b h0 ∞ := Subtype.ext hνeq
  rw [← hsub]
  exact hlim

/-- **The leaf map is weakly continuous.**  This is the `continuous_leaf` field. -/
theorem continuous_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Continuous (nevLeaf h h0b h0) := by
  rw [OnePoint.continuous_iff]
  exact ⟨tendsto_nevLeaf_cocompact h h0b h0,
    continuous_iff_continuousAt.mpr fun t => continuousAt_nevLeaf h h0b h0 t⟩

end HTGeometry
