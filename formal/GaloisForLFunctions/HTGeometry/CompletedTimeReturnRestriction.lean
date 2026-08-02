import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-!
# Exact return and observer restriction in completed time

A finite frequency packet has an exact nonzero return of its phase flow exactly when its completed
time is at most one dimensional: an exact return forces all frequencies onto one rational line, and
conversely a rank-one packet is an integer multiple of a single frequency, whose period returns the
whole packet.

Restricting an observer to part of the packet is coordinate projection of the phase torus.  It maps
completed time onto completed time and cannot raise temporal dimension.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d d' : Type*} [Fintype d] [Fintype d']

/-- **Exact return.**  The phase flow of a finite frequency packet returns exactly to its start at
some nonzero time precisely when its completed time is at most one dimensional. -/
theorem exists_ne_zero_return_iff (omega : d → ℝ) :
    (∃ t : ℝ, t ≠ 0 ∧ finiteClockPhasePoint omega t = 0)
      ↔ Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) ≤ 1 := by
  constructor
  · rintro ⟨t, ht, hflow⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hint : ∀ i, ∃ m : ℤ, t * omega i / (2 * Real.pi) = (m : ℝ) := by
      intro i
      have hi : ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0 := congrFun hflow i
      obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
      exact ⟨m, by rw [← hm]; simp⟩
    choose m hm using hint
    have hsub : Submodule.span ℚ (Set.range omega)
        ≤ Submodule.span ℚ ({2 * Real.pi / t} : Set ℝ) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have h1 : t * omega i = (m i : ℝ) * (2 * Real.pi) := (div_eq_iff hpi).mp (hm i)
      have hval : ((m i : ℚ) : ℝ) * (2 * Real.pi / t) = omega i := by
        push_cast
        rw [← mul_div_assoc, ← h1, mul_comm t (omega i), mul_div_assoc, div_self ht, mul_one]
      refine Submodule.mem_span_singleton.mpr ⟨(m i : ℚ), ?_⟩
      rw [Rat.smul_def]
      exact hval
    have hfin : Module.finrank ℚ (Submodule.span ℚ ({2 * Real.pi / t} : Set ℝ)) ≤ 1 := by
      have := finrank_span_le_card (R := ℚ) ({2 * Real.pi / t} : Set ℝ)
      simpa using this
    exact le_trans (Submodule.finrank_mono hsub) hfin
  · intro hrank
    obtain ⟨k, gamma, M, A, -, -, -, hM, -, hk⟩ := exists_frequency_integer_basis omega
    rw [← hk] at hrank
    interval_cases k
    · refine ⟨1, one_ne_zero, ?_⟩
      funext i
      have hzero : omega i = 0 := by
        rw [hM i]
        simp
      show ((1 * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0
      rw [hzero]
      simp
    · by_cases hg : gamma 0 = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        funext i
        have hzero : omega i = 0 := by
          rw [hM i, Fin.sum_univ_one, hg, mul_zero]
        show ((1 * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0
        rw [hzero]
        simp
      · refine ⟨2 * Real.pi / gamma 0, div_ne_zero (by positivity) hg, ?_⟩
        funext i
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        have hval : (2 * Real.pi / gamma 0) * omega i / (2 * Real.pi) = (M i 0 : ℝ) := by
          rw [hM i, Fin.sum_univ_one]
          field_simp
        show (((2 * Real.pi / gamma 0) * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0
        rw [hval]
        exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨M i 0, by simp⟩

/-- Coordinate projection of the phase torus along a reindexing of the packet. -/
def phaseRestrict (f : d' → d) (x : UnitAddTorus d) : UnitAddTorus d' := fun i => x (f i)

omit [Fintype d] [Fintype d'] in
theorem continuous_phaseRestrict (f : d' → d) :
    Continuous (phaseRestrict (d := d) (d' := d') f) :=
  continuous_pi fun i => continuous_apply (f i)

theorem phaseRestrict_finiteClockPhasePoint (omega : d → ℝ) (f : d' → d) (t : ℝ) :
    phaseRestrict f (finiteClockPhasePoint omega t) = finiteClockPhasePoint (omega ∘ f) t := rfl

/-- **Observer restriction.**  Restricting the observed packet projects completed time onto
completed time. -/
theorem image_closure_range_phaseRestrict (omega : d → ℝ) (f : d' → d) :
    phaseRestrict f '' closure (Set.range (finiteClockPhasePoint omega))
      = closure (Set.range (finiteClockPhasePoint (omega ∘ f))) := by
  have hrange : phaseRestrict f '' Set.range (finiteClockPhasePoint omega)
      = Set.range (finiteClockPhasePoint (omega ∘ f)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, phaseRestrict_finiteClockPhasePoint omega f t⟩
    · rintro ⟨t, rfl⟩
      exact ⟨finiteClockPhasePoint omega t, ⟨t, rfl⟩,
        phaseRestrict_finiteClockPhasePoint omega f t⟩
  refine le_antisymm ?_ ?_
  · rw [← hrange]
    exact image_closure_subset_closure_image (continuous_phaseRestrict f)
  · have hcl : IsClosed (phaseRestrict f '' closure (Set.range (finiteClockPhasePoint omega))) :=
      (isClosed_closure.isCompact.image (continuous_phaseRestrict f)).isClosed
    refine closure_minimal ?_ hcl
    rw [← hrange]
    exact Set.image_mono subset_closure

omit [Fintype d'] in
/-- **Temporal dimension cannot increase under restriction.** -/
theorem finrank_span_restrict_le (omega : d → ℝ) (f : d' → d) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (omega ∘ f)))
      ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) := by
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range omega)) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range omega)
  refine Submodule.finrank_mono (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, rfl⟩

end

end GaloisForLFunctions.HTGeometry
