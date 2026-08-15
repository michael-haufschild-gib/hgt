import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw

/-!
# The optimal design law inside an arbitrary finite-dimensional carrier

A finite spanning family of a finite-dimensional complex inner-product space carries a probability
design whose leverage is at most the dimension of that space: every probe is controlled by the
design average of the probes at the family, with the dimension of the carrier as the only factor.

The coordinate case is the occupied-endpoint design law; transporting it along the orthonormal
coordinate isometry of the carrier removes the coordinate hypothesis, so the design factor becomes
the dimension of the actual carrier rather than that of any ambient space containing it.
-/

open MeasureTheory Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]

theorem stdSimplex_nonempty (C : Type*) [Fintype C] [Nonempty C] [DecidableEq C] :
    ∃ w : C → ℝ, w ∈ stdSimplex ℝ C := by
  classical
  refine ⟨fun c => if c = Classical.arbitrary C then 1 else 0, ?_, ?_⟩
  · intro c
    split <;> norm_num
  · rw [Finset.sum_ite_eq' Finset.univ (Classical.arbitrary C) (fun _ => (1 : ℝ))]
    simp

/-- **Carrier design law.**  A finite spanning family of a finite-dimensional complex
inner-product space carries a probability design whose leverage is at most the dimension of that
space. -/
theorem exists_optimalDesign_of_span_top (v : C → E)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C, ∀ (u : E) (c : C),
      ‖(inner ℂ u (v c) : ℂ)‖ ^ 2 ≤
        (Module.finrank ℂ E : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ E) with hn | hn
  · -- the carrier is trivial, so every family member vanishes
    obtain ⟨w, hw⟩ := stdSimplex_nonempty C
    refine ⟨w, hw, fun u c => ?_⟩
    have htop : (⊤ : Submodule ℂ E) = ⊥ := by
      have := Submodule.finrank_eq_zero (R := ℂ) (M := E) (S := (⊤ : Submodule ℂ E))
      rw [finrank_top] at this
      exact this.mp hn
    have hv : v c = 0 := by
      have : v c ∈ (⊤ : Submodule ℂ E) := Submodule.mem_top
      rw [htop] at this
      exact this
    rw [hv, inner_zero_right, norm_zero]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℂ E : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ 2 := by
      refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
      exact mul_nonneg (hw.1 j) (sq_nonneg _)
    simpa using hnn
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, Module.finrank ℂ E = m + 1 := ⟨Module.finrank ℂ E - 1, by omega⟩
    set b := stdOrthonormalBasis ℂ E with hb
    set e : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) := b.repr with he
    set T : C → (Fin (Module.finrank ℂ E) → ℂ) := fun c => (e (v c)).ofLp with hT
    have hinnerT : ∀ (u : E) (c : C),
        finiteComplexInner ((e u).ofLp) (T c) = (inner ℂ u (v c) : ℂ) := by
      intro u c
      rw [hT, ← inner_toLp_eq_finiteComplexInner]
      simp [e.inner_map_map]
    have hspanT : Submodule.span ℂ (Set.range T) = ⊤ := by
      have hsurj : Function.Surjective (fun x : E => ((e x).ofLp : Fin (Module.finrank ℂ E) → ℂ)) :=
        fun y => ⟨e.symm (WithLp.toLp 2 y), by simp⟩
      refine Submodule.eq_top_iff'.mpr fun y => ?_
      obtain ⟨x, rfl⟩ := hsurj y
      have hx : x ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; exact Submodule.mem_top
      refine Submodule.span_induction (p := fun x _ =>
        ((e x).ofLp : Fin (Module.finrank ℂ E) → ℂ) ∈ Submodule.span ℂ (Set.range T)) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨c, rfl⟩
        exact Submodule.subset_span ⟨c, rfl⟩
      · simpa using Submodule.zero_mem _
      · intro x y _ _ hx hy
        have : ((e (x + y)).ofLp : Fin (Module.finrank ℂ E) → ℂ) =
            (e x).ofLp + (e y).ofLp := by simp
        rw [this]
        exact Submodule.add_mem _ hx hy
      · intro a x _ hx
        have : ((e (a • x)).ofLp : Fin (Module.finrank ℂ E) → ℂ) = a • (e x).ofLp := by simp
        rw [this]
        exact Submodule.smul_mem _ a hx
    have hcast : ∃ T' : C → (Fin (m + 1) → ℂ), Submodule.span ℂ (Set.range T') = ⊤ ∧
        ∀ (u : E) (c : C), ‖finiteComplexInner ((hm ▸ (e u).ofLp : Fin (m + 1) → ℂ)) (T' c)‖ =
          ‖(inner ℂ u (v c) : ℂ)‖ := by
      subst hm
      exact ⟨T, hspanT, fun u c => by rw [hinnerT]⟩
    obtain ⟨T', hspanT', hnormT'⟩ := hcast
    obtain ⟨w, hw, hdesign⟩ := exists_finiteOptimalDesign_pointwise T' hspanT'
    refine ⟨w, hw, fun u c => ?_⟩
    have hbase := hdesign ((hm ▸ (e u).ofLp : Fin (m + 1) → ℂ)) c
    rw [hnormT' u c] at hbase
    have hrw : ∀ j : C, ‖finiteComplexInner ((hm ▸ (e u).ofLp : Fin (m + 1) → ℂ)) (T' j)‖ =
        ‖(inner ℂ u (v j) : ℂ)‖ := fun j => hnormT' u j
    calc ‖(inner ℂ u (v c) : ℂ)‖ ^ 2
        ≤ ((m : ℝ) + 1) * ∑ j, w j *
            ‖finiteComplexInner ((hm ▸ (e u).ofLp : Fin (m + 1) → ℂ)) (T' j)‖ ^ 2 := hbase
      _ = (Module.finrank ℂ E : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ 2 := by
          rw [hm]
          push_cast
          refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
          rw [hrw j]

end Transport

end GaloisForLFunctions.HTGeometry
