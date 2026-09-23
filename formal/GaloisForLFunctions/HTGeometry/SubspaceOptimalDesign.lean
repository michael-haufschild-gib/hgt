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

variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]

theorem stdSimplex_nonempty (C : Type*) [Fintype C] [Nonempty C] [DecidableEq C] :
    ∃ w : C → ℝ, w ∈ stdSimplex ℝ C := by
  classical
  refine ⟨fun c => if c = Classical.arbitrary C then 1 else 0, fun c => ?_, ?_⟩
  · by_cases h : c = Classical.arbitrary C <;> simp [h]
  · simp

/-- The coordinate design law at every positive dimension. -/
theorem exists_optimalDesign_coord {m : ℕ} (hm : 0 < m) (T : C → Fin m → ℂ)
    (hspanT : Submodule.span ℂ (Set.range T) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C, ∀ (u : Fin m → ℂ) (c : C),
      ‖finiteComplexInner u (T c)‖ ^ (2 : ℕ) ≤
        (m : ℝ) * ∑ j, w j * ‖finiteComplexInner u (T j)‖ ^ (2 : ℕ) := by
  rcases m with _ | m
  · exact absurd hm (lt_irrefl 0)
  · simpa using exists_finiteOptimalDesign_pointwise T hspanT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Carrier design law.**  A finite spanning family of a finite-dimensional complex
inner-product space carries a probability design whose leverage is at most the dimension of that
space. -/
theorem exists_optimalDesign_of_span_top (v : C → E)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C, ∀ (u : E) (c : C),
      ‖(inner ℂ u (v c) : ℂ)‖ ^ (2 : ℕ) ≤
        (Module.finrank ℂ E : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ (2 : ℕ) := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ E) with hn | hn
  · obtain ⟨w, hw⟩ := stdSimplex_nonempty C
    refine ⟨w, hw, fun u c => ?_⟩
    have htop : (⊤ : Submodule ℂ E) = ⊥ := by
      have hzero := Submodule.finrank_eq_zero (R := ℂ) (M := E) (S := (⊤ : Submodule ℂ E))
      rw [finrank_top] at hzero
      exact hzero.mp hn
    have hv : v c = 0 := by
      have hmem : v c ∈ (⊤ : Submodule ℂ E) := Submodule.mem_top
      rw [htop] at hmem
      exact hmem
    rw [hv, inner_zero_right, norm_zero]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℂ E : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ (2 : ℕ) := by
      refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
      exact mul_nonneg (hw.1 j) (sq_nonneg _)
    simpa using hnn
  · set e : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
      (stdOrthonormalBasis ℂ E).repr with he
    set T : C → (Fin (Module.finrank ℂ E) → ℂ) := fun c => (e (v c)).ofLp with hT
    have hinnerT : ∀ (u : E) (c : C),
        finiteComplexInner ((e u).ofLp) (T c) = (inner ℂ u (v c) : ℂ) := by
      intro u c
      rw [hT, ← inner_toLp_eq_finiteComplexInner]
      simp [e.inner_map_map]
    have hspanT : Submodule.span ℂ (Set.range T) = ⊤ := by
      refine Submodule.eq_top_iff'.mpr fun y => ?_
      have hy : y = (e (e.symm (WithLp.toLp 2 y))).ofLp := by simp
      rw [hy]
      have hx : e.symm (WithLp.toLp 2 y) ∈ Submodule.span ℂ (Set.range v) := by
        rw [hspan]; exact Submodule.mem_top
      refine Submodule.span_induction (p := fun x _ =>
        ((e x).ofLp : Fin (Module.finrank ℂ E) → ℂ) ∈ Submodule.span ℂ (Set.range T))
        ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨c, rfl⟩
        exact Submodule.subset_span ⟨c, rfl⟩
      · simp
      · intro x₁ x₂ _ _ h₁ h₂
        have hadd : ((e (x₁ + x₂)).ofLp : Fin (Module.finrank ℂ E) → ℂ) =
            (e x₁).ofLp + (e x₂).ofLp := by simp
        rw [hadd]
        exact Submodule.add_mem _ h₁ h₂
      · intro a x₁ _ h₁
        have hsmul : ((e (a • x₁)).ofLp : Fin (Module.finrank ℂ E) → ℂ) = a • (e x₁).ofLp := by
          simp
        rw [hsmul]
        exact Submodule.smul_mem _ a h₁
    obtain ⟨w, hw, hdesign⟩ := exists_optimalDesign_coord hn T hspanT
    refine ⟨w, hw, fun u c => ?_⟩
    have hbase := hdesign ((e u).ofLp) c
    rw [hinnerT u c] at hbase
    refine le_trans hbase (le_of_eq ?_)
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hinnerT u j]

end Transport

section Carrier

variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Carrier design law, ambient form.**  A finite family spanning a submodule carries a
probability design whose leverage is at most the dimension of that submodule, uniformly over
ambient probes. -/
theorem exists_optimalDesign_of_span_eq {U : Submodule ℂ H} (v : C → H) (hv : ∀ c, v c ∈ U)
    (hspan : Submodule.span ℂ (Set.range v) = U) :
    ∃ w ∈ stdSimplex ℝ C, ∀ (u : H) (c : C),
      ‖(inner ℂ u (v c) : ℂ)‖ ^ (2 : ℕ) ≤
        (Module.finrank ℂ U : ℝ) * ∑ j, w j * ‖(inner ℂ u (v j) : ℂ)‖ ^ (2 : ℕ) := by
  classical
  set v' : C → U := fun c => ⟨v c, hv c⟩ with hv'
  have hrange : U.subtype '' (Set.range v') = Set.range v := by
    ext y
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨v' c, ⟨c, rfl⟩, rfl⟩
  have hspan' : Submodule.span ℂ (Set.range v') = ⊤ := by
    have hmap : (Submodule.span ℂ (Set.range v')).map U.subtype = Submodule.span ℂ (Set.range v) := by
      rw [← Submodule.span_image, hrange]
    have htop : ((⊤ : Submodule ℂ U)).map U.subtype = U := Submodule.map_subtype_top U
    refine Submodule.map_injective_of_injective (Submodule.injective_subtype U) ?_
    rw [hmap, hspan, htop]
  obtain ⟨w, hw, hdesign⟩ := exists_optimalDesign_of_span_top v' hspan'
  refine ⟨w, hw, fun u c => ?_⟩
  have hproj : ∀ c : C, (inner ℂ (U.starProjection u) (v c) : ℂ) = inner ℂ u (v c) := by
    intro c
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hv c)]
  have hinner : ∀ c : C,
      (inner ℂ (⟨U.starProjection u, U.starProjection_apply_mem u⟩ : U) (v' c) : ℂ) =
        inner ℂ u (v c) := by
    intro c
    rw [← hproj c]
    rfl
  have hbase := hdesign ⟨U.starProjection u, U.starProjection_apply_mem u⟩ c
  rw [hinner c] at hbase
  refine le_trans hbase (le_of_eq ?_)
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hinner j]

variable {X : Type*}

/-- The surviving light-source incidence carrier: the span of the target-span projections of the
occupied source generators. -/
def incidenceCarrier (S : Submodule ℂ H) (g : X → H) (A : Set X) : Submodule ℂ H :=
  Submodule.span ℂ ((fun x => S.starProjection (g x)) '' A)

theorem incidenceCarrier_le (S : Submodule ℂ H) (g : X → H) (A : Set X) :
    incidenceCarrier S g A ≤ S := by
  rw [incidenceCarrier]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, -, rfl⟩
  exact S.starProjection_apply_mem _

theorem starProjection_of_le {U S : Submodule ℂ H} (h : U ≤ S) (x : H) :
    U.starProjection (S.starProjection x) = U.starProjection x := by
  have h1 : x - S.starProjection x ∈ Uᗮ :=
    Submodule.orthogonal_le h (S.sub_starProjection_mem_orthogonal x)
  have h2 : S.starProjection x - U.starProjection (S.starProjection x) ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal _
  have h3 : x - U.starProjection (S.starProjection x) ∈ Uᗮ := by
    have hrw : x - U.starProjection (S.starProjection x) =
        (x - S.starProjection x) +
          (S.starProjection x - U.starProjection (S.starProjection x)) := by
      abel
    rw [hrw]
    exact Submodule.add_mem _ h1 h2
  exact (Submodule.eq_starProjection_of_mem_orthogonal
    (U.starProjection_apply_mem (S.starProjection x)) h3).symm

/-- **Equation `(14)`.**  Inside the carrier the nested projection of an occupied generator agrees
with its target-span projection. -/
theorem starProjection_incidenceCarrier_eq {S : Submodule ℂ H} {g : X → H} {A : Set X} {x : X}
    (hx : x ∈ A) :
    (incidenceCarrier S g A).starProjection (g x) = S.starProjection (g x) := by
  have h1 : (incidenceCarrier S g A).starProjection (S.starProjection (g x)) =
      S.starProjection (g x) := by
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  rw [← starProjection_of_le (incidenceCarrier_le S g A) (g x), h1]

/-- **Equation `(15)`.**  Projecting a target into the carrier preserves its incidence with every
occupied generator. -/
theorem inner_incidenceCarrier_target {S : Submodule ℂ H} {g : X → H} {A : Set X} {t : H}
    (ht : t ∈ S) {x : X} (hx : x ∈ A) :
    (inner ℂ (g x) ((incidenceCarrier S g A).starProjection t) : ℂ) = inner ℂ (g x) t := by
  rw [← Submodule.inner_starProjection_left_eq_right,
    starProjection_incidenceCarrier_eq hx,
    Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr ht]

/-- The carrier is spanned by the carrier projections of the targets. -/
theorem span_starProjection_incidenceCarrier {S : Submodule ℂ H} {g : X → H} {A : Set X}
    {z : C → H} (hspanS : Submodule.span ℂ (Set.range z) = S) :
    Submodule.span ℂ
      (Set.range fun c => (incidenceCarrier S g A).starProjection (z c)) =
      incidenceCarrier S g A := by
  classical
  set U := incidenceCarrier S g A with hU
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    exact U.starProjection_apply_mem _
  · rw [hU, incidenceCarrier]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    show S.starProjection (g x) ∈ Submodule.span ℂ (Set.range fun c => U.starProjection (z c))
    have hmem : S.starProjection (g x) ∈ Submodule.span ℂ (Set.range z) := by
      rw [hspanS]
      exact S.starProjection_apply_mem _
    have hkey : U.starProjection (S.starProjection (g x)) = S.starProjection (g x) := by
      rw [Submodule.starProjection_eq_self_iff, hU]
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← hkey]
    refine Submodule.span_induction (p := fun y _ => U.starProjection y ∈
      Submodule.span ℂ (Set.range fun c => U.starProjection (z c))) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨c, rfl⟩
    · simp
    · intro y₁ y₂ _ _ h₁ h₂
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂
    · intro a y₁ _ h₁
      rw [map_smul]
      exact Submodule.smul_mem _ a h₁

end Carrier


end GaloisForLFunctions.HTGeometry
