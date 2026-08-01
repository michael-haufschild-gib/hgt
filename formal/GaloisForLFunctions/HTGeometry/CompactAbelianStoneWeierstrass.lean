import GaloisForLFunctions.HTGeometry.CompactAbelianPeterWeyl

/-!
# Trigonometric polynomials are dense on a compact abelian group

The continuous characters are closed under multiplication and conjugation and contain the constant
one, so their linear span is a star-subalgebra of `C(G, ℂ)`.  By Peter–Weyl it separates points, so
by Stone–Weierstrass it is dense: every continuous function on a compact abelian group is a uniform
limit of finite linear combinations of characters.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]

/-- A continuous character of `G`. -/
structure IsGroupChar (χ : C(G, ℂ)) : Prop where
  map_add : ∀ x y : G, χ (x + y) = χ x * χ y
  norm_one : ∀ x : G, ‖χ x‖ = 1

omit [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] in
theorem isGroupChar_one : IsGroupChar (1 : C(G, ℂ)) where
  map_add _ _ := by simp
  norm_one _ := by simp

omit [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] in
theorem IsGroupChar.mul {χ ψ : C(G, ℂ)} (hχ : IsGroupChar χ) (hψ : IsGroupChar ψ) :
    IsGroupChar (χ * ψ) where
  map_add x y := by
    simp only [ContinuousMap.mul_apply, hχ.map_add, hψ.map_add]
    ring
  norm_one x := by
    simp only [ContinuousMap.mul_apply, norm_mul, hχ.norm_one, hψ.norm_one, one_mul]

omit [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] in
theorem IsGroupChar.star {χ : C(G, ℂ)} (hχ : IsGroupChar χ) : IsGroupChar (star χ) where
  map_add x y := by
    show (starRingEnd ℂ) (χ (x + y)) = (starRingEnd ℂ) (χ x) * (starRingEnd ℂ) (χ y)
    rw [hχ.map_add, map_mul]
  norm_one x := by
    show ‖(starRingEnd ℂ) (χ x)‖ = 1
    rw [RCLike.norm_conj, hχ.norm_one]

/-- The linear span of the continuous characters. -/
def charSpanSubmodule (G : Type*) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ {p : C(G, ℂ) | IsGroupChar p}

theorem mem_charSpanSubmodule_of_isGroupChar {χ : C(G, ℂ)} (hχ : IsGroupChar χ) :
    χ ∈ charSpanSubmodule G :=
  Submodule.subset_span hχ

theorem mul_mem_charSpanSubmodule {p q : C(G, ℂ)} (hp : p ∈ charSpanSubmodule G)
    (hq : q ∈ charSpanSubmodule G) : p * q ∈ charSpanSubmodule G := by
  refine Submodule.span_induction (p := fun x _ => x * q ∈ charSpanSubmodule G) ?_ ?_ ?_ ?_ hp
  · intro χ hχ
    refine Submodule.span_induction (p := fun y _ => χ * y ∈ charSpanSubmodule G) ?_ ?_ ?_ ?_ hq
    · intro ψ hψ
      exact mem_charSpanSubmodule_of_isGroupChar (IsGroupChar.mul hχ hψ)
    · simp
    · intro y z _ _ hy hz
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    · intro c y _ hy
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

theorem star_mem_charSpanSubmodule {p : C(G, ℂ)} (hp : p ∈ charSpanSubmodule G) :
    star p ∈ charSpanSubmodule G := by
  refine Submodule.span_induction (p := fun x _ => star x ∈ charSpanSubmodule G) ?_ ?_ ?_ ?_ hp
  · intro χ hχ
    exact mem_charSpanSubmodule_of_isGroupChar hχ.star
  · simp
  · intro x y _ _ hx hy
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [star_smul]
    exact Submodule.smul_mem _ _ hx

/-- The star-subalgebra of trigonometric polynomials. -/
def charSubalgebra (G : Type*) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] : StarSubalgebra ℂ C(G, ℂ) where
  toSubalgebra := (charSpanSubmodule G).toSubalgebra
    (mem_charSpanSubmodule_of_isGroupChar isGroupChar_one)
    (fun _ _ hx hy => mul_mem_charSpanSubmodule hx hy)
  star_mem' := star_mem_charSpanSubmodule

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- **The trigonometric polynomials separate points**, by Peter–Weyl. -/
theorem charSubalgebra_separatesPoints : (charSubalgebra G).SeparatesPoints := by
  rintro x y hxy
  obtain ⟨χ, hcont, hmul, hnorm, hne⟩ := exists_character_ne_one (g := x - y)
    (by
      intro h
      exact hxy (by rwa [sub_eq_zero] at h))
  refine ⟨fun z => χ z, ⟨⟨χ, hcont⟩, ?_, rfl⟩, ?_⟩
  · exact mem_charSpanSubmodule_of_isGroupChar ⟨hmul, hnorm⟩
  · intro hEq
    apply hne
    have hxy' : χ (x - y) * χ y = χ x := by
      rw [← hmul]
      congr 1
      abel
    have hEq' : χ x = χ y := hEq
    rw [hEq'] at hxy'
    have hy0 : χ y ≠ 0 := by
      intro h0
      have := hnorm y
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    field_simp at hxy'
    exact hxy'

/-- **Stone–Weierstrass:** the trigonometric polynomials are dense in `C(G, ℂ)`. -/
theorem charSubalgebra_topologicalClosure_eq_top :
    (charSubalgebra G).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    charSubalgebra_separatesPoints

/-- **Every continuous function on a compact abelian group is uniformly approximated by finite
linear combinations of characters.** -/
theorem exists_char_combination_approx (F : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (χ : Fin n → C(G, ℂ)),
      (∀ j, IsGroupChar (χ j)) ∧ ‖F - ∑ j, c j • χ j‖ < ε := by
  classical
  have hmem : F ∈ (charSubalgebra G).topologicalClosure := by
    rw [charSubalgebra_topologicalClosure_eq_top]
    trivial
  have hclosure : F ∈ closure ((charSubalgebra G : StarSubalgebra ℂ C(G, ℂ)) : Set C(G, ℂ)) :=
    hmem
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  have hpspan : p ∈ charSpanSubmodule G := hp
  obtain ⟨n, f, g, hg⟩ := Submodule.mem_span_set'.mp hpspan
  refine ⟨n, f, fun j => (g j : C(G, ℂ)), fun j => (g j).2, ?_⟩
  rw [hg, ← dist_eq_norm]
  exact hdist

end

end CompactAbelian

end GaloisForLFunctions
