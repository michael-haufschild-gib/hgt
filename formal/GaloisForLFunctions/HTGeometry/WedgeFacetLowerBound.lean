import Mathlib
import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# Dimension-three impossibility for the nonpure two-thick wedge

The lower-bound half of the exact faithful facet-separation dimension of the connected nonpure
two-thick complex `S¹ ∨ S²`: no faithful facet separation of this complex exists in a complex
vector space of dimension at most three, hence `ffsDim(Δ_wedge) ≥ 4`.

The complex has vertices `{0,…,5}` and seven facets — the three circle edges `{0,1},{1,2},{0,2}`
and the four sphere triangles `{0,3,4},{0,3,5},{0,4,5},{3,4,5}`, glued at vertex `0`.  A faithful
separation supplies vectors `a v` and forms `ℓ i` with the exact zero pattern
`ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i`.

The argument is pure complex linear algebra.  Set `L = span_ℂ{a₃,a₄,a₅}` (the sphere apex vectors).
Both forms `ℓ_{0,1}` and `ℓ_{1,2}` annihilate `a₃,a₄,a₅`, hence all of `L`.

* If `dim L ≤ 1`, then `a₅ ≠ 0` spans `L`, so `a₃ ∈ ℂ·a₅`; applying `ℓ_{0,3,4}` (which kills `a₅`,
  since `5 ∉ {0,3,4}`) forces `ℓ_{0,3,4}(a₃) = 0`, contradicting `3 ∈ {0,3,4}`.
* If `dim L ≥ 2`, then `a₀ ∈ L`: otherwise `L ⊔ ℂ·a₀` has dimension `≥ 3 ≥ dim E`, so equals the
  whole space, forcing `ℓ_{1,2}` (which kills `L` and `a₀`) to vanish identically, contradicting
  `1 ∈ {1,2}`.  But `a₀ ∈ L` makes `ℓ_{0,1}(a₀) = 0`, contradicting `0 ∈ {0,1}`.

Either way the ambient dimension exceeds three.
-/

open Finset

namespace GaloisForLFunctions

/-- The seven facets of the nonpure two-thick wedge `S¹ ∨ S²` on vertices `{0,…,5}`: the three
edges `{0,1},{1,2},{0,2}` of the circle and the four triangles `{0,3,4},{0,3,5},{0,4,5},{3,4,5}`
of the sphere, joined at vertex `0`. -/
def wedgeFacet : Fin 7 → Finset (Fin 6)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}
  | 3 => {0, 3, 4}
  | 4 => {0, 3, 5}
  | 5 => {0, 4, 5}
  | 6 => {3, 4, 5}

/-- **Dimension-three impossibility for the wedge.**  No faithful facet separation of the nonpure
two-thick wedge `S¹ ∨ S²` exists in a complex vector space of dimension at most three: given
vectors `a` and forms `ℓ` realizing the exact facet zero pattern `ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i`
in an `E` with `dim_ℂ E ≤ 3`, a contradiction follows.  Hence `ffsDim(Δ_wedge) ≥ 4`. -/
theorem wedge_no_faithfulSeparation_of_finrank_le_three
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E ≤ 3)
    (a : Fin 6 → E) (ℓ : Fin 7 → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (i : Fin 7) (v : Fin 6), ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i) :
    False := by
  -- zero / nonzero incidence facts used
  have z10 : ℓ 1 (a 0) = 0 := (hzero 1 0).mpr (by decide)
  have z13 : ℓ 1 (a 3) = 0 := (hzero 1 3).mpr (by decide)
  have z14 : ℓ 1 (a 4) = 0 := (hzero 1 4).mpr (by decide)
  have z15 : ℓ 1 (a 5) = 0 := (hzero 1 5).mpr (by decide)
  have n11 : ℓ 1 (a 1) ≠ 0 := fun h => (hzero 1 1).mp h (by decide)
  have z03 : ℓ 0 (a 3) = 0 := (hzero 0 3).mpr (by decide)
  have z04 : ℓ 0 (a 4) = 0 := (hzero 0 4).mpr (by decide)
  have z05 : ℓ 0 (a 5) = 0 := (hzero 0 5).mpr (by decide)
  have n00 : ℓ 0 (a 0) ≠ 0 := fun h => (hzero 0 0).mp h (by decide)
  have z35 : ℓ 3 (a 5) = 0 := (hzero 3 5).mpr (by decide)
  have n33 : ℓ 3 (a 3) ≠ 0 := fun h => (hzero 3 3).mp h (by decide)
  have n65 : ℓ 6 (a 5) ≠ 0 := fun h => (hzero 6 5).mp h (by decide)
  have a5ne : a 5 ≠ 0 := fun h => n65 (by rw [h, map_zero])
  -- L = span{a₃,a₄,a₅}
  set L : Submodule ℂ E := Submodule.span ℂ ({a 3, a 4, a 5} : Set E) with hL
  have a3L : a 3 ∈ L := Submodule.subset_span (by simp)
  have a5L : a 5 ∈ L := Submodule.subset_span (by simp)
  -- ℓ 0 and ℓ 1 annihilate L
  have hL0 : ∀ x ∈ L, ℓ 0 x = 0 := by
    intro x hx
    have hsub : L ≤ LinearMap.ker (ℓ 0) := by
      rw [hL, Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h <;> subst h <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker] <;> assumption
    exact LinearMap.mem_ker.mp (hsub hx)
  -- dichotomy on dim L
  rcases Nat.lt_or_ge (Module.finrank ℂ L) 2 with hle | hgt
  · -- dim L ≤ 1
    have hsl : (ℂ ∙ a 5) ≤ L := (Submodule.span_singleton_le_iff_mem (a 5) L).mpr a5L
    have hrank1 : Module.finrank ℂ (ℂ ∙ a 5) = 1 := finrank_span_singleton a5ne
    have heq : (ℂ ∙ a 5) = L :=
      Submodule.eq_of_le_of_finrank_le hsl (by rw [hrank1]; omega)
    have a3span : a 3 ∈ (ℂ ∙ a 5) := by rw [heq]; exact a3L
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a3span
    have : ℓ 3 (a 3) = 0 := by rw [← hc, map_smul, z35, smul_zero]
    exact n33 this
  · -- dim L ≥ 2
    have a0L : a 0 ∈ L := by
      by_contra ha0
      set M : Submodule ℂ E :=
        Submodule.span ℂ (insert (a 0) ({a 3, a 4, a 5} : Set E)) with hM
      have hLM : L < M := by
        rw [hL, hM]
        refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert _ _)) ?_
        intro he
        apply ha0
        rw [hL, he]
        exact Submodule.subset_span (Set.mem_insert _ _)
      have hlt : Module.finrank ℂ L < Module.finrank ℂ M :=
        Submodule.finrank_lt_finrank_of_lt hLM
      have h1 : Module.finrank ℂ M ≤ Module.finrank ℂ E := Submodule.finrank_le M
      have hMtop : M = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        omega
      have hM1 : ℓ 1 (a 1) = 0 := by
        have hsub : M ≤ LinearMap.ker (ℓ 1) := by
          rw [hM, Submodule.span_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with h | h | h | h <;> subst h <;>
            simp only [SetLike.mem_coe, LinearMap.mem_ker]
          · exact z10
          · exact z13
          · exact z14
          · exact z15
        exact LinearMap.mem_ker.mp (hsub (hMtop ▸ Submodule.mem_top))
      exact n11 hM1
    exact n00 (hL0 (a 0) a0L)

end GaloisForLFunctions

namespace GaloisForLFunctions

/-! ## Uniform lower bound for all two-boundary wedges -/

namespace UniformBoundaryWedge

/-- Vertices of the boundary wedge: one common centre and two disjoint finite blocks. -/
abbrev BoundaryWedgeVertex (r s : ℕ) := Option (Fin r ⊕ Fin s)

/-- Membership in the left simplex block, with the common centre belonging to both blocks. -/
def boundaryWedgeLeft {r s : ℕ} : BoundaryWedgeVertex r s → Prop
  | none => True
  | some (Sum.inl _) => True
  | some (Sum.inr _) => False

/-- Membership in the right simplex block, with the common centre belonging to both blocks. -/
def boundaryWedgeRight {r s : ℕ} : BoundaryWedgeVertex r s → Prop
  | none => True
  | some (Sum.inl _) => False
  | some (Sum.inr _) => True

/-- Embed a left-block simplex vertex in the full boundary wedge. -/
def boundaryWedgeLeftVertex {r s : ℕ} : Option (Fin r) → BoundaryWedgeVertex r s
  | none => none
  | some i => some (Sum.inl i)

/-- Embed a right-block simplex vertex in the full boundary wedge. -/
def boundaryWedgeRightVertex {r s : ℕ} : Option (Fin s) → BoundaryWedgeVertex r s
  | none => none
  | some j => some (Sum.inr j)

/-- Membership in the left boundary facet obtained by omitting `u`. -/
def boundaryWedgeLeftFacetMember {r s : ℕ}
    (u : Option (Fin r)) (v : BoundaryWedgeVertex r s) : Prop :=
  boundaryWedgeLeft v ∧ v ≠ boundaryWedgeLeftVertex u

/-- Membership in the right boundary facet obtained by omitting `u`. -/
def boundaryWedgeRightFacetMember {r s : ℕ}
    (u : Option (Fin s)) (v : BoundaryWedgeVertex r s) : Prop :=
  boundaryWedgeRight v ∧ v ≠ boundaryWedgeRightVertex u

/-- Uniform dimension-three impossibility for every wedge of two simplex boundaries of
dimension at least two. -/
theorem no_faithfulSeparation_of_finrank_le_three
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E ≤ 3)
    (a : BoundaryWedgeVertex r s → E)
    (ℓx : Option (Fin r) → (E →ₗ[ℂ] ℂ))
    (ℓy : Option (Fin s) → (E →ₗ[ℂ] ℂ))
    (hzeroX : ∀ u v, ℓx u (a v) = 0 ↔ ¬ boundaryWedgeLeftFacetMember u v)
    (hzeroY : ∀ u v, ℓy u (a v) = 0 ↔ ¬ boundaryWedgeRightFacetMember u v) :
    False := by
  let x₀ : Fin r := ⟨0, by omega⟩
  let x₁ : Fin r := ⟨1, by omega⟩
  let y₀ : Fin s := ⟨0, by omega⟩
  let y₁ : Fin s := ⟨1, by omega⟩
  let vx₀ : BoundaryWedgeVertex r s := some (Sum.inl x₀)
  let vy₀ : BoundaryWedgeVertex r s := some (Sum.inr y₀)
  let vy₁ : BoundaryWedgeVertex r s := some (Sum.inr y₁)
  have zX0 : ℓx none (a none) = 0 := (hzeroX none none).2 (by
    simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeftVertex, boundaryWedgeLeft])
  have zXy0 : ℓx none (a vy₀) = 0 := (hzeroX none vy₀).2 (by
    simp [vy₀, boundaryWedgeLeftFacetMember, boundaryWedgeLeft])
  have zXy1 : ℓx none (a vy₁) = 0 := (hzeroX none vy₁).2 (by
    simp [vy₁, boundaryWedgeLeftFacetMember, boundaryWedgeLeft])
  have nXx0 : ℓx none (a vx₀) ≠ 0 := fun h =>
    (hzeroX none vx₀).1 h (by
      simp [vx₀, boundaryWedgeLeftFacetMember, boundaryWedgeLeftVertex,
        boundaryWedgeLeft])
  have zX1y0 : ℓx (some x₁) (a vy₀) = 0 :=
    (hzeroX (some x₁) vy₀).2 (by
      simp [vy₀, boundaryWedgeLeftFacetMember, boundaryWedgeLeft])
  have zX1y1 : ℓx (some x₁) (a vy₁) = 0 :=
    (hzeroX (some x₁) vy₁).2 (by
      simp [vy₁, boundaryWedgeLeftFacetMember, boundaryWedgeLeft])
  have nX1c : ℓx (some x₁) (a none) ≠ 0 := fun h =>
    (hzeroX (some x₁) none).1 h (by
      simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeftVertex, boundaryWedgeLeft])
  have zY1y1 : ℓy (some y₁) (a vy₁) = 0 :=
    (hzeroY (some y₁) vy₁).2 (by
      simp [vy₁, boundaryWedgeRightFacetMember, boundaryWedgeRightVertex,
        boundaryWedgeRight])
  have nY1y0 : ℓy (some y₁) (a vy₀) ≠ 0 := fun h =>
    (hzeroY (some y₁) vy₀).1 h (by
      simp [vy₀, y₀, y₁, boundaryWedgeRightFacetMember,
        boundaryWedgeRightVertex, boundaryWedgeRight])
  have nY0y1 : ℓy (some y₀) (a vy₁) ≠ 0 := fun h =>
    (hzeroY (some y₀) vy₁).1 h (by
      simp [vy₁, y₀, y₁, boundaryWedgeRightFacetMember,
        boundaryWedgeRightVertex, boundaryWedgeRight])
  have ay1ne : a vy₁ ≠ 0 := fun h => nY0y1 (by rw [h, map_zero])
  set L : Submodule ℂ E := Submodule.span ℂ ({a vy₀, a vy₁} : Set E) with hL
  have ay0L : a vy₀ ∈ L := Submodule.subset_span (by simp)
  have ay1L : a vy₁ ∈ L := Submodule.subset_span (by simp)
  rcases Nat.lt_or_ge (Module.finrank ℂ L) 2 with hle | hgt
  · have hsl : (ℂ ∙ a vy₁) ≤ L :=
      (Submodule.span_singleton_le_iff_mem (a vy₁) L).mpr ay1L
    have hrank1 : Module.finrank ℂ (ℂ ∙ a vy₁) = 1 :=
      finrank_span_singleton ay1ne
    have heq : (ℂ ∙ a vy₁) = L :=
      Submodule.eq_of_le_of_finrank_le hsl (by rw [hrank1]; omega)
    have ay0span : a vy₀ ∈ (ℂ ∙ a vy₁) := by rw [heq]; exact ay0L
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ay0span
    exact nY1y0 (by rw [← hc, map_smul, zY1y1, smul_zero])
  · have acL : a none ∈ L := by
      by_contra hac
      set M : Submodule ℂ E :=
        Submodule.span ℂ (insert (a none) ({a vy₀, a vy₁} : Set E)) with hM
      have hLM : L < M := by
        rw [hL, hM]
        refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert _ _)) ?_
        intro he
        apply hac
        rw [hL, he]
        exact Submodule.subset_span (Set.mem_insert _ _)
      have hlt : Module.finrank ℂ L < Module.finrank ℂ M :=
        Submodule.finrank_lt_finrank_of_lt hLM
      have hMtop : M = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hME : Module.finrank ℂ M ≤ Module.finrank ℂ E := Submodule.finrank_le M
        omega
      have hsub : M ≤ LinearMap.ker (ℓx none) := by
        rw [hM, Submodule.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with h | h | h <;> subst h <;>
          simp only [SetLike.mem_coe, LinearMap.mem_ker]
        · exact zX0
        · exact zXy0
        · exact zXy1
      apply nXx0
      exact LinearMap.mem_ker.mp (hsub (hMtop ▸ Submodule.mem_top))
    have hsub : L ≤ LinearMap.ker (ℓx (some x₁)) := by
      rw [hL, Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h <;> subst h <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker]
      · exact zX1y0
      · exact zX1y1
    exact nX1c (LinearMap.mem_ker.mp (hsub acL))

end UniformBoundaryWedge

end GaloisForLFunctions

namespace GaloisForLFunctions.UniformBoundaryWedge

noncomputable section

/-- Exponents for the common centre and the left vertices. -/
def leftPowerCode {r : ℕ} : Option (Fin r) → ℕ
  | none => 0
  | some i => i.1 + 1

theorem leftPowerCode_injective {r : ℕ} : Function.Injective (@leftPowerCode r) := by
  intro u v huv
  cases u with
  | none =>
      cases v with
      | none => rfl
      | some j => simp [leftPowerCode] at huv
  | some i =>
      cases v with
      | none => simp [leftPowerCode] at huv
      | some j =>
          exact congrArg some (Fin.ext (Nat.add_right_cancel huv))

/-- Exponents for the common centre and the right vertices. -/
def rightPowerCode {s : ℕ} : Option (Fin s) → ℕ
  | none => 0
  | some j => j.1 + 1

theorem rightPowerCode_injective {s : ℕ} : Function.Injective (@rightPowerCode s) := by
  intro u v huv
  cases u with
  | none =>
      cases v with
      | none => rfl
      | some j => simp [rightPowerCode] at huv
  | some i =>
      cases v with
      | none => simp [rightPowerCode] at huv
      | some j =>
          exact congrArg some (Fin.ext (Nat.add_right_cancel huv))

/-- The explicit four-dimensional vectors for a boundary wedge. -/
def faithfulVector {r s : ℕ} (τ : ℂ) : BoundaryWedgeVertex r s → (Fin 4 → ℂ)
  | none => ![1, τ ^ leftPowerCode (@none (Fin r)), 1,
      τ ^ rightPowerCode (@none (Fin s))]
  | some (Sum.inl i) => ![1, τ ^ leftPowerCode (some i), 0, 0]
  | some (Sum.inr j) => ![0, 0, 1, τ ^ rightPowerCode (some j)]

/-- The left facet form, vanishing on the omitted left vertex and on the whole right block. -/
def faithfulLeftForm {r : ℕ} (τ : ℂ) (u : Option (Fin r)) :
    (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj 1 - (τ ^ leftPowerCode u) • LinearMap.proj 0

/-- The right facet form, vanishing on the omitted right vertex and on the whole left block. -/
def faithfulRightForm {s : ℕ} (τ : ℂ) (u : Option (Fin s)) :
    (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj 3 - (τ ^ rightPowerCode u) • LinearMap.proj 2

@[simp] theorem faithfulLeftForm_apply_leftVertex {r s : ℕ} (τ : ℂ)
    (u v : Option (Fin r)) :
    faithfulLeftForm τ u (faithfulVector (s := s) τ (boundaryWedgeLeftVertex v)) =
      τ ^ leftPowerCode v - τ ^ leftPowerCode u := by
  cases v <;> simp [faithfulLeftForm, faithfulVector, boundaryWedgeLeftVertex]

@[simp] theorem faithfulLeftForm_apply_rightNoncenter {r s : ℕ} (τ : ℂ)
    (u : Option (Fin r)) (j : Fin s) :
    faithfulLeftForm τ u (faithfulVector (r := r) (s := s) τ (some (Sum.inr j))) = 0 := by
  simp [faithfulLeftForm, faithfulVector]

@[simp] theorem faithfulRightForm_apply_rightVertex {r s : ℕ} (τ : ℂ)
    (u v : Option (Fin s)) :
    faithfulRightForm τ u (faithfulVector (r := r) τ (boundaryWedgeRightVertex v)) =
      τ ^ rightPowerCode v - τ ^ rightPowerCode u := by
  cases v <;> simp [faithfulRightForm, faithfulVector, boundaryWedgeRightVertex]

@[simp] theorem faithfulRightForm_apply_leftNoncenter {r s : ℕ} (τ : ℂ)
    (u : Option (Fin s)) (i : Fin r) :
    faithfulRightForm τ u (faithfulVector (r := r) (s := s) τ (some (Sum.inl i))) = 0 := by
  simp [faithfulRightForm, faithfulVector]

theorem faithfulVector_linearIndependent {r s : ℕ} {τ : ℂ}
    (hτ : Transcendental ℚ τ) :
    LinearIndependent ℚ (@faithfulVector r s τ) := by
  classical
  have hleftPow : LinearIndependent ℚ (fun u : Option (Fin r) => τ ^ leftPowerCode u) :=
    transcendental_pow_comp_linearIndependent hτ leftPowerCode_injective
  have hrightPow : LinearIndependent ℚ (fun u : Option (Fin s) => τ ^ rightPowerCode u) :=
    transcendental_pow_comp_linearIndependent hτ rightPowerCode_injective
  rw [Fintype.linearIndependent_iff]
  intro q hq v
  have hcoord1 := congrFun hq (1 : Fin 4)
  have hcoord3 := congrFun hq (3 : Fin 4)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord1 hcoord3
  have hleft : ∑ u : Option (Fin r),
      q (boundaryWedgeLeftVertex u) • τ ^ leftPowerCode u = 0 := by
    simpa [Fintype.sum_option, Fintype.sum_sum_type, faithfulVector,
      boundaryWedgeLeftVertex, leftPowerCode] using hcoord1
  have hright : ∑ u : Option (Fin s),
      q (boundaryWedgeRightVertex u) • τ ^ rightPowerCode u = 0 := by
    simpa [Fintype.sum_option, Fintype.sum_sum_type, faithfulVector,
      boundaryWedgeRightVertex, rightPowerCode] using hcoord3
  have hqleft : ∀ u, q (boundaryWedgeLeftVertex u) = 0 :=
    Fintype.linearIndependent_iff.mp hleftPow _ hleft
  have hqright : ∀ u, q (boundaryWedgeRightVertex u) = 0 :=
    Fintype.linearIndependent_iff.mp hrightPow _ hright
  rcases v with _ | (i | j)
  · exact hqleft none
  · exact hqleft (some i)
  · exact hqright (some j)

theorem faithfulLeftForm_zero_iff {r s : ℕ} {τ : ℂ}
    (hτ : Transcendental ℚ τ) (u : Option (Fin r)) (v : BoundaryWedgeVertex r s) :
    faithfulLeftForm τ u (faithfulVector τ v) = 0 ↔
      ¬ boundaryWedgeLeftFacetMember u v := by
  have hp : Function.Injective (fun w : Option (Fin r) => τ ^ leftPowerCode w) :=
    (transcendental_pow_comp_linearIndependent hτ leftPowerCode_injective).injective
  rcases v with _ | (i | j)
  · rw [show (none : BoundaryWedgeVertex r s) = boundaryWedgeLeftVertex none by rfl,
      faithfulLeftForm_apply_leftVertex, sub_eq_zero]
    cases u <;> simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeft,
      boundaryWedgeLeftVertex, hp.eq_iff]
  · rw [show (some (Sum.inl i) : BoundaryWedgeVertex r s) =
        boundaryWedgeLeftVertex (some i) by rfl,
      faithfulLeftForm_apply_leftVertex, sub_eq_zero]
    cases u <;> simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeft,
      boundaryWedgeLeftVertex, hp.eq_iff]
  · simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeft]

theorem faithfulRightForm_zero_iff {r s : ℕ} {τ : ℂ}
    (hτ : Transcendental ℚ τ) (u : Option (Fin s)) (v : BoundaryWedgeVertex r s) :
    faithfulRightForm τ u (faithfulVector τ v) = 0 ↔
      ¬ boundaryWedgeRightFacetMember u v := by
  have hp : Function.Injective (fun w : Option (Fin s) => τ ^ rightPowerCode w) :=
    (transcendental_pow_comp_linearIndependent hτ rightPowerCode_injective).injective
  rcases v with _ | (i | j)
  · rw [show (none : BoundaryWedgeVertex r s) = boundaryWedgeRightVertex none by rfl,
      faithfulRightForm_apply_rightVertex, sub_eq_zero]
    cases u <;> simp [boundaryWedgeRightFacetMember, boundaryWedgeRight,
      boundaryWedgeRightVertex, hp.eq_iff]
  · simp [boundaryWedgeRightFacetMember, boundaryWedgeRight]
  · rw [show (some (Sum.inr j) : BoundaryWedgeVertex r s) =
        boundaryWedgeRightVertex (some j) by rfl,
      faithfulRightForm_apply_rightVertex, sub_eq_zero]
    cases u <;> simp [boundaryWedgeRightFacetMember, boundaryWedgeRight,
      boundaryWedgeRightVertex, hp.eq_iff]

theorem faithfulLeftValues_linearIndependent {r s : ℕ} {τ : ℂ}
    (hτ : Transcendental ℚ τ) (u : Option (Fin r)) :
    LinearIndependent ℚ (fun v : {v : Option (Fin r) // v ≠ u} =>
      faithfulLeftForm τ u
        (faithfulVector (s := s) τ (boundaryWedgeLeftVertex v.1))) := by
  have hp : LinearIndependent ℚ (fun v : Option (Fin r) => τ ^ leftPowerCode v) :=
    transcendental_pow_comp_linearIndependent hτ leftPowerCode_injective
  have haff := hp.affineIndependent ℚ
  have hdiff :=
    (affineIndependent_iff_linearIndependent_vsub ℚ
      (fun v : Option (Fin r) => τ ^ leftPowerCode v) u).mp haff
  simpa using hdiff

theorem faithfulRightValues_linearIndependent {r s : ℕ} {τ : ℂ}
    (hτ : Transcendental ℚ τ) (u : Option (Fin s)) :
    LinearIndependent ℚ (fun v : {v : Option (Fin s) // v ≠ u} =>
      faithfulRightForm τ u
        (faithfulVector (r := r) τ (boundaryWedgeRightVertex v.1))) := by
  have hp : LinearIndependent ℚ (fun v : Option (Fin s) => τ ^ rightPowerCode v) :=
    transcendental_pow_comp_linearIndependent hτ rightPowerCode_injective
  have haff := hp.affineIndependent ℚ
  have hdiff :=
    (affineIndependent_iff_linearIndependent_vsub ℚ
      (fun v : Option (Fin s) => τ ^ rightPowerCode v) u).mp haff
  simpa using hdiff

/-- Complete faithful facet-separation data for the two-boundary wedge in a coordinate space. -/
structure FaithfulSeparation (r s d : ℕ) where
  vector : BoundaryWedgeVertex r s → (Fin d → ℂ)
  leftForm : Option (Fin r) → ((Fin d → ℂ) →ₗ[ℂ] ℂ)
  rightForm : Option (Fin s) → ((Fin d → ℂ) →ₗ[ℂ] ℂ)
  vector_linearIndependent : LinearIndependent ℚ vector
  left_zero_iff :
    ∀ u v, leftForm u (vector v) = 0 ↔ ¬ boundaryWedgeLeftFacetMember u v
  right_zero_iff :
    ∀ u v, rightForm u (vector v) = 0 ↔ ¬ boundaryWedgeRightFacetMember u v
  left_values_linearIndependent :
    ∀ u, LinearIndependent ℚ (fun v : {v : Option (Fin r) // v ≠ u} =>
      leftForm u (vector (boundaryWedgeLeftVertex v.1)))
  right_values_linearIndependent :
    ∀ u, LinearIndependent ℚ (fun v : {v : Option (Fin s) // v ≠ u} =>
      rightForm u (vector (boundaryWedgeRightVertex v.1)))

/-- One transcendental number gives faithful separation of every boundary wedge in four complex
coordinates. -/
def faithfulSeparationFinFour {r s : ℕ} {τ : ℂ} (hτ : Transcendental ℚ τ) :
    FaithfulSeparation r s 4 where
  vector := faithfulVector τ
  leftForm := faithfulLeftForm τ
  rightForm := faithfulRightForm τ
  vector_linearIndependent := faithfulVector_linearIndependent hτ
  left_zero_iff := faithfulLeftForm_zero_iff hτ
  right_zero_iff := faithfulRightForm_zero_iff hτ
  left_values_linearIndependent := faithfulLeftValues_linearIndependent hτ
  right_values_linearIndependent := faithfulRightValues_linearIndependent hτ

/-- Exact faithful facet-separation dimension of every wedge of two simplex boundaries of
dimension at least two: dimension four exists, and every faithful separation has dimension at
least four. -/
theorem faithfulSeparation_fin_four_and_minimal
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) {τ : ℂ} (hτ : Transcendental ℚ τ) :
    Nonempty (FaithfulSeparation r s 4) ∧
      ∀ d, Nonempty (FaithfulSeparation r s d) → 4 ≤ d := by
  refine ⟨⟨faithfulSeparationFinFour hτ⟩, ?_⟩
  intro d hdata
  by_contra hd
  have hdim : d ≤ 3 := by omega
  rcases hdata with ⟨data⟩
  exact no_faithfulSeparation_of_finrank_le_three hr hs
    (E := Fin d → ℂ) (by simpa using hdim)
    data.vector data.leftForm data.rightForm
    data.left_zero_iff data.right_zero_iff

end

end GaloisForLFunctions.UniformBoundaryWedge
