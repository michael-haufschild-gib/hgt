import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# The dimension-two periodic-pencil realization of a simplex-boundary wedge

For a transcendental `τ`, the translation vectors of the wedge `∂σ^r ∧ ∂σ^s` in `ℂ²`

`a₀ = (τ^s, τ^r)`,   `a_{xᵢ} = (0, τ^i)` (`i < r`),   `a_{yⱼ} = (τ^j, 0)` (`j < s`)

are `ℚ`-linearly independent (`wedge_realization_linearIndependent`).  The first coordinate is a
`ℚ`-combination of distinct powers `τ^(0 : ℕ),…,τ^{s-1}, τ^s`, so transcendence kills the `a₀` and
`y`-coefficients; the second coordinate then kills the `x`-coefficients.  This realizes the
periodic-pencil dimension of the wedge in dimension two.
-/

open Finset

namespace GaloisForLFunctions

/-- A `ℚ`-combination of distinct powers of a transcendental number vanishes only trivially. -/
theorem transcendental_pow_combination_eq_zero {ι : Type*} [Fintype ι] {τ : ℂ}
    (hτ : Transcendental ℚ τ) {p : ι → ℕ} (hp : Function.Injective p) (g : ι → ℚ)
    (h : ∑ i, g i • (τ ^ p i) = 0) : ∀ i, g i = 0 :=
  Fintype.linearIndependent_iff.mp (transcendental_pow_comp_linearIndependent hτ hp) g h

/-- The translation vectors `a₀, a_{xᵢ}, a_{yⱼ}` of the wedge `∂σ^r ∧ ∂σ^s`. -/
noncomputable def wedgeVec (τ : ℂ) (r s : ℕ) : Option (Fin r ⊕ Fin s) → ℂ × ℂ
  | none => (τ ^ s, τ ^ r)
  | some (Sum.inl i) => (0, τ ^ (i : ℕ))
  | some (Sum.inr j) => (τ ^ (j : ℕ), 0)

/-- **Wedge realization independence.**  For transcendental `τ`, the wedge translation vectors are
`ℚ`-linearly independent in `ℂ²`. -/
theorem wedge_realization_linearIndependent {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) :
    LinearIndependent ℚ (wedgeVec τ r s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- first coordinate: g none • τ^s + ∑_j g (inr j) • τ^j = 0
  have hfst : g none • (τ ^ s) + ∑ j : Fin s, g (some (Sum.inr j)) • (τ ^ (j : ℕ)) = 0 := by
    have h := congrArg Prod.fst hg
    simp only [Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Prod.fst_add, Fintype.sum_option,
      Fintype.sum_sum_type, wedgeVec, smul_zero, Finset.sum_const_zero, zero_add] at h
    exact h
  -- reindex first coord as powers over Option (Fin s):  none ↦ s,  inr j ↦ j
  set p₁ : Option (Fin s) → ℕ := fun o => o.elim s (fun j => (j : ℕ)) with hp₁
  have hp₁inj : Function.Injective p₁ := by
    rintro (_ | a) (_ | b) hab <;> simp_all <;> omega
  set g₁ : Option (Fin s) → ℚ := fun o => o.elim (g none) (fun j => g (some (Sum.inr j))) with hg₁
  have hcomb₁ : ∑ o : Option (Fin s), g₁ o • (τ ^ p₁ o) = 0 := by
    rw [Fintype.sum_option]; simpa [hg₁, hp₁] using hfst
  have hz₁ := transcendental_pow_combination_eq_zero hτ hp₁inj g₁ hcomb₁
  have hnone : g none = 0 := by have := hz₁ none; simpa [hg₁] using this
  have hyj : ∀ j, g (some (Sum.inr j)) = 0 := fun j => by
    have := hz₁ (some j); simpa [hg₁] using this
  -- second coordinate with g none = 0: ∑_i g (inl i) • τ^i = 0
  have hsnd : ∑ i : Fin r, g (some (Sum.inl i)) • (τ ^ (i : ℕ)) = 0 := by
    have h := congrArg Prod.snd hg
    simp only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Prod.snd_add, Fintype.sum_option,
      Fintype.sum_sum_type, wedgeVec, smul_zero, Finset.sum_const_zero, add_zero] at h
    rw [hnone, zero_smul, zero_add] at h
    exact h
  set p₂ : Fin r → ℕ := fun i => (i : ℕ) with hp₂
  have hp₂inj : Function.Injective p₂ := fun a b h => Fin.ext h
  have hz₂ := transcendental_pow_combination_eq_zero hτ hp₂inj
    (fun i => g (some (Sum.inl i))) hsnd
  intro o
  rcases o with _ | (a | b)
  · exact hnone
  · exact hz₂ a
  · exact hyj b

/-! ## The deleted-centre constraint boundary

The common vertex of `∂σʳ ∨ ∂σˢ` is represented by `none`.  Deleting it leaves the disjoint
union of the two full simplices on `Fin r` and `Fin s`.  The definitions below isolate that
combinatorial core without assuming any homology or Hochster theorem. -/

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

/-- The faces of `∂σʳ ∨ ∂σˢ`: a face lies in one block and properly omits a vertex of that
block. -/
def boundaryWedgeFace {r s : ℕ} (J : Finset (BoundaryWedgeVertex r s)) : Prop :=
  ((∀ v ∈ J, boundaryWedgeLeft v) ∧
      ∃ v : BoundaryWedgeVertex r s, boundaryWedgeLeft v ∧ v ∉ J) ∨
    ((∀ v ∈ J, boundaryWedgeRight v) ∧
      ∃ v : BoundaryWedgeVertex r s, boundaryWedgeRight v ∧ v ∉ J)

/-- The empty set is a face of every boundary wedge. -/
theorem boundaryWedgeFace_empty (r s : ℕ) :
    boundaryWedgeFace (∅ : Finset (BoundaryWedgeVertex r s)) := by
  left
  refine ⟨by simp, none, ?_, by simp⟩
  simp [boundaryWedgeLeft]

/-- Boundary-wedge faces are closed under taking subsets. -/
theorem boundaryWedgeFace_mono {r s : ℕ}
    {I J : Finset (BoundaryWedgeVertex r s)} (hIJ : I ⊆ J)
    (hJ : boundaryWedgeFace J) : boundaryWedgeFace I := by
  rcases hJ with ⟨hleft, v, hvleft, hvJ⟩ | ⟨hright, v, hvright, hvJ⟩
  · left
    exact ⟨fun u hu => hleft u (hIJ hu), v, hvleft, fun hvI => hvJ (hIJ hvI)⟩
  · right
    exact ⟨fun u hu => hright u (hIJ hu), v, hvright, fun hvI => hvJ (hIJ hvI)⟩

/-- Insert a noncentral vertex into the full boundary-wedge vertex type. -/
def boundaryWedgeDeleteCenterEmbedding (r s : ℕ) :
    (Fin r ⊕ Fin s) ↪ BoundaryWedgeVertex r s :=
  ⟨some, by
    intro u v h
    simpa using h⟩

/-- A face in the subcomplex induced after deleting the common centre. -/
def boundaryWedgeDeletedFace {r s : ℕ} (J : Finset (Fin r ⊕ Fin s)) : Prop :=
  boundaryWedgeFace (J.map (boundaryWedgeDeleteCenterEmbedding r s))

/-- Left-block predicate on the deleted-centre vertex set. -/
def boundaryWedgeDeletedLeft {r s : ℕ} : Fin r ⊕ Fin s → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Right-block predicate on the deleted-centre vertex set. -/
def boundaryWedgeDeletedRight {r s : ℕ} : Fin r ⊕ Fin s → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- **Deleted-centre classification.**  A finite set is a face after deleting the common vertex
exactly when all of its vertices lie in one of the two blocks.  Thus the induced subcomplex is
the disjoint union of two full simplices. -/
theorem boundaryWedgeDeletedFace_iff {r s : ℕ} (J : Finset (Fin r ⊕ Fin s)) :
    boundaryWedgeDeletedFace J ↔
      (∀ v ∈ J, boundaryWedgeDeletedLeft v) ∨
      (∀ v ∈ J, boundaryWedgeDeletedRight v) := by
  constructor
  · rintro (⟨hleft, -⟩ | ⟨hright, -⟩)
    · left
      intro v hv
      have hsome := hleft (some v) (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
      rcases v with i | j <;>
        simp_all [boundaryWedgeLeft, boundaryWedgeDeletedLeft]
    · right
      intro v hv
      have hsome := hright (some v) (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
      rcases v with i | j <;>
        simp_all [boundaryWedgeRight, boundaryWedgeDeletedRight]
  · rintro (hleft | hright)
    · left
      refine ⟨?_, none, by simp [boundaryWedgeLeft], by
        simp [boundaryWedgeDeleteCenterEmbedding]⟩
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
      rcases w with i | j <;>
        simpa [boundaryWedgeLeft, boundaryWedgeDeletedLeft] using! hleft _ hw
    · right
      refine ⟨?_, none, by simp [boundaryWedgeRight], by
        simp [boundaryWedgeDeleteCenterEmbedding]⟩
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
      rcases w with i | j <;>
        simpa [boundaryWedgeRight, boundaryWedgeDeletedRight] using! hright _ hw

/-- Every finite subset of the left block is a deleted-centre face. -/
theorem boundaryWedgeDeletedFace_left {r s : ℕ} (J : Finset (Fin r)) :
    boundaryWedgeDeletedFace
      (J.map ⟨Sum.inl, by intro i j h; simpa using h⟩ : Finset (Fin r ⊕ Fin s)) := by
  rw [boundaryWedgeDeletedFace_iff]
  left
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨i, hi, rfl⟩
  simp [boundaryWedgeDeletedLeft]

/-- Every finite subset of the right block is a deleted-centre face. -/
theorem boundaryWedgeDeletedFace_right {r s : ℕ} (J : Finset (Fin s)) :
    boundaryWedgeDeletedFace
      (J.map ⟨Sum.inr, by intro i j h; simpa using h⟩ : Finset (Fin r ⊕ Fin s)) := by
  rw [boundaryWedgeDeletedFace_iff]
  right
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨j, hj, rfl⟩
  simp [boundaryWedgeDeletedRight]

/-- No edge crosses between the two components of the deleted-centre boundary. -/
theorem boundaryWedgeDeleted_mixed_pair_not_face {r s : ℕ} (i : Fin r) (j : Fin s) :
    ¬ boundaryWedgeDeletedFace ({Sum.inl i, Sum.inr j} : Finset (Fin r ⊕ Fin s)) := by
  rw [boundaryWedgeDeletedFace_iff]
  intro h
  rcases h with hleft | hright
  · have h := hleft (Sum.inr j) (by simp)
    simp [boundaryWedgeDeletedLeft] at h
  · have h := hright (Sum.inl i) (by simp)
    simp [boundaryWedgeDeletedRight] at h

/-- The component label of a noncentral boundary-wedge vertex. -/
def boundaryWedgeComponent {r s : ℕ} : Fin r ⊕ Fin s → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

@[simp]
theorem boundaryWedgeDeletedLeft_iff_component_false {r s : ℕ} (v : Fin r ⊕ Fin s) :
    boundaryWedgeDeletedLeft v ↔ boundaryWedgeComponent v = false := by
  rcases v with i | j <;> simp [boundaryWedgeDeletedLeft, boundaryWedgeComponent]

@[simp]
theorem boundaryWedgeDeletedRight_iff_component_true {r s : ℕ} (v : Fin r ⊕ Fin s) :
    boundaryWedgeDeletedRight v ↔ boundaryWedgeComponent v = true := by
  rcases v with i | j <;> simp [boundaryWedgeDeletedRight, boundaryWedgeComponent]

/-- The block label is locally constant on every deleted-centre face. -/
theorem boundaryWedgeComponent_eq_of_face {r s : ℕ} {J : Finset (Fin r ⊕ Fin s)}
    (hJ : boundaryWedgeDeletedFace J) {u v : Fin r ⊕ Fin s} (hu : u ∈ J) (hv : v ∈ J) :
    boundaryWedgeComponent u = boundaryWedgeComponent v := by
  rw [boundaryWedgeDeletedFace_iff] at hJ
  rcases hJ with hleft | hright
  · have hu' := (boundaryWedgeDeletedLeft_iff_component_false u).mp (hleft u hu)
    have hv' := (boundaryWedgeDeletedLeft_iff_component_false v).mp (hleft v hv)
    exact hu'.trans hv'.symm
  · have hu' := (boundaryWedgeDeletedRight_iff_component_true u).mp (hright u hu)
    have hv' := (boundaryWedgeDeletedRight_iff_component_true v).mp (hright v hv)
    exact hu'.trans hv'.symm

/-- If both blocks are nonempty, their locally constant component label is not globally
constant.  This is the characteristic-free combinatorial witness underlying the nonzero reduced
degree-zero class of the deleted-centre subcomplex. -/
theorem boundaryWedgeComponent_not_constant {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ¬ ∀ u v : Fin r ⊕ Fin s,
      boundaryWedgeComponent u = boundaryWedgeComponent v := by
  intro h
  have huv := h (Sum.inl ⟨0, hr⟩) (Sum.inr ⟨0, hs⟩)
  simp [boundaryWedgeComponent] at huv

/-! ## Polarization transport across the sewing vertex -/

/-- A Boolean orientation is compatible when it is transported unchanged across every edge of
the boundary wedge. -/
def boundaryWedgeOrientationCompatible {r s : ℕ}
    (ε : BoundaryWedgeVertex r s → Bool) : Prop :=
  ∀ u v, boundaryWedgeFace ({u, v} : Finset (BoundaryWedgeVertex r s)) → ε u = ε v

/-- When the left boundary has dimension at least one, every left vertex is joined to the common
centre by an edge. -/
theorem boundaryWedgeFace_center_left {r s : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    boundaryWedgeFace
      ({none, some (Sum.inl i)} : Finset (BoundaryWedgeVertex r s)) := by
  have hcard : 1 < Fintype.card (Fin r) := by simpa using! hr
  obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  left
  refine ⟨?_, some (Sum.inl k), by simp [boundaryWedgeLeft], ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [boundaryWedgeLeft]
  · simp [hki]

/-- When the right boundary has dimension at least one, every right vertex is joined to the
common centre by an edge. -/
theorem boundaryWedgeFace_center_right {r s : ℕ} (hs : 2 ≤ s) (j : Fin s) :
    boundaryWedgeFace
      ({none, some (Sum.inr j)} : Finset (BoundaryWedgeVertex r s)) := by
  have hcard : 1 < Fintype.card (Fin s) := by simpa using! hs
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
  right
  refine ⟨?_, some (Sum.inr k), by simp [boundaryWedgeRight], ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [boundaryWedgeRight]
  · simp [hkj]

/-- A compatible orientation on the sewn wedge is determined by its value at the common centre. -/
theorem boundaryWedgeOrientation_eq_center {r s : ℕ}
    {ε : BoundaryWedgeVertex r s → Bool} (hε : boundaryWedgeOrientationCompatible ε)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (v : BoundaryWedgeVertex r s) :
    ε v = ε none := by
  rcases v with _ | (i | j)
  · rfl
  · exact (hε none (some (Sum.inl i)) (boundaryWedgeFace_center_left hr i)).symm
  · exact (hε none (some (Sum.inr j)) (boundaryWedgeFace_center_right hs j)).symm

/-- Constant orientations are compatible with every boundary-wedge sewing. -/
theorem boundaryWedgeOrientationCompatible_const {r s : ℕ} (b : Bool) :
    boundaryWedgeOrientationCompatible (fun _ : BoundaryWedgeVertex r s => b) := by
  intro u v huv
  rfl

/-- The space of compatible Boolean orientations on the sewn boundary wedge. -/
abbrev BoundaryWedgeCompatibleOrientation (r s : ℕ) :=
  {ε : BoundaryWedgeVertex r s → Bool // boundaryWedgeOrientationCompatible ε}

/-- **Connected polarization collapse.**  Sewing the two blocks through their common vertex
reduces the compatible orientation fibre to one global Boolean choice. -/
def boundaryWedgeCompatibleOrientationEquivBool {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    BoundaryWedgeCompatibleOrientation r s ≃ Bool where
  toFun ε := ε.1 none
  invFun b := ⟨fun _ => b, boundaryWedgeOrientationCompatible_const b⟩
  left_inv ε := by
    apply Subtype.ext
    funext v
    exact (boundaryWedgeOrientation_eq_center ε.2 hr hs v).symm
  right_inv b := rfl

/-- A deleted-centre orientation is compatible when it is constant across every remaining edge. -/
def boundaryWedgeDeletedOrientationCompatible {r s : ℕ}
    (ε : Fin r ⊕ Fin s → Bool) : Prop :=
  ∀ u v, boundaryWedgeDeletedFace ({u, v} : Finset (Fin r ⊕ Fin s)) → ε u = ε v

/-- Every pair of left-block vertices is an edge after deleting the centre. -/
theorem boundaryWedgeDeletedFace_left_pair {r s : ℕ} (i k : Fin r) :
    boundaryWedgeDeletedFace ({Sum.inl i, Sum.inl k} : Finset (Fin r ⊕ Fin s)) := by
  rw [boundaryWedgeDeletedFace_iff]
  left
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp [boundaryWedgeDeletedLeft]

/-- Every pair of right-block vertices is an edge after deleting the centre. -/
theorem boundaryWedgeDeletedFace_right_pair {r s : ℕ} (j k : Fin s) :
    boundaryWedgeDeletedFace ({Sum.inr j, Sum.inr k} : Finset (Fin r ⊕ Fin s)) := by
  rw [boundaryWedgeDeletedFace_iff]
  right
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp [boundaryWedgeDeletedRight]

/-- The space of compatible Boolean orientations after deleting the sewing vertex. -/
abbrev BoundaryWedgeDeletedCompatibleOrientation (r s : ℕ) :=
  {ε : Fin r ⊕ Fin s → Bool // boundaryWedgeDeletedOrientationCompatible ε}

/-- **Disconnected polarization fibre.**  Before sewing through the common centre, the two full
simplex components carry two independent Boolean orientations. -/
def boundaryWedgeDeletedCompatibleOrientationEquivBoolProd {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    BoundaryWedgeDeletedCompatibleOrientation r s ≃ Bool × Bool where
  toFun ε := (ε.1 (Sum.inl ⟨0, hr⟩), ε.1 (Sum.inr ⟨0, hs⟩))
  invFun b :=
    ⟨fun v => match v with
      | Sum.inl _ => b.1
      | Sum.inr _ => b.2,
    by
      intro u v huv
      have hc := boundaryWedgeComponent_eq_of_face (u := u) (v := v) huv (by simp) (by simp)
      rcases u with i | j <;> rcases v with k | l <;>
        simp_all [boundaryWedgeComponent]⟩
  left_inv ε := by
    apply Subtype.ext
    funext v
    rcases v with i | j
    · exact ε.2 (Sum.inl ⟨0, hr⟩) (Sum.inl i)
        (boundaryWedgeDeletedFace_left_pair _ _)
    · exact ε.2 (Sum.inr ⟨0, hs⟩) (Sum.inr j)
        (boundaryWedgeDeletedFace_right_pair _ _)
  right_inv b := by
    rcases b with ⟨b₀, b₁⟩
    rfl

/-- The homological degree selected by the disconnected deleted-centre Hochster strand. -/
def boundaryWedgeSourceCoherenceDepth (r s : ℕ) : ℕ := r + s - 1

/-- Every finite coherence depth at least three occurs in the boundary-wedge family while the
analytic realization dimension remains two. -/
theorem boundaryWedgeSourceCoherenceDepth_surjective {m : ℕ} (hm : 3 ≤ m) :
    ∃ r s : ℕ, 2 ≤ r ∧ 2 ≤ s ∧ boundaryWedgeSourceCoherenceDepth r s = m := by
  refine ⟨2, m - 1, by omega, by omega, ?_⟩
  simp only [boundaryWedgeSourceCoherenceDepth]
  omega

end GaloisForLFunctions
