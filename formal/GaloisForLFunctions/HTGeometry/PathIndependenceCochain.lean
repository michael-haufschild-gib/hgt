import GaloisForLFunctions.HTGeometry.SimplexConeContraction

/-!
# The three-vertex cochain reduction of a path independence complex

Faces of the independence complex of the path on `{0, …, n-1}` are the vertex sets with no two
adjacent members. On reduced simplicial cochains the two lowest vertices support an explicit
contraction onto the tail: with

  `(K f)(σ) = 0` if `0 ∈ σ` or `1 ∈ σ`, and `f ({0} ∪ σ)` otherwise,
  `(q f)(τ) = f ({1} ∪ τ) - f ({0} ∪ τ)`,
  `(J g)(σ) = g (σ \ {1})` if `1 ∈ σ`, and `0` otherwise,

the four identities `δK + Kδ = id - Jq`, `qJ = id`, `qδ = -δq` and `δJ = -Jδ` hold. `K` and `q`
lower the occupation degree by one and `J` raises it by one, so `q` and `J` induce inverse
cohomology isomorphisms with a shift of one in occupation degree.

The third case of the first identity is exactly the corpus's cone contraction of the full simplex
at the base vertex `0` (`simplicialCoboundary_simplicialCone_add`); the first two cases are the
corrections forced by the path condition, which forbids adjoining `0` to a face containing `1`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Finset

variable {F : Type*} [CommRing F]

/-! ### Path faces -/

/-- `σ` is a face of the independence complex of the path on `{0, …, n-1}`: its members are below
`n` and no two are adjacent. -/
def IsPathFace (n : ℕ) (σ : Finset ℕ) : Prop :=
  (∀ v ∈ σ, v < n) ∧ ∀ v ∈ σ, v + 1 ∉ σ

instance instDecidableIsPathFace (n : ℕ) (σ : Finset ℕ) : Decidable (IsPathFace n σ) :=
  decidable_of_iff ((∀ v ∈ σ, v < n) ∧ ∀ v ∈ σ, v + 1 ∉ σ) Iff.rfl

theorem IsPathFace.subset {n : ℕ} {σ τ : Finset ℕ} (h : IsPathFace n σ) (hτ : τ ⊆ σ) :
    IsPathFace n τ :=
  ⟨fun v hv => h.1 v (hτ hv), fun v hv hv1 => h.2 v (hτ hv) (hτ hv1)⟩

theorem IsPathFace.erase {n : ℕ} {σ : Finset ℕ} (h : IsPathFace n σ) (v : ℕ) :
    IsPathFace n (σ.erase v) :=
  h.subset (Finset.erase_subset v σ)

/-- Vertex sets in the tail: subsets of `{3, 4, …}`. -/
def IsTailSet (τ : Finset ℕ) : Prop := ∀ v ∈ τ, 3 ≤ v

theorem IsTailSet.notMem_zero {τ : Finset ℕ} (h : IsTailSet τ) : 0 ∉ τ := fun hv => by
  have := h 0 hv; omega

theorem IsTailSet.notMem_one {τ : Finset ℕ} (h : IsTailSet τ) : 1 ∉ τ := fun hv => by
  have := h 1 hv; omega

theorem IsTailSet.erase {τ : Finset ℕ} (h : IsTailSet τ) (v : ℕ) : IsTailSet (τ.erase v) :=
  fun u hu => h u (Finset.mem_of_mem_erase hu)

/-! ### Incidence signs at the two lowest vertices -/

theorem pathFaceSign_zero (σ : Finset ℕ) : faceSign F σ 0 = 1 := by
  have h : σ.filter (· < 0) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro v _
    omega
  rw [faceSign, h, Finset.card_empty, pow_zero]

theorem pathFaceSign_one {σ : Finset ℕ} (h0 : 0 ∉ σ) : faceSign F σ 1 = 1 := by
  have h : σ.filter (· < 1) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro v hv hlt
    exact h0 (by rwa [show v = 0 from by omega] at hv)
  rw [faceSign, h, Finset.card_empty, pow_zero]

theorem pathFaceSign_insert_of_lt {a v : ℕ} {τ : Finset ℕ} (ha : a ∉ τ) (hav : a < v) :
    faceSign F (insert a τ) v = - faceSign F τ v := by
  have h1 : (insert a τ).filter (· < v) = insert a (τ.filter (· < v)) := by
    rw [Finset.filter_insert, if_pos hav]
  have h2 : a ∉ τ.filter (· < v) := fun hv => ha (Finset.mem_of_mem_filter a hv)
  rw [faceSign, faceSign, h1, Finset.card_insert_of_notMem h2, pow_succ]
  ring

theorem pathFaceSign_insert_self {a : ℕ} {τ : Finset ℕ} (h : ∀ u ∈ τ, a < u) :
    faceSign F (insert a τ) a = 1 := by
  have h1 : (insert a τ).filter (· < a) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · omega
    · have := h v hv; omega
  rw [faceSign, h1, Finset.card_empty, pow_zero]

/-! ### The three explicit maps -/

/-- The path cone at the base vertex `0`, cut off on the faces meeting the vertex `1`. -/
def pathCone (F : Type*) [CommRing F] (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if 0 ∈ σ ∨ 1 ∈ σ then 0 else f (insert 0 σ)

/-- The tail contraction, lowering the occupation degree by one. -/
def pathTailMap (F : Type*) [CommRing F] (f : Finset ℕ → F) (τ : Finset ℕ) : F :=
  f (insert 1 τ) - f (insert 0 τ)

/-- The tail inclusion, raising the occupation degree by one. -/
def pathIncl (F : Type*) [CommRing F] (g : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if 1 ∈ σ then g (σ.erase 1) else 0

theorem pathCone_of_mem_zero {f : Finset ℕ → F} {σ : Finset ℕ} (h : 0 ∈ σ) :
    pathCone F f σ = 0 := by
  rw [pathCone, if_pos (Or.inl h)]

theorem pathCone_of_mem_one {f : Finset ℕ → F} {σ : Finset ℕ} (h : 1 ∈ σ) :
    pathCone F f σ = 0 := by
  rw [pathCone, if_pos (Or.inr h)]

theorem pathCone_of_notMem {f : Finset ℕ → F} {σ : Finset ℕ} (h0 : 0 ∉ σ) (h1 : 1 ∉ σ) :
    pathCone F f σ = f (insert 0 σ) := by
  rw [pathCone, if_neg (by tauto)]

theorem pathIncl_of_mem {g : Finset ℕ → F} {σ : Finset ℕ} (h : 1 ∈ σ) :
    pathIncl F g σ = g (σ.erase 1) := by
  rw [pathIncl, if_pos h]

theorem pathIncl_of_notMem {g : Finset ℕ → F} {σ : Finset ℕ} (h : 1 ∉ σ) :
    pathIncl F g σ = 0 := by
  rw [pathIncl, if_neg h]

/-! ### `q ∘ J = id` -/

/-- **`qJ = id`.** The tail contraction is a left inverse of the tail inclusion. -/
theorem pathTailMap_pathIncl (g : Finset ℕ → F) {τ : Finset ℕ} (_h0 : 0 ∉ τ) (h1 : 1 ∉ τ) :
    pathTailMap F (pathIncl F g) τ = g τ := by
  rw [pathTailMap, pathIncl_of_mem (Finset.mem_insert_self 1 τ),
    pathIncl_of_notMem (by simp [h1]), sub_zero, Finset.erase_insert h1]

/-! ### The coboundary at a minimal adjoined vertex -/

theorem pathCoboundary_insert_of_min (f : Finset ℕ → F) {a : ℕ} {τ : Finset ℕ}
    (ha : ∀ u ∈ τ, a < u) :
    simplicialCoboundary F f (insert a τ)
      = f τ - ∑ v ∈ τ, faceSign F τ v * f (insert a (τ.erase v)) := by
  have hanot : a ∉ τ := fun h => by have := ha a h; omega
  have hkey : ∑ v ∈ τ, faceSign F (insert a τ) v * f ((insert a τ).erase v)
      = - ∑ v ∈ τ, faceSign F τ v * f (insert a (τ.erase v)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hav : a ≠ v := fun h => by have := ha v hv; omega
    rw [pathFaceSign_insert_of_lt hanot (ha v hv), Finset.erase_insert_of_ne hav]
    ring
  rw [simplicialCoboundary_apply, Finset.sum_insert hanot, pathFaceSign_insert_self ha,
    Finset.erase_insert hanot, one_mul, hkey]
  ring

/-! ### `q` and `J` are chain maps up to sign -/

/-- **`qδ = -δq`.** -/
theorem pathTailMap_simplicialCoboundary (f : Finset ℕ → F) {τ : Finset ℕ}
    (hτ : IsTailSet τ) :
    pathTailMap F (simplicialCoboundary F f) τ
      = - simplicialCoboundary F (pathTailMap F f) τ := by
  have h1 : ∀ u ∈ τ, 1 < u := fun u hu => by have := hτ u hu; omega
  have h0 : ∀ u ∈ τ, 0 < u := fun u hu => by have := hτ u hu; omega
  have e1 := pathCoboundary_insert_of_min (F := F) f h1
  have e0 := pathCoboundary_insert_of_min (F := F) f h0
  have e2 : simplicialCoboundary F (pathTailMap F f) τ
      = ∑ v ∈ τ, faceSign F τ v * f (insert 1 (τ.erase v))
        - ∑ v ∈ τ, faceSign F τ v * f (insert 0 (τ.erase v)) := by
    rw [simplicialCoboundary_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [pathTailMap]
    ring
  rw [pathTailMap, e1, e0, e2]
  ring

theorem pathErase_erase_comm (σ : Finset ℕ) (a b : ℕ) :
    (σ.erase a).erase b = (σ.erase b).erase a := by
  ext x
  simp only [Finset.mem_erase]
  tauto

/-- **`δJ = -Jδ`.** -/
theorem simplicialCoboundary_pathIncl (g : Finset ℕ → F) {n : ℕ} {σ : Finset ℕ}
    (hσ : IsPathFace n σ) :
    simplicialCoboundary F (pathIncl F g) σ
      = - pathIncl F (simplicialCoboundary F g) σ := by
  by_cases h1 : 1 ∈ σ
  · have h0 : 0 ∉ σ := fun h => hσ.2 0 h h1
    have hlt : ∀ v ∈ σ.erase 1, 1 < v := by
      intro v hv
      have hvσ : v ∈ σ := Finset.mem_of_mem_erase hv
      have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
      rcases Nat.lt_or_ge v 2 with h | h
      · interval_cases v
        · exact absurd hvσ h0
        · exact absurd rfl hv1
      · omega
    have hone : faceSign F σ 1 * pathIncl F g (σ.erase 1) = 0 := by
      rw [pathIncl_of_notMem (Finset.notMem_erase 1 σ), mul_zero]
    have hrest : ∀ v ∈ σ.erase 1, faceSign F σ v * pathIncl F g (σ.erase v)
        = - (faceSign F (σ.erase 1) v * g ((σ.erase 1).erase v)) := by
      intro v hv
      have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
      rw [pathIncl_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hv1, h1⟩),
        pathErase_erase_comm σ v 1, faceSign_erase_of_lt h1 (hlt v hv)]
      ring
    rw [pathIncl_of_mem h1, simplicialCoboundary_apply, simplicialCoboundary_apply,
      ← Finset.add_sum_erase σ _ h1, hone, zero_add,
      Finset.sum_congr rfl hrest, Finset.sum_neg_distrib]
  · rw [pathIncl_of_notMem h1, neg_zero, simplicialCoboundary_apply]
    refine Finset.sum_eq_zero (fun v hv => ?_)
    rw [pathIncl_of_notMem (fun h => h1 (Finset.mem_of_mem_erase h)), mul_zero]

/-! ### The contraction identity -/

/-- **`δK + Kδ = id - Jq` on path faces.** -/
theorem simplicialCoboundary_pathCone_add (f : Finset ℕ → F) {n : ℕ} {σ : Finset ℕ}
    (hσ : IsPathFace n σ) :
    simplicialCoboundary F (pathCone F f) σ + pathCone F (simplicialCoboundary F f) σ
      = f σ - pathIncl F (pathTailMap F f) σ := by
  by_cases h0 : 0 ∈ σ
  · have h1 : 1 ∉ σ := fun h => hσ.2 0 h0 h
    have hsingle : ∑ v ∈ σ, faceSign F σ v * pathCone F f (σ.erase v)
        = faceSign F σ 0 * pathCone F f (σ.erase 0) := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro v hv hv0
        rw [pathCone_of_mem_zero (Finset.mem_erase.mpr ⟨Ne.symm hv0, h0⟩), mul_zero]
      · intro h
        exact absurd h0 h
    rw [pathCone_of_mem_zero h0, add_zero, pathIncl_of_notMem h1, sub_zero,
      simplicialCoboundary_apply, hsingle, pathFaceSign_zero, one_mul,
      pathCone_of_notMem (Finset.notMem_erase 0 σ)
        (fun h => h1 (Finset.mem_of_mem_erase h)), Finset.insert_erase h0]
  · by_cases h1 : 1 ∈ σ
    · have hsingle : ∑ v ∈ σ, faceSign F σ v * pathCone F f (σ.erase v)
          = faceSign F σ 1 * pathCone F f (σ.erase 1) := by
        refine Finset.sum_eq_single 1 ?_ ?_
        · intro v hv hv1
          rw [pathCone_of_mem_one (Finset.mem_erase.mpr ⟨Ne.symm hv1, h1⟩), mul_zero]
        · intro h
          exact absurd h1 h
      rw [pathCone_of_mem_one h1, add_zero, pathIncl_of_mem h1, pathTailMap,
        Finset.insert_erase h1, simplicialCoboundary_apply, hsingle, pathFaceSign_one h0, one_mul,
        pathCone_of_notMem (fun h => h0 (Finset.mem_of_mem_erase h))
          (Finset.notMem_erase 1 σ)]
      ring
    · rw [pathIncl_of_notMem h1, sub_zero]
      have hagree : ∀ (g : Finset ℕ → F) (τ : Finset ℕ), 1 ∉ τ →
          pathCone F g τ = simplicialCone F 0 g τ := by
        intro g τ hτ1
        by_cases hτ0 : 0 ∈ τ
        · rw [pathCone_of_mem_zero hτ0, simplicialCone_of_mem _ hτ0]
        · rw [pathCone_of_notMem hτ0 hτ1, simplicialCone_of_notMem _ hτ0, pathFaceSign_zero, one_mul]
      have hsum : simplicialCoboundary F (pathCone F f) σ
          = simplicialCoboundary F (simplicialCone F 0 f) σ := by
        rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
        refine Finset.sum_congr rfl (fun v hv => ?_)
        rw [hagree f _ (fun h => h1 (Finset.mem_of_mem_erase h))]
      rw [hsum, hagree (simplicialCoboundary F f) σ h1]
      exact simplicialCoboundary_simplicialCone_add (F := F) (α := ℕ) 0 f σ

/-! ### The cochain complex of the path complex in the occupation grading -/

/-- The coboundary of the path complex: the reduced simplicial coboundary, evaluated only at the
faces of the complex. -/
def pathCoboundary (F : Type*) [CommRing F] (n : ℕ) (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if IsPathFace n σ then simplicialCoboundary F f σ else 0

theorem pathCoboundary_of_face {n : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : IsPathFace n σ) : pathCoboundary F n f σ = simplicialCoboundary F f σ := by
  rw [pathCoboundary, if_pos h]

theorem pathCoboundary_of_not_face {n : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsPathFace n σ) : pathCoboundary F n f σ = 0 := by
  rw [pathCoboundary, if_neg h]

/-- The path coboundary as an `F`-linear map. -/
def pathCoboundaryₗ (F : Type*) [CommRing F] (n : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := pathCoboundary F n
  map_add' f g := by
    funext σ
    by_cases h : IsPathFace n σ
    · rw [pathCoboundary_of_face h, Pi.add_apply, pathCoboundary_of_face h,
        pathCoboundary_of_face h]
      exact congrFun (map_add (simplicialCoboundaryₗ F) f g) σ
    · rw [pathCoboundary_of_not_face h, Pi.add_apply, pathCoboundary_of_not_face h,
        pathCoboundary_of_not_face h, add_zero]
  map_smul' r f := by
    funext σ
    by_cases h : IsPathFace n σ
    · rw [pathCoboundary_of_face h, RingHom.id_apply, Pi.smul_apply,
        pathCoboundary_of_face h]
      exact congrFun (map_smul (simplicialCoboundaryₗ F) r f) σ
    · rw [pathCoboundary_of_not_face h, RingHom.id_apply, Pi.smul_apply,
        pathCoboundary_of_not_face h, smul_zero]

@[simp]
theorem pathCoboundaryₗ_apply (n : ℕ) (f : Finset ℕ → F) :
    pathCoboundaryₗ F n f = pathCoboundary F n f := rfl

/-- **`δ² = 0` for the path complex.** -/
theorem pathCoboundary_pathCoboundary (n : ℕ) (f : Finset ℕ → F) :
    pathCoboundary F n (pathCoboundary F n f) = 0 := by
  funext σ
  by_cases h : IsPathFace n σ
  · rw [pathCoboundary_of_face h, simplicialCoboundary_apply]
    have hterm : ∀ v ∈ σ, faceSign F σ v * pathCoboundary F n f (σ.erase v)
        = faceSign F σ v * simplicialCoboundary F f (σ.erase v) := by
      intro v _
      rw [pathCoboundary_of_face (h.erase v)]
    rw [Finset.sum_congr rfl hterm]
    have := simplicialCoboundary_simplicialCoboundary (F := F) f
    rw [← simplicialCoboundary_apply]
    exact congrFun this σ
  · rw [pathCoboundary_of_not_face h]
    rfl

theorem pathCoboundaryₗ_comp_self (n : ℕ) :
    (pathCoboundaryₗ F n) ∘ₗ (pathCoboundaryₗ F n) = 0 :=
  LinearMap.ext fun f => pathCoboundary_pathCoboundary n f

/-! ### Cochains supported on the faces of one occupation degree -/

/-- Cochains supported on the path faces of occupation degree `j`. -/
def pathSupported (F : Type*) [CommRing F] (n j : ℕ) : Submodule F (Finset ℕ → F) where
  carrier := {f | ∀ σ : Finset ℕ, (σ.card ≠ j ∨ ¬ IsPathFace n σ) → f σ = 0}
  add_mem' hf hg := fun σ hσ => by
    simp only [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun σ hσ => by
    show r * _ = 0
    rw [hf σ hσ, mul_zero]

theorem mem_pathSupported {n j : ℕ} {f : Finset ℕ → F} :
    f ∈ pathSupported F n j ↔ ∀ σ : Finset ℕ, (σ.card ≠ j ∨ ¬ IsPathFace n σ) → f σ = 0 :=
  Iff.rfl

/-- **The path coboundary raises the occupation degree by one.** -/
theorem pathCoboundary_mem_pathSupported {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ pathSupported F n j) :
    pathCoboundary F n f ∈ pathSupported F n (j + 1) := by
  intro σ hσ
  rcases hσ with hc | hface
  · by_cases hface : IsPathFace n σ
    · rw [pathCoboundary_of_face hface, simplicialCoboundary_apply]
      refine Finset.sum_eq_zero (fun v hv => ?_)
      have hpos : 1 ≤ σ.card := Finset.card_pos.mpr ⟨v, hv⟩
      have : (σ.erase v).card ≠ j := by
        rw [Finset.card_erase_of_mem hv]
        omega
      rw [hf _ (Or.inl this), mul_zero]
    · rw [pathCoboundary_of_not_face hface]
  · rw [pathCoboundary_of_not_face hface]

/-! ### The tail complex and the three graded maps -/

/-- Faces of the tail complex: path faces contained in `{3, 4, …}`. -/
def IsTailFace (n : ℕ) (τ : Finset ℕ) : Prop := IsPathFace n τ ∧ IsTailSet τ

instance instDecidableIsTailFace (n : ℕ) (τ : Finset ℕ) : Decidable (IsTailFace n τ) :=
  decidable_of_iff (IsPathFace n τ ∧ ∀ v ∈ τ, 3 ≤ v) Iff.rfl

theorem IsTailFace.insert_one {n : ℕ} {τ : Finset ℕ} (h : IsTailFace n τ) (hn : 1 < n) :
    IsPathFace n (insert 1 τ) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hn
    · exact h.1.1 v hv
  · intro v hv hv1
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · omega
      · have := h.2 2 h2; omega
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · have := h.2 v hv; omega
      · exact h.1.2 v hv h2

theorem IsTailFace.insert_zero {n : ℕ} {τ : Finset ℕ} (h : IsTailFace n τ) (hn : 0 < n) :
    IsPathFace n (insert 0 τ) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hn
    · exact h.1.1 v hv
  · intro v hv hv1
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · omega
      · have := h.2 1 h2; omega
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · have := h.2 v hv; omega
      · exact h.1.2 v hv h2

/-- Cochains supported on the tail faces of occupation degree `j`. -/
def tailSupported (F : Type*) [CommRing F] (n j : ℕ) : Submodule F (Finset ℕ → F) where
  carrier := {f | ∀ τ : Finset ℕ, (τ.card ≠ j ∨ ¬ IsTailFace n τ) → f τ = 0}
  add_mem' hf hg := fun σ hσ => by
    simp only [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun σ hσ => by
    show r * _ = 0
    rw [hf σ hσ, mul_zero]

theorem mem_tailSupported {n j : ℕ} {f : Finset ℕ → F} :
    f ∈ tailSupported F n j ↔ ∀ τ : Finset ℕ, (τ.card ≠ j ∨ ¬ IsTailFace n τ) → f τ = 0 :=
  Iff.rfl

/-- The tail inclusion, guarded to land on the faces of the path complex. -/
def pathInclFace (F : Type*) [CommRing F] (n : ℕ) (g : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if IsPathFace n σ then pathIncl F g σ else 0

/-- The tail contraction, guarded to land on the faces of the tail complex. -/
def pathTailMapFace (F : Type*) [CommRing F] (n : ℕ) (f : Finset ℕ → F) (τ : Finset ℕ) : F :=
  if IsTailFace n τ then pathTailMap F f τ else 0

/-- The path cone, guarded to land on the faces of the path complex. -/
def pathConeFace (F : Type*) [CommRing F] (n : ℕ) (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if IsPathFace n σ then pathCone F f σ else 0

theorem pathInclFace_of_face {n : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ} (h : IsPathFace n σ) :
    pathInclFace F n g σ = pathIncl F g σ := by
  rw [pathInclFace, if_pos h]

theorem pathTailMapFace_of_face {n : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : IsTailFace n τ) : pathTailMapFace F n f τ = pathTailMap F f τ := by
  rw [pathTailMapFace, if_pos h]

theorem pathConeFace_of_face {n : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ} (h : IsPathFace n σ) :
    pathConeFace F n f σ = pathCone F f σ := by
  rw [pathConeFace, if_pos h]

/-! ### The graded maps respect the occupation degree -/

theorem pathInclFace_mem_pathSupported {n j : ℕ} {g : Finset ℕ → F}
    (hg : g ∈ tailSupported F n j) :
    pathInclFace F n g ∈ pathSupported F n (j + 1) := by
  intro σ hσ
  by_cases hface : IsPathFace n σ
  · rw [pathInclFace_of_face hface]
    by_cases h1 : 1 ∈ σ
    · rw [pathIncl_of_mem h1]
      refine hg _ ?_
      rcases hσ with hc | hc
      · left
        rw [Finset.card_erase_of_mem h1]
        have hpos : 1 ≤ σ.card := Finset.card_pos.mpr ⟨1, h1⟩
        omega
      · exact absurd hface hc
    · rw [pathIncl_of_notMem h1]
  · rw [pathInclFace, if_neg hface]

theorem pathTailMapFace_mem_tailSupported {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ pathSupported F n (j + 1)) :
    pathTailMapFace F n f ∈ tailSupported F n j := by
  intro τ hτ
  by_cases hface : IsTailFace n τ
  · rw [pathTailMapFace_of_face hface, pathTailMap]
    have hc : τ.card ≠ j := by
      rcases hτ with hc | hc
      · exact hc
      · exact absurd hface hc
    have h1 : 1 ∉ τ := hface.2.notMem_one
    have h0 : 0 ∉ τ := hface.2.notMem_zero
    rw [hf _ (Or.inl (by rw [Finset.card_insert_of_notMem h1]; omega)),
      hf _ (Or.inl (by rw [Finset.card_insert_of_notMem h0]; omega)), sub_zero]
  · rw [pathTailMapFace, if_neg hface]

theorem pathConeFace_mem_pathSupported {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ pathSupported F n (j + 1)) :
    pathConeFace F n f ∈ pathSupported F n j := by
  intro σ hσ
  by_cases hface : IsPathFace n σ
  · rw [pathConeFace_of_face hface]
    by_cases h : 0 ∈ σ ∨ 1 ∈ σ
    · rw [pathCone, if_pos h]
    · push Not at h
      rw [pathCone_of_notMem h.1 h.2]
      refine hf _ ?_
      rcases hσ with hc | hc
      · left
        rw [Finset.card_insert_of_notMem h.1]
        omega
      · exact absurd hface hc
  · rw [pathConeFace, if_neg hface]

/-! ### The identities for the graded maps -/

/-- **`qJ = id` for the graded maps.** -/
theorem pathTailMapFace_pathInclFace (g : Finset ℕ → F) {n : ℕ} {τ : Finset ℕ}
    (hτ : IsTailFace n τ) (hn : 1 < n) :
    pathTailMapFace F n (pathInclFace F n g) τ = g τ := by
  rw [pathTailMapFace_of_face hτ, pathTailMap,
    pathInclFace_of_face (hτ.insert_one hn), pathInclFace_of_face (hτ.insert_zero (by omega)),
    ← pathTailMap]
  exact pathTailMap_pathIncl g hτ.2.notMem_zero hτ.2.notMem_one

/-- **`δK + Kδ = id − Jq` for the graded maps, on path faces.** -/
theorem pathCoboundary_pathConeFace_add (f : Finset ℕ → F) {n : ℕ} (hn : 0 < n)
    {σ : Finset ℕ} (hσ : IsPathFace n σ) :
    pathCoboundary F n (pathConeFace F n f) σ + pathConeFace F n (pathCoboundary F n f) σ
      = f σ - pathInclFace F n (pathTailMapFace F n f) σ := by
  have hK : simplicialCoboundary F (pathConeFace F n f) σ
      = simplicialCoboundary F (pathCone F f) σ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [pathConeFace_of_face (hσ.erase v)]
  have hsecond : pathConeFace F n (pathCoboundary F n f) σ
      = pathCone F (simplicialCoboundary F f) σ := by
    rw [pathConeFace_of_face hσ]
    by_cases h : 0 ∈ σ ∨ 1 ∈ σ
    · rw [pathCone, if_pos h, pathCone, if_pos h]
    · push Not at h
      have hins : IsPathFace n (insert 0 σ) := by
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hn
          · exact hσ.1 v hv
        · intro v hv hv1
          rcases Finset.mem_insert.mp hv with rfl | hv
          · rcases Finset.mem_insert.mp hv1 with h2 | h2
            · omega
            · exact h.2 h2
          · rcases Finset.mem_insert.mp hv1 with h2 | h2
            · omega
            · exact hσ.2 v hv h2
      rw [pathCone_of_notMem h.1 h.2, pathCone_of_notMem h.1 h.2, pathCoboundary_of_face hins]
  have hJ : pathInclFace F n (pathTailMapFace F n f) σ = pathIncl F (pathTailMap F f) σ := by
    rw [pathInclFace_of_face hσ]
    by_cases h1 : 1 ∈ σ
    · have h0 : 0 ∉ σ := fun h => hσ.2 0 h h1
      have hτ : IsTailFace n (σ.erase 1) := by
        refine ⟨hσ.erase 1, ?_⟩
        intro v hv
        have hvσ : v ∈ σ := Finset.mem_of_mem_erase hv
        have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
        rcases Nat.lt_or_ge v 3 with h | h
        · interval_cases v
          · exact absurd hvσ h0
          · exact absurd rfl hv1
          · exact absurd hvσ (fun h2 => hσ.2 1 h1 h2)
        · exact h
      rw [pathIncl_of_mem h1, pathIncl_of_mem h1, pathTailMapFace_of_face hτ]
    · rw [pathIncl_of_notMem h1, pathIncl_of_notMem h1]
  rw [pathCoboundary_of_face hσ, hK, hsecond, hJ]
  exact simplicialCoboundary_pathCone_add f hσ

/-! ### The tail coboundary -/

/-- The coboundary of the tail complex: the reduced simplicial coboundary, evaluated only at the
faces of the tail complex. -/
def tailCoboundary (F : Type*) [CommRing F] (n : ℕ) (f : Finset ℕ → F) (τ : Finset ℕ) : F :=
  if IsTailFace n τ then simplicialCoboundary F f τ else 0

theorem IsTailFace.erase {n : ℕ} {τ : Finset ℕ} (h : IsTailFace n τ) (v : ℕ) :
    IsTailFace n (τ.erase v) :=
  ⟨h.1.erase v, h.2.erase v⟩

theorem tailCoboundary_of_face {n : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : IsTailFace n τ) : tailCoboundary F n f τ = simplicialCoboundary F f τ := by
  rw [tailCoboundary, if_pos h]

theorem tailCoboundary_of_not_face {n : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : ¬ IsTailFace n τ) : tailCoboundary F n f τ = 0 := by
  rw [tailCoboundary, if_neg h]

/-- The tail coboundary as an `F`-linear map. -/
def tailCoboundaryₗ (F : Type*) [CommRing F] (n : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := tailCoboundary F n
  map_add' f g := by
    funext τ
    by_cases h : IsTailFace n τ
    · rw [tailCoboundary_of_face h, Pi.add_apply, tailCoboundary_of_face h,
        tailCoboundary_of_face h]
      exact congrFun (map_add (simplicialCoboundaryₗ F) f g) τ
    · rw [tailCoboundary_of_not_face h, Pi.add_apply, tailCoboundary_of_not_face h,
        tailCoboundary_of_not_face h, add_zero]
  map_smul' r f := by
    funext τ
    by_cases h : IsTailFace n τ
    · rw [tailCoboundary_of_face h, RingHom.id_apply, Pi.smul_apply, tailCoboundary_of_face h]
      exact congrFun (map_smul (simplicialCoboundaryₗ F) r f) τ
    · rw [tailCoboundary_of_not_face h, RingHom.id_apply, Pi.smul_apply,
        tailCoboundary_of_not_face h, smul_zero]

@[simp]
theorem tailCoboundaryₗ_apply (n : ℕ) (f : Finset ℕ → F) :
    tailCoboundaryₗ F n f = tailCoboundary F n f := rfl

/-- **`δ² = 0` for the tail complex.** -/
theorem tailCoboundary_tailCoboundary (n : ℕ) (f : Finset ℕ → F) :
    tailCoboundary F n (tailCoboundary F n f) = 0 := by
  funext τ
  by_cases h : IsTailFace n τ
  · rw [tailCoboundary_of_face h, simplicialCoboundary_apply]
    have hterm : ∀ v ∈ τ, faceSign F τ v * tailCoboundary F n f (τ.erase v)
        = faceSign F τ v * simplicialCoboundary F f (τ.erase v) := by
      intro v _
      rw [tailCoboundary_of_face (h.erase v)]
    rw [Finset.sum_congr rfl hterm, ← simplicialCoboundary_apply]
    exact congrFun (simplicialCoboundary_simplicialCoboundary (F := F) f) τ
  · rw [tailCoboundary_of_not_face h]
    rfl

theorem tailCoboundary_mem_tailSupported {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ tailSupported F n j) :
    tailCoboundary F n f ∈ tailSupported F n (j + 1) := by
  intro τ hτ
  rcases hτ with hc | hface
  · by_cases hface : IsTailFace n τ
    · rw [tailCoboundary_of_face hface, simplicialCoboundary_apply]
      refine Finset.sum_eq_zero (fun v hv => ?_)
      have hpos : 1 ≤ τ.card := Finset.card_pos.mpr ⟨v, hv⟩
      have hne : (τ.erase v).card ≠ j := by
        rw [Finset.card_erase_of_mem hv]
        omega
      rw [hf _ (Or.inl hne), mul_zero]
    · rw [tailCoboundary_of_not_face hface]
  · rw [tailCoboundary_of_not_face hface]

/-! ### Reduced cohomology in the occupation grading -/

/-- Reduced cocycles of the path complex in occupation degree `j`. -/
def pathCocycles (F : Type*) [CommRing F] (n j : ℕ) : Submodule F (Finset ℕ → F) :=
  pathSupported F n j ⊓ LinearMap.ker (pathCoboundaryₗ F n)

/-- Reduced coboundaries of the path complex in occupation degree `j`. -/
def pathCoboundaries (F : Type*) [CommRing F] (n : ℕ) : ℕ → Submodule F (Finset ℕ → F)
  | 0 => ⊥
  | (i + 1) => Submodule.map (pathCoboundaryₗ F n) (pathSupported F n i)

theorem pathCoboundaries_le_pathCocycles (n j : ℕ) :
    pathCoboundaries F n j ≤ pathCocycles F n j := by
  match j with
  | 0 => exact bot_le
  | (i + 1) =>
    rintro x ⟨f, hf, rfl⟩
    refine ⟨pathCoboundary_mem_pathSupported hf, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact pathCoboundary_pathCoboundary n f

/-- Reduced cohomology of the path complex in occupation degree `j`. -/
abbrev pathCohomology (F : Type*) [CommRing F] (n j : ℕ) : Type _ :=
  (pathCocycles F n j) ⧸
    (Submodule.comap (pathCocycles F n j).subtype (pathCoboundaries F n j))

/-- Reduced cocycles of the tail complex in occupation degree `j`. -/
def tailCocycles (F : Type*) [CommRing F] (n j : ℕ) : Submodule F (Finset ℕ → F) :=
  tailSupported F n j ⊓ LinearMap.ker (tailCoboundaryₗ F n)

/-- Reduced coboundaries of the tail complex in occupation degree `j`. -/
def tailCoboundaries (F : Type*) [CommRing F] (n : ℕ) : ℕ → Submodule F (Finset ℕ → F)
  | 0 => ⊥
  | (i + 1) => Submodule.map (tailCoboundaryₗ F n) (tailSupported F n i)

theorem tailCoboundaries_le_tailCocycles (n j : ℕ) :
    tailCoboundaries F n j ≤ tailCocycles F n j := by
  match j with
  | 0 => exact bot_le
  | (i + 1) =>
    rintro x ⟨f, hf, rfl⟩
    refine ⟨tailCoboundary_mem_tailSupported hf, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact tailCoboundary_tailCoboundary n f

/-- Reduced cohomology of the tail complex in occupation degree `j`. -/
abbrev tailCohomology (F : Type*) [CommRing F] (n j : ℕ) : Type _ :=
  (tailCocycles F n j) ⧸
    (Submodule.comap (tailCocycles F n j).subtype (tailCoboundaries F n j))

/-! ### The guarded maps are chain maps up to sign -/

theorem IsPathFace.erase_one_isTailFace {n : ℕ} {σ : Finset ℕ} (hσ : IsPathFace n σ)
    (h1 : 1 ∈ σ) : IsTailFace n (σ.erase 1) := by
  have h0 : 0 ∉ σ := fun h => hσ.2 0 h h1
  refine ⟨hσ.erase 1, ?_⟩
  intro v hv
  have hvσ : v ∈ σ := Finset.mem_of_mem_erase hv
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  rcases Nat.lt_or_ge v 3 with h | h
  · interval_cases v
    · exact absurd hvσ h0
    · exact absurd rfl hv1
    · exact absurd hvσ (fun h2 => hσ.2 1 h1 h2)
  · exact h

/-- **`qδ = −δq` for the guarded maps, on tail faces.** -/
theorem tailCoboundary_pathTailMapFace (f : Finset ℕ → F) {n : ℕ} (hn : 1 < n)
    {τ : Finset ℕ} (hτ : IsTailFace n τ) :
    tailCoboundary F n (pathTailMapFace F n f) τ
      = - pathTailMapFace F n (pathCoboundary F n f) τ := by
  have hL : simplicialCoboundary F (pathTailMapFace F n f) τ
      = simplicialCoboundary F (pathTailMap F f) τ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [pathTailMapFace_of_face (hτ.erase v)]
  have hR : pathTailMapFace F n (pathCoboundary F n f) τ
      = pathTailMap F (simplicialCoboundary F f) τ := by
    rw [pathTailMapFace_of_face hτ, pathTailMap, pathTailMap,
      pathCoboundary_of_face (hτ.insert_one hn),
      pathCoboundary_of_face (hτ.insert_zero (by omega))]
  rw [tailCoboundary_of_face hτ, hL, hR, pathTailMap_simplicialCoboundary f hτ.2]
  ring

/-- **`δJ = −Jδ` for the guarded maps, on path faces.** -/
theorem pathCoboundary_pathInclFace (g : Finset ℕ → F) {n : ℕ} {σ : Finset ℕ}
    (hσ : IsPathFace n σ) :
    pathCoboundary F n (pathInclFace F n g) σ
      = - pathInclFace F n (tailCoboundary F n g) σ := by
  have hL : simplicialCoboundary F (pathInclFace F n g) σ
      = simplicialCoboundary F (pathIncl F g) σ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [pathInclFace_of_face (hσ.erase v)]
  have hR : pathInclFace F n (tailCoboundary F n g) σ
      = pathIncl F (simplicialCoboundary F g) σ := by
    rw [pathInclFace_of_face hσ]
    by_cases h1 : 1 ∈ σ
    · rw [pathIncl_of_mem h1, pathIncl_of_mem h1,
        tailCoboundary_of_face (hσ.erase_one_isTailFace h1)]
    · rw [pathIncl_of_notMem h1, pathIncl_of_notMem h1]
  rw [pathCoboundary_of_face hσ, hL, hR]
  exact simplicialCoboundary_pathIncl g hσ

/-! ### The identities as equalities of cochains -/

theorem pathTailMapFace_of_not_face {n : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : ¬ IsTailFace n τ) : pathTailMapFace F n f τ = 0 := by
  rw [pathTailMapFace, if_neg h]

theorem pathInclFace_of_not_face {n : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsPathFace n σ) : pathInclFace F n g σ = 0 := by
  rw [pathInclFace, if_neg h]

theorem pathConeFace_of_not_face {n : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsPathFace n σ) : pathConeFace F n f σ = 0 := by
  rw [pathConeFace, if_neg h]

/-- **`qδ = −δq` as an equality of cochains.** -/
theorem pathTailMapFace_pathCoboundary_eq (f : Finset ℕ → F) {n : ℕ} (hn : 1 < n) :
    pathTailMapFace F n (pathCoboundary F n f)
      = - tailCoboundary F n (pathTailMapFace F n f) := by
  funext τ
  by_cases hτ : IsTailFace n τ
  · rw [Pi.neg_apply, tailCoboundary_pathTailMapFace f hn hτ, neg_neg]
  · rw [pathTailMapFace_of_not_face hτ, Pi.neg_apply, tailCoboundary_of_not_face hτ, neg_zero]

/-- **`δJ = −Jδ` as an equality of cochains.** -/
theorem pathCoboundary_pathInclFace_eq (g : Finset ℕ → F) (n : ℕ) :
    pathCoboundary F n (pathInclFace F n g)
      = - pathInclFace F n (tailCoboundary F n g) := by
  funext σ
  by_cases hσ : IsPathFace n σ
  · exact pathCoboundary_pathInclFace g hσ
  · rw [pathCoboundary_of_not_face hσ, Pi.neg_apply, pathInclFace_of_not_face hσ, neg_zero]

/-- **`qJ = id` as an equality of cochains on tail-supported cochains.** -/
theorem pathTailMapFace_pathInclFace_eq {g : Finset ℕ → F} {n j : ℕ} (hn : 1 < n)
    (hg : g ∈ tailSupported F n j) :
    pathTailMapFace F n (pathInclFace F n g) = g := by
  funext τ
  by_cases hτ : IsTailFace n τ
  · exact pathTailMapFace_pathInclFace g hτ hn
  · rw [pathTailMapFace_of_not_face hτ, hg τ (Or.inr hτ)]

/-- **`δK + Kδ = id − Jq` as an equality of cochains on face-supported cochains.** -/
theorem pathCoboundary_pathConeFace_add_eq {f : Finset ℕ → F} {n j : ℕ} (hn : 0 < n)
    (hf : f ∈ pathSupported F n j) :
    pathCoboundary F n (pathConeFace F n f) + pathConeFace F n (pathCoboundary F n f)
      = f - pathInclFace F n (pathTailMapFace F n f) := by
  funext σ
  by_cases hσ : IsPathFace n σ
  · exact pathCoboundary_pathConeFace_add f hn hσ
  · rw [Pi.add_apply, pathCoboundary_of_not_face hσ, pathConeFace_of_not_face hσ, add_zero,
      Pi.sub_apply, pathInclFace_of_not_face hσ, hf σ (Or.inr hσ), sub_zero]

/-! ### The graded maps as linear maps -/

/-- The guarded tail contraction as an `F`-linear map. -/
def pathTailMapFaceₗ (F : Type*) [CommRing F] (n : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := pathTailMapFace F n
  map_add' f g := by
    funext τ
    by_cases h : IsTailFace n τ
    · rw [pathTailMapFace_of_face h, Pi.add_apply, pathTailMapFace_of_face h,
        pathTailMapFace_of_face h, pathTailMap, pathTailMap, pathTailMap]
      simp only [Pi.add_apply]
      ring
    · rw [pathTailMapFace_of_not_face h, Pi.add_apply, pathTailMapFace_of_not_face h,
        pathTailMapFace_of_not_face h, add_zero]
  map_smul' r f := by
    funext τ
    by_cases h : IsTailFace n τ
    · rw [pathTailMapFace_of_face h, RingHom.id_apply, Pi.smul_apply,
        pathTailMapFace_of_face h, pathTailMap, pathTailMap]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [pathTailMapFace_of_not_face h, RingHom.id_apply, Pi.smul_apply,
        pathTailMapFace_of_not_face h, smul_zero]

@[simp]
theorem pathTailMapFaceₗ_apply (n : ℕ) (f : Finset ℕ → F) :
    pathTailMapFaceₗ F n f = pathTailMapFace F n f := rfl

/-- The guarded tail inclusion as an `F`-linear map. -/
def pathInclFaceₗ (F : Type*) [CommRing F] (n : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := pathInclFace F n
  map_add' g h := by
    funext σ
    by_cases hface : IsPathFace n σ
    · rw [pathInclFace_of_face hface, Pi.add_apply, pathInclFace_of_face hface,
        pathInclFace_of_face hface]
      by_cases h1 : 1 ∈ σ
      · rw [pathIncl_of_mem h1, pathIncl_of_mem h1, pathIncl_of_mem h1, Pi.add_apply]
      · rw [pathIncl_of_notMem h1, pathIncl_of_notMem h1, pathIncl_of_notMem h1, add_zero]
    · rw [pathInclFace_of_not_face hface, Pi.add_apply, pathInclFace_of_not_face hface,
        pathInclFace_of_not_face hface, add_zero]
  map_smul' r g := by
    funext σ
    by_cases hface : IsPathFace n σ
    · rw [pathInclFace_of_face hface, RingHom.id_apply, Pi.smul_apply,
        pathInclFace_of_face hface]
      by_cases h1 : 1 ∈ σ
      · rw [pathIncl_of_mem h1, pathIncl_of_mem h1, Pi.smul_apply]
      · rw [pathIncl_of_notMem h1, pathIncl_of_notMem h1, smul_zero]
    · rw [pathInclFace_of_not_face hface, RingHom.id_apply, Pi.smul_apply,
        pathInclFace_of_not_face hface, smul_zero]

@[simp]
theorem pathInclFaceₗ_apply (n : ℕ) (g : Finset ℕ → F) :
    pathInclFaceₗ F n g = pathInclFace F n g := rfl

/-- The guarded path cone as an `F`-linear map. -/
def pathConeFaceₗ (F : Type*) [CommRing F] (n : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := pathConeFace F n
  map_add' f g := by
    funext σ
    by_cases hface : IsPathFace n σ
    · rw [pathConeFace_of_face hface, Pi.add_apply, pathConeFace_of_face hface,
        pathConeFace_of_face hface]
      by_cases h : 0 ∈ σ ∨ 1 ∈ σ
      · rw [pathCone, if_pos h, pathCone, if_pos h, pathCone, if_pos h, add_zero]
      · push Not at h
        rw [pathCone_of_notMem h.1 h.2, pathCone_of_notMem h.1 h.2, pathCone_of_notMem h.1 h.2,
          Pi.add_apply]
    · rw [pathConeFace_of_not_face hface, Pi.add_apply, pathConeFace_of_not_face hface,
        pathConeFace_of_not_face hface, add_zero]
  map_smul' r f := by
    funext σ
    by_cases hface : IsPathFace n σ
    · rw [pathConeFace_of_face hface, RingHom.id_apply, Pi.smul_apply,
        pathConeFace_of_face hface]
      by_cases h : 0 ∈ σ ∨ 1 ∈ σ
      · rw [pathCone, if_pos h, pathCone, if_pos h, smul_zero]
      · push Not at h
        rw [pathCone_of_notMem h.1 h.2, pathCone_of_notMem h.1 h.2, Pi.smul_apply]
    · rw [pathConeFace_of_not_face hface, RingHom.id_apply, Pi.smul_apply,
        pathConeFace_of_not_face hface, smul_zero]

@[simp]
theorem pathConeFaceₗ_apply (n : ℕ) (f : Finset ℕ → F) :
    pathConeFaceₗ F n f = pathConeFace F n f := rfl

/-! ### The reduction on cocycles -/

/-- **Every path cocycle differs from `J q f` by the explicit coboundary `δ K f`.** -/
theorem pathCocycles_sub_pathInclFace_pathTailMapFace {f : Finset ℕ → F} {n j : ℕ} (hn : 0 < n)
    (hf : f ∈ pathCocycles F n j) :
    f - pathInclFace F n (pathTailMapFace F n f)
      = pathCoboundary F n (pathConeFace F n f) := by
  have hδ : pathCoboundary F n f = 0 := by
    have := hf.2
    rw [SetLike.mem_coe, LinearMap.mem_ker] at this
    exact this
  have hzero : pathConeFace F n (pathCoboundary F n f) = 0 := by
    rw [hδ]
    exact (pathConeFaceₗ F n).map_zero
  rw [← pathCoboundary_pathConeFace_add_eq hn hf.1, hzero, add_zero]

/-! ### `q` and `J` transport cocycles and coboundaries -/

theorem pathTailMapFace_zero (n : ℕ) : pathTailMapFace F n (0 : Finset ℕ → F) = 0 :=
  (pathTailMapFaceₗ F n).map_zero

theorem pathInclFace_zero (n : ℕ) : pathInclFace F n (0 : Finset ℕ → F) = 0 :=
  (pathInclFaceₗ F n).map_zero

theorem pathConeFace_zero (n : ℕ) : pathConeFace F n (0 : Finset ℕ → F) = 0 :=
  (pathConeFaceₗ F n).map_zero

theorem tailCoboundary_zero (n : ℕ) : tailCoboundary F n (0 : Finset ℕ → F) = 0 :=
  (tailCoboundaryₗ F n).map_zero

theorem pathCoboundary_eq_zero_of_mem_pathCocycles {f : Finset ℕ → F} {n j : ℕ}
    (hf : f ∈ pathCocycles F n j) : pathCoboundary F n f = 0 := by
  have h := hf.2
  rw [SetLike.mem_coe, LinearMap.mem_ker] at h
  exact h

theorem tailCoboundary_eq_zero_of_mem_tailCocycles {g : Finset ℕ → F} {n j : ℕ}
    (hg : g ∈ tailCocycles F n j) : tailCoboundary F n g = 0 := by
  have h := hg.2
  rw [SetLike.mem_coe, LinearMap.mem_ker] at h
  exact h

theorem pathTailMapFace_mem_tailCocycles {f : Finset ℕ → F} {n j : ℕ} (hn : 1 < n)
    (hf : f ∈ pathCocycles F n (j + 1)) :
    pathTailMapFace F n f ∈ tailCocycles F n j := by
  refine ⟨pathTailMapFace_mem_tailSupported hf.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show tailCoboundary F n (pathTailMapFace F n f) = 0
  have h := pathTailMapFace_pathCoboundary_eq f hn
  rw [pathCoboundary_eq_zero_of_mem_pathCocycles hf, pathTailMapFace_zero] at h
  exact neg_eq_zero.mp h.symm

theorem pathInclFace_mem_pathCocycles {g : Finset ℕ → F} {n j : ℕ}
    (hg : g ∈ tailCocycles F n j) :
    pathInclFace F n g ∈ pathCocycles F n (j + 1) := by
  refine ⟨pathInclFace_mem_pathSupported hg.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show pathCoboundary F n (pathInclFace F n g) = 0
  have h := pathCoboundary_pathInclFace_eq g n
  rw [tailCoboundary_eq_zero_of_mem_tailCocycles hg, pathInclFace_zero, neg_zero] at h
  exact h

theorem pathTailMapFace_mem_tailCoboundaries {f : Finset ℕ → F} {n j : ℕ} (hn : 1 < n)
    (hf : f ∈ pathCoboundaries F n (j + 1)) :
    pathTailMapFace F n f ∈ tailCoboundaries F n j := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hq := pathTailMapFace_pathCoboundary_eq h hn
  have hval : pathTailMapFace F n ((pathCoboundaryₗ F n) h)
      = - tailCoboundary F n (pathTailMapFace F n h) := hq
  match j with
  | 0 =>
    have hzero : pathTailMapFace F n h = 0 := by
      funext τ
      show pathTailMapFace F n h τ = 0
      by_cases hτ : IsTailFace n τ
      · rw [pathTailMapFace_of_face hτ, pathTailMap,
          hh _ (Or.inl (by
            rw [Finset.card_insert_of_notMem hτ.2.notMem_one]
            omega)),
          hh _ (Or.inl (by
            rw [Finset.card_insert_of_notMem hτ.2.notMem_zero]
            omega)), sub_zero]
      · rw [pathTailMapFace_of_not_face hτ]
    rw [hval, hzero, tailCoboundary_zero, neg_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    rw [hval]
    refine Submodule.neg_mem _ ⟨pathTailMapFace F n h, ?_, rfl⟩
    exact pathTailMapFace_mem_tailSupported hh

theorem pathInclFace_mem_pathCoboundaries {g : Finset ℕ → F} {n j : ℕ}
    (hg : g ∈ tailCoboundaries F n j) :
    pathInclFace F n g ∈ pathCoboundaries F n (j + 1) := by
  match j with
  | 0 =>
    have hgb : g ∈ (⊥ : Submodule F (Finset ℕ → F)) := hg
    have hg0 : g = 0 := (Submodule.mem_bot F).mp hgb
    rw [hg0, pathInclFace_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    obtain ⟨h, hh, rfl⟩ := hg
    have hval : pathInclFace F n ((tailCoboundaryₗ F n) h)
        = - pathCoboundary F n (pathInclFace F n h) := by
      have hj := pathCoboundary_pathInclFace_eq h n
      show pathInclFace F n (tailCoboundary F n h)
        = - pathCoboundary F n (pathInclFace F n h)
      rw [hj]
      ring
    rw [hval]
    refine Submodule.neg_mem _ ⟨pathInclFace F n h, ?_, rfl⟩
    exact pathInclFace_mem_pathSupported hh

/-! ### The cohomology isomorphism with a shift of one in occupation degree -/

/-- The tail contraction restricted to cocycles. -/
def pathTailMapCocycles (F : Type*) [CommRing F] (n j : ℕ) (hn : 1 < n) :
    pathCocycles F n (j + 1) →ₗ[F] tailCocycles F n j :=
  LinearMap.restrict (pathTailMapFaceₗ F n)
    (fun _ hx => pathTailMapFace_mem_tailCocycles hn hx)

/-- The tail inclusion restricted to cocycles. -/
def pathInclCocycles (F : Type*) [CommRing F] (n j : ℕ) :
    tailCocycles F n j →ₗ[F] pathCocycles F n (j + 1) :=
  LinearMap.restrict (pathInclFaceₗ F n)
    (fun _ hx => pathInclFace_mem_pathCocycles hx)

/-- The induced map on reduced cohomology, lowering the occupation degree by one. -/
def pathTailMapCohomology (F : Type*) [CommRing F] (n j : ℕ) (hn : 1 < n) :
    pathCohomology F n (j + 1) →ₗ[F] tailCohomology F n j :=
  Submodule.mapQ _ _ (pathTailMapCocycles F n j hn) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ pathCoboundaries F n (j + 1) := hx
    show pathTailMapFace F n (x : Finset ℕ → F) ∈ tailCoboundaries F n j
    exact pathTailMapFace_mem_tailCoboundaries hn hxv)

/-- The induced map on reduced cohomology, raising the occupation degree by one. -/
def pathInclCohomology (F : Type*) [CommRing F] (n j : ℕ) :
    tailCohomology F n j →ₗ[F] pathCohomology F n (j + 1) :=
  Submodule.mapQ _ _ (pathInclCocycles F n j) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ tailCoboundaries F n j := hx
    show pathInclFace F n (x : Finset ℕ → F) ∈ pathCoboundaries F n (j + 1)
    exact pathInclFace_mem_pathCoboundaries hxv)

theorem pathTailMapCohomology_pathInclCohomology (n j : ℕ) (hn : 1 < n)
    (y : tailCohomology F n j) :
    pathTailMapCohomology F n j hn (pathInclCohomology F n j y) = y := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [pathInclCohomology, Submodule.mapQ_apply, pathTailMapCohomology, Submodule.mapQ_apply]
  refine congrArg _ (Subtype.ext ?_)
  show pathTailMapFace F n (pathInclFace F n g.val) = g.val
  exact pathTailMapFace_pathInclFace_eq hn g.property.1

theorem pathInclCohomology_pathTailMapCohomology (n j : ℕ) (hn : 1 < n)
    (x : pathCohomology F n (j + 1)) :
    pathInclCohomology F n j (pathTailMapCohomology F n j hn x) = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [pathTailMapCohomology, Submodule.mapQ_apply, pathInclCohomology, Submodule.mapQ_apply,
    Submodule.Quotient.eq]
  show (pathInclFace F n (pathTailMapFace F n f.val) : Finset ℕ → F) - f.val
    ∈ pathCoboundaries F n (j + 1)
  have hkey := pathCocycles_sub_pathInclFace_pathTailMapFace (by omega : 0 < n) f.property
  have hsub : (pathInclFace F n (pathTailMapFace F n f.val) : Finset ℕ → F) - f.val
      = - pathCoboundary F n (pathConeFace F n f.val) := by
    rw [← hkey]
    ring
  rw [hsub]
  exact Submodule.neg_mem _
    ⟨pathConeFace F n f.val, pathConeFace_mem_pathSupported f.property.1, rfl⟩

/-- **The three-vertex reduction.** The tail contraction and the tail inclusion are inverse
isomorphisms of reduced cohomology, with a shift of one in occupation degree. -/
def pathCohomologyEquiv (F : Type*) [CommRing F] (n j : ℕ) (hn : 1 < n) :
    pathCohomology F n (j + 1) ≃ₗ[F] tailCohomology F n j :=
  LinearEquiv.ofLinear (pathTailMapCohomology F n j hn) (pathInclCohomology F n j)
    (LinearMap.ext fun y => pathTailMapCohomology_pathInclCohomology n j hn y)
    (LinearMap.ext fun x => pathInclCohomology_pathTailMapCohomology n j hn x)

end
end GaloisForLFunctions.HTGeometry
