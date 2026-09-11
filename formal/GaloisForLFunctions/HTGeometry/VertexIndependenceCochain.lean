import GaloisForLFunctions.HTGeometry.PathIndependenceCochain

/-!
# The leaf reduction of an arbitrary induced path independence complex

Let `V` be a finite set of natural numbers, regarded as the vertex set of the induced subgraph of
the infinite path on `ℕ` (so `v` and `v + 1` are adjacent when both lie in `V`). A face of the
independence complex is a subset of `V` with no two adjacent members.

If `a` is the least element of `V` and `a + 1 ∈ V` as well, then `a` is a leaf whose unique
neighbour is `a + 1`, and the three explicit maps

  `(K f)(σ) = 0` if `a ∈ σ` or `a + 1 ∈ σ`, and `f ({a} ∪ σ)` otherwise,
  `(q f)(τ) = f ({a+1} ∪ τ) - f ({a} ∪ τ)`,
  `(J g)(σ) = g (σ \ {a+1})` if `a + 1 ∈ σ`, and `0` otherwise,

satisfy `δK + Kδ = id - Jq`, `qJ = id`, `qδ = -δq`, `δJ = -Jδ`, where the tail complex is the
independence complex on `tailVerts V a = {v ∈ V | a + 3 ≤ v}`, that is, on `V` with the closed
neighbourhood of `a + 1` deleted. Hence

  `cohomologyEquiv : cohomology F V (j+1) ≃ₗ[F] cohomology F (tailVerts V a) j`.

This is the vertex-set form of the three-vertex reduction of `PathIndependenceCochain`, where `V`
was `Finset.range n` and `a` was `0`. It applies to induced subgraphs that are not paths, in
particular to disjoint unions of paths, which is what joins of independence complexes are.
-/

namespace GaloisForLFunctions.HTGeometry
namespace VertexIndependence

noncomputable section
open Finset

variable {F : Type*} [CommRing F]

/-! ### Faces -/

/-- `σ` is a face of the independence complex of the induced subgraph of the path on `V`. -/
def IsFace (V σ : Finset ℕ) : Prop :=
  (∀ v ∈ σ, v ∈ V) ∧ ∀ v ∈ σ, v + 1 ∉ σ

instance instDecidableIsFace (V σ : Finset ℕ) : Decidable (IsFace V σ) :=
  decidable_of_iff ((∀ v ∈ σ, v ∈ V) ∧ ∀ v ∈ σ, v + 1 ∉ σ) Iff.rfl

theorem IsFace.subset {V σ τ : Finset ℕ} (h : IsFace V σ) (hτ : τ ⊆ σ) : IsFace V τ :=
  ⟨fun v hv => h.1 v (hτ hv), fun v hv hv1 => h.2 v (hτ hv) (hτ hv1)⟩

theorem IsFace.erase {V σ : Finset ℕ} (h : IsFace V σ) (v : ℕ) : IsFace V (σ.erase v) :=
  h.subset (Finset.erase_subset v σ)

theorem IsFace.mono {V W σ : Finset ℕ} (h : IsFace V σ) (hVW : V ⊆ W) : IsFace W σ :=
  ⟨fun v hv => hVW (h.1 v hv), h.2⟩

theorem isFace_empty (V : Finset ℕ) : IsFace V (∅ : Finset ℕ) :=
  ⟨fun v hv => absurd hv (by simp), fun v hv => absurd hv (by simp)⟩

/-- `a` is a leaf of the induced path on `V`: it is the least vertex and its successor is also a
vertex, so `a + 1` is its unique neighbour. -/
structure IsLeaf (V : Finset ℕ) (a : ℕ) : Prop where
  min : ∀ v ∈ V, a ≤ v
  mem : a ∈ V
  memSucc : a + 1 ∈ V

theorem IsLeaf.face_min {V : Finset ℕ} {a : ℕ} (hL : IsLeaf V a) {σ : Finset ℕ}
    (hσ : IsFace V σ) : ∀ u ∈ σ, a ≤ u :=
  fun u hu => hL.min u (hσ.1 u hu)

/-! ### The tail vertex set -/

/-- The tail vertex set: `V` with the closed neighbourhood `{a, a+1, a+2}` of the leaf's
neighbour deleted. When `a` is the least element of `V` this is exactly `V \ {a, a+1, a+2}`. -/
def tailVerts (V : Finset ℕ) (a : ℕ) : Finset ℕ := V.filter (fun v => a + 3 ≤ v)

theorem mem_tailVerts {V : Finset ℕ} {a v : ℕ} :
    v ∈ tailVerts V a ↔ v ∈ V ∧ a + 3 ≤ v := by
  rw [tailVerts, Finset.mem_filter]

theorem tailVerts_subset (V : Finset ℕ) (a : ℕ) : tailVerts V a ⊆ V :=
  Finset.filter_subset _ _

theorem IsFace.tailSet {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ} (h : IsFace (tailVerts V a) τ) :
    ∀ v ∈ τ, a + 3 ≤ v :=
  fun v hv => (mem_tailVerts.mp (h.1 v hv)).2

theorem IsFace.of_tailVerts {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) : IsFace V τ :=
  h.mono (tailVerts_subset V a)

theorem IsFace.notMem_self {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) : a ∉ τ := fun hv => by
  have := h.tailSet a hv; omega

theorem IsFace.notMem_succ {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) : a + 1 ∉ τ := fun hv => by
  have := h.tailSet (a + 1) hv; omega

theorem IsFace.notMem_succSucc {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) : a + 2 ∉ τ := fun hv => by
  have := h.tailSet (a + 2) hv; omega

theorem IsFace.insert_succ {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) (ha1 : a + 1 ∈ V) : IsFace V (insert (a + 1) τ) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha1
    · exact h.of_tailVerts.1 v hv
  · intro v hv hv1
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · omega
      · exact absurd h2 h.notMem_succSucc
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · have := h.tailSet v hv; omega
      · exact h.2 v hv h2

theorem IsFace.insert_self {V : Finset ℕ} {a : ℕ} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) (ha : a ∈ V) : IsFace V (insert a τ) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha
    · exact h.of_tailVerts.1 v hv
  · intro v hv hv1
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · omega
      · exact absurd h2 h.notMem_succ
    · rcases Finset.mem_insert.mp hv1 with h2 | h2
      · have := h.tailSet v hv; omega
      · exact h.2 v hv h2

theorem IsFace.erase_succ_tailVerts {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    {σ : Finset ℕ} (hσ : IsFace V σ) (h1 : a + 1 ∈ σ) :
    IsFace (tailVerts V a) (σ.erase (a + 1)) := by
  have h0 : a ∉ σ := fun h => hσ.2 a h h1
  have h2 : a + 2 ∉ σ := fun h => hσ.2 (a + 1) h1 h
  refine ⟨fun v hv => ?_, (hσ.erase (a + 1)).2⟩
  have hvσ : v ∈ σ := Finset.mem_of_mem_erase hv
  have hv1 : v ≠ a + 1 := Finset.ne_of_mem_erase hv
  refine mem_tailVerts.mpr ⟨hσ.1 v hvσ, ?_⟩
  have hva : a ≤ v := hmin v (hσ.1 v hvσ)
  have hv0 : v ≠ a := fun h => h0 (h ▸ hvσ)
  have hv2 : v ≠ a + 2 := fun h => h2 (h ▸ hvσ)
  omega

/-! ### Incidence signs at the leaf and its neighbour -/

theorem faceSign_min {a : ℕ} {σ : Finset ℕ} (h : ∀ u ∈ σ, a ≤ u) : faceSign F σ a = 1 := by
  have hf : σ.filter (· < a) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro v hv
    have := h v hv
    omega
  rw [faceSign, hf, Finset.card_empty, pow_zero]

theorem faceSign_succ {a : ℕ} {σ : Finset ℕ} (hmin : ∀ u ∈ σ, a ≤ u) (h0 : a ∉ σ) :
    faceSign F σ (a + 1) = 1 := by
  have hf : σ.filter (· < a + 1) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro v hv hlt
    have := hmin v hv
    exact h0 (by rwa [show v = a from by omega] at hv)
  rw [faceSign, hf, Finset.card_empty, pow_zero]

/-! ### The three explicit maps -/

/-- The cone at the leaf `a`, cut off on the faces meeting its neighbour `a + 1`. -/
def cone (F : Type*) [CommRing F] (a : ℕ) (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if a ∈ σ ∨ a + 1 ∈ σ then 0 else f (insert a σ)

/-- The tail contraction, lowering the occupation degree by one. -/
def tailMap (F : Type*) [CommRing F] (a : ℕ) (f : Finset ℕ → F) (τ : Finset ℕ) : F :=
  f (insert (a + 1) τ) - f (insert a τ)

/-- The tail inclusion, raising the occupation degree by one. -/
def incl (F : Type*) [CommRing F] (a : ℕ) (g : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if a + 1 ∈ σ then g (σ.erase (a + 1)) else 0

theorem cone_of_mem_self {a : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ} (h : a ∈ σ) :
    cone F a f σ = 0 := by
  rw [cone, if_pos (Or.inl h)]

theorem cone_of_mem_succ {a : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ} (h : a + 1 ∈ σ) :
    cone F a f σ = 0 := by
  rw [cone, if_pos (Or.inr h)]

theorem cone_of_notMem {a : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ} (h0 : a ∉ σ)
    (h1 : a + 1 ∉ σ) : cone F a f σ = f (insert a σ) := by
  rw [cone, if_neg (by tauto)]

theorem incl_of_mem {a : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ} (h : a + 1 ∈ σ) :
    incl F a g σ = g (σ.erase (a + 1)) := by
  rw [incl, if_pos h]

theorem incl_of_notMem {a : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ} (h : a + 1 ∉ σ) :
    incl F a g σ = 0 := by
  rw [incl, if_neg h]

/-! ### `q ∘ J = id` -/

/-- **`qJ = id`.** -/
theorem tailMap_incl {a : ℕ} (g : Finset ℕ → F) {τ : Finset ℕ} (h0 : a ∉ τ)
    (h1 : a + 1 ∉ τ) : tailMap F a (incl F a g) τ = g τ := by
  rw [tailMap, incl_of_mem (Finset.mem_insert_self (a + 1) τ),
    incl_of_notMem (by simp [h1]), sub_zero, Finset.erase_insert h1]

/-! ### `q` and `J` are chain maps up to sign -/

/-- **`qδ = -δq`.** -/
theorem tailMap_simplicialCoboundary {a : ℕ} (f : Finset ℕ → F) {τ : Finset ℕ}
    (hτ : ∀ v ∈ τ, a + 3 ≤ v) :
    tailMap F a (simplicialCoboundary F f) τ
      = - simplicialCoboundary F (tailMap F a f) τ := by
  have h1 : ∀ u ∈ τ, a + 1 < u := fun u hu => by have := hτ u hu; omega
  have h0 : ∀ u ∈ τ, a < u := fun u hu => by have := hτ u hu; omega
  have e1 := pathCoboundary_insert_of_min (F := F) f h1
  have e0 := pathCoboundary_insert_of_min (F := F) f h0
  have e2 : simplicialCoboundary F (tailMap F a f) τ
      = ∑ v ∈ τ, faceSign F τ v * f (insert (a + 1) (τ.erase v))
        - ∑ v ∈ τ, faceSign F τ v * f (insert a (τ.erase v)) := by
    rw [simplicialCoboundary_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [tailMap]
    ring
  rw [tailMap, e1, e0, e2]
  ring

/-- **`δJ = -Jδ`.** -/
theorem simplicialCoboundary_incl {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (g : Finset ℕ → F) {σ : Finset ℕ} (hσ : IsFace V σ) :
    simplicialCoboundary F (incl F a g) σ = - incl F a (simplicialCoboundary F g) σ := by
  by_cases h1 : a + 1 ∈ σ
  · have h0 : a ∉ σ := fun h => hσ.2 a h h1
    have hlt : ∀ v ∈ σ.erase (a + 1), a + 1 < v := by
      intro v hv
      have hvσ : v ∈ σ := Finset.mem_of_mem_erase hv
      have hv1 : v ≠ a + 1 := Finset.ne_of_mem_erase hv
      have hva : a ≤ v := hmin v (hσ.1 v hvσ)
      have hv0 : v ≠ a := fun h => h0 (h ▸ hvσ)
      omega
    have hone : faceSign F σ (a + 1) * incl F a g (σ.erase (a + 1)) = 0 := by
      rw [incl_of_notMem (Finset.notMem_erase (a + 1) σ), mul_zero]
    have hrest : ∀ v ∈ σ.erase (a + 1), faceSign F σ v * incl F a g (σ.erase v)
        = - (faceSign F (σ.erase (a + 1)) v * g ((σ.erase (a + 1)).erase v)) := by
      intro v hv
      have hv1 : v ≠ a + 1 := Finset.ne_of_mem_erase hv
      rw [incl_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hv1, h1⟩),
        pathErase_erase_comm σ v (a + 1), faceSign_erase_of_lt h1 (hlt v hv)]
      ring
    rw [incl_of_mem h1, simplicialCoboundary_apply, simplicialCoboundary_apply,
      ← Finset.add_sum_erase σ _ h1, hone, zero_add,
      Finset.sum_congr rfl hrest, Finset.sum_neg_distrib]
  · rw [incl_of_notMem h1, neg_zero, simplicialCoboundary_apply]
    refine Finset.sum_eq_zero (fun v hv => ?_)
    rw [incl_of_notMem (fun h => h1 (Finset.mem_of_mem_erase h)), mul_zero]

/-! ### The contraction identity -/

theorem cone_eq_simplicialCone {a : ℕ} (g : Finset ℕ → F) {τ : Finset ℕ}
    (hmin : ∀ u ∈ τ, a ≤ u) (hτ1 : a + 1 ∉ τ) :
    cone F a g τ = simplicialCone F a g τ := by
  by_cases hτ0 : a ∈ τ
  · rw [cone_of_mem_self hτ0, simplicialCone_of_mem _ hτ0]
  · have hlt : ∀ u ∈ τ, a < u := fun u hu =>
      Nat.lt_of_le_of_ne (hmin u hu) (fun h => hτ0 (h ▸ hu))
    rw [cone_of_notMem hτ0 hτ1, simplicialCone_of_notMem _ hτ0,
      pathFaceSign_insert_self hlt, one_mul]

/-- **`δK + Kδ = id - Jq` on faces.** -/
theorem simplicialCoboundary_cone_add {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (f : Finset ℕ → F) {σ : Finset ℕ} (hσ : IsFace V σ) :
    simplicialCoboundary F (cone F a f) σ + cone F a (simplicialCoboundary F f) σ
      = f σ - incl F a (tailMap F a f) σ := by
  have hσmin : ∀ u ∈ σ, a ≤ u := fun u hu => hmin u (hσ.1 u hu)
  by_cases h0 : a ∈ σ
  · have h1 : a + 1 ∉ σ := fun h => hσ.2 a h0 h
    have hsingle : ∑ v ∈ σ, faceSign F σ v * cone F a f (σ.erase v)
        = faceSign F σ a * cone F a f (σ.erase a) := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro v hv hv0
        rw [cone_of_mem_self (Finset.mem_erase.mpr ⟨Ne.symm hv0, h0⟩), mul_zero]
      · intro h
        exact absurd h0 h
    rw [cone_of_mem_self h0, add_zero, incl_of_notMem h1, sub_zero,
      simplicialCoboundary_apply, hsingle, faceSign_min hσmin, one_mul,
      cone_of_notMem (Finset.notMem_erase a σ)
        (fun h => h1 (Finset.mem_of_mem_erase h)), Finset.insert_erase h0]
  · by_cases h1 : a + 1 ∈ σ
    · have hsingle : ∑ v ∈ σ, faceSign F σ v * cone F a f (σ.erase v)
          = faceSign F σ (a + 1) * cone F a f (σ.erase (a + 1)) := by
        refine Finset.sum_eq_single (a + 1) ?_ ?_
        · intro v hv hv1
          rw [cone_of_mem_succ (Finset.mem_erase.mpr ⟨Ne.symm hv1, h1⟩), mul_zero]
        · intro h
          exact absurd h1 h
      rw [cone_of_mem_succ h1, add_zero, incl_of_mem h1, tailMap,
        Finset.insert_erase h1, simplicialCoboundary_apply, hsingle,
        faceSign_succ hσmin h0, one_mul,
        cone_of_notMem (fun h => h0 (Finset.mem_of_mem_erase h))
          (Finset.notMem_erase (a + 1) σ)]
      ring
    · rw [incl_of_notMem h1, sub_zero]
      have hsum : simplicialCoboundary F (cone F a f) σ
          = simplicialCoboundary F (simplicialCone F a f) σ := by
        rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
        refine Finset.sum_congr rfl (fun v hv => ?_)
        rw [cone_eq_simplicialCone f (fun u hu => hσmin u (Finset.mem_of_mem_erase hu))
          (fun h => h1 (Finset.mem_of_mem_erase h))]
      rw [hsum, cone_eq_simplicialCone (simplicialCoboundary F f) hσmin h1]
      exact simplicialCoboundary_simplicialCone_add (F := F) (α := ℕ) a f σ

/-! ### The cochain complex in the occupation grading -/

/-- The coboundary of the independence complex on `V`: the reduced simplicial coboundary,
evaluated only at faces. -/
def coboundary (F : Type*) [CommRing F] (V : Finset ℕ) (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  if IsFace V σ then simplicialCoboundary F f σ else 0

theorem coboundary_of_face {V : Finset ℕ} {f : Finset ℕ → F} {σ : Finset ℕ} (h : IsFace V σ) :
    coboundary F V f σ = simplicialCoboundary F f σ := by
  rw [coboundary, if_pos h]

theorem coboundary_of_not_face {V : Finset ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsFace V σ) : coboundary F V f σ = 0 := by
  rw [coboundary, if_neg h]

/-- The coboundary as an `F`-linear map. -/
def coboundaryₗ (F : Type*) [CommRing F] (V : Finset ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := coboundary F V
  map_add' f g := by
    funext σ
    by_cases h : IsFace V σ
    · rw [coboundary_of_face h, Pi.add_apply, coboundary_of_face h, coboundary_of_face h]
      exact congrFun (map_add (simplicialCoboundaryₗ F) f g) σ
    · rw [coboundary_of_not_face h, Pi.add_apply, coboundary_of_not_face h,
        coboundary_of_not_face h, add_zero]
  map_smul' r f := by
    funext σ
    by_cases h : IsFace V σ
    · rw [coboundary_of_face h, RingHom.id_apply, Pi.smul_apply, coboundary_of_face h]
      exact congrFun (map_smul (simplicialCoboundaryₗ F) r f) σ
    · rw [coboundary_of_not_face h, RingHom.id_apply, Pi.smul_apply,
        coboundary_of_not_face h, smul_zero]

@[simp]
theorem coboundaryₗ_apply (V : Finset ℕ) (f : Finset ℕ → F) :
    coboundaryₗ F V f = coboundary F V f := rfl

/-- **`δ² = 0`.** -/
theorem coboundary_coboundary (V : Finset ℕ) (f : Finset ℕ → F) :
    coboundary F V (coboundary F V f) = 0 := by
  funext σ
  by_cases h : IsFace V σ
  · rw [coboundary_of_face h, simplicialCoboundary_apply]
    have hterm : ∀ v ∈ σ, faceSign F σ v * coboundary F V f (σ.erase v)
        = faceSign F σ v * simplicialCoboundary F f (σ.erase v) := by
      intro v _
      rw [coboundary_of_face (h.erase v)]
    rw [Finset.sum_congr rfl hterm, ← simplicialCoboundary_apply]
    exact congrFun (simplicialCoboundary_simplicialCoboundary (F := F) f) σ
  · rw [coboundary_of_not_face h]
    rfl

theorem coboundaryₗ_comp_self (V : Finset ℕ) :
    (coboundaryₗ F V) ∘ₗ (coboundaryₗ F V) = 0 :=
  LinearMap.ext fun f => coboundary_coboundary V f

/-! ### Cochains supported on the faces of one occupation degree -/

/-- Cochains supported on the faces of occupation degree `j`. -/
def supported (F : Type*) [CommRing F] (V : Finset ℕ) (j : ℕ) : Submodule F (Finset ℕ → F) where
  carrier := {f | ∀ σ : Finset ℕ, (σ.card ≠ j ∨ ¬ IsFace V σ) → f σ = 0}
  add_mem' hf hg := fun σ hσ => by
    simp only [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun σ hσ => by
    show r * _ = 0
    rw [hf σ hσ, mul_zero]

theorem mem_supported {V : Finset ℕ} {j : ℕ} {f : Finset ℕ → F} :
    f ∈ supported F V j ↔ ∀ σ : Finset ℕ, (σ.card ≠ j ∨ ¬ IsFace V σ) → f σ = 0 :=
  Iff.rfl

/-- **The coboundary raises the occupation degree by one.** -/
theorem coboundary_mem_supported {V : Finset ℕ} {j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ supported F V j) : coboundary F V f ∈ supported F V (j + 1) := by
  intro σ hσ
  rcases hσ with hc | hface
  · by_cases hface : IsFace V σ
    · rw [coboundary_of_face hface, simplicialCoboundary_apply]
      refine Finset.sum_eq_zero (fun v hv => ?_)
      have hpos : 1 ≤ σ.card := Finset.card_pos.mpr ⟨v, hv⟩
      have hne : (σ.erase v).card ≠ j := by
        rw [Finset.card_erase_of_mem hv]
        omega
      rw [hf _ (Or.inl hne), mul_zero]
    · rw [coboundary_of_not_face hface]
  · rw [coboundary_of_not_face hface]

/-! ### The guarded maps -/

/-- The tail inclusion, guarded to land on the faces of the complex on `V`. -/
def inclFace (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) (g : Finset ℕ → F)
    (σ : Finset ℕ) : F :=
  if IsFace V σ then incl F a g σ else 0

/-- The tail contraction, guarded to land on the faces of the tail complex. -/
def tailMapFace (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) (f : Finset ℕ → F)
    (τ : Finset ℕ) : F :=
  if IsFace (tailVerts V a) τ then tailMap F a f τ else 0

/-- The cone, guarded to land on the faces of the complex on `V`. -/
def coneFace (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) (f : Finset ℕ → F)
    (σ : Finset ℕ) : F :=
  if IsFace V σ then cone F a f σ else 0

theorem inclFace_of_face {V : Finset ℕ} {a : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ}
    (h : IsFace V σ) : inclFace F V a g σ = incl F a g σ := by
  rw [inclFace, if_pos h]

theorem inclFace_of_not_face {V : Finset ℕ} {a : ℕ} {g : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsFace V σ) : inclFace F V a g σ = 0 := by
  rw [inclFace, if_neg h]

theorem tailMapFace_of_face {V : Finset ℕ} {a : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : IsFace (tailVerts V a) τ) : tailMapFace F V a f τ = tailMap F a f τ := by
  rw [tailMapFace, if_pos h]

theorem tailMapFace_of_not_face {V : Finset ℕ} {a : ℕ} {f : Finset ℕ → F} {τ : Finset ℕ}
    (h : ¬ IsFace (tailVerts V a) τ) : tailMapFace F V a f τ = 0 := by
  rw [tailMapFace, if_neg h]

theorem coneFace_of_face {V : Finset ℕ} {a : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : IsFace V σ) : coneFace F V a f σ = cone F a f σ := by
  rw [coneFace, if_pos h]

theorem coneFace_of_not_face {V : Finset ℕ} {a : ℕ} {f : Finset ℕ → F} {σ : Finset ℕ}
    (h : ¬ IsFace V σ) : coneFace F V a f σ = 0 := by
  rw [coneFace, if_neg h]

/-! ### The graded maps respect the occupation degree -/

theorem inclFace_mem_supported {V : Finset ℕ} {a j : ℕ} {g : Finset ℕ → F}
    (hg : g ∈ supported F (tailVerts V a) j) :
    inclFace F V a g ∈ supported F V (j + 1) := by
  intro σ hσ
  by_cases hface : IsFace V σ
  · rw [inclFace_of_face hface]
    by_cases h1 : a + 1 ∈ σ
    · rw [incl_of_mem h1]
      refine hg _ ?_
      rcases hσ with hc | hc
      · left
        rw [Finset.card_erase_of_mem h1]
        have hpos : 1 ≤ σ.card := Finset.card_pos.mpr ⟨a + 1, h1⟩
        omega
      · exact absurd hface hc
    · rw [incl_of_notMem h1]
  · rw [inclFace, if_neg hface]

theorem tailMapFace_mem_supported {V : Finset ℕ} {a j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ supported F V (j + 1)) :
    tailMapFace F V a f ∈ supported F (tailVerts V a) j := by
  intro τ hτ
  by_cases hface : IsFace (tailVerts V a) τ
  · rw [tailMapFace_of_face hface, tailMap]
    have hc : τ.card ≠ j := by
      rcases hτ with hc | hc
      · exact hc
      · exact absurd hface hc
    have h1 : a + 1 ∉ τ := hface.notMem_succ
    have h0 : a ∉ τ := hface.notMem_self
    rw [hf _ (Or.inl (by rw [Finset.card_insert_of_notMem h1]; omega)),
      hf _ (Or.inl (by rw [Finset.card_insert_of_notMem h0]; omega)), sub_zero]
  · rw [tailMapFace, if_neg hface]

theorem coneFace_mem_supported {V : Finset ℕ} {a j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ supported F V (j + 1)) : coneFace F V a f ∈ supported F V j := by
  intro σ hσ
  by_cases hface : IsFace V σ
  · rw [coneFace_of_face hface]
    by_cases h : a ∈ σ ∨ a + 1 ∈ σ
    · rw [cone, if_pos h]
    · push Not at h
      rw [cone_of_notMem h.1 h.2]
      refine hf _ ?_
      rcases hσ with hc | hc
      · left
        rw [Finset.card_insert_of_notMem h.1]
        omega
      · exact absurd hface hc
  · rw [coneFace, if_neg hface]

/-! ### The identities for the graded maps -/

/-- **`qJ = id` for the graded maps.** -/
theorem tailMapFace_inclFace {V : Finset ℕ} {a : ℕ} (g : Finset ℕ → F) {τ : Finset ℕ}
    (hτ : IsFace (tailVerts V a) τ) (ha : a ∈ V) (ha1 : a + 1 ∈ V) :
    tailMapFace F V a (inclFace F V a g) τ = g τ := by
  rw [tailMapFace_of_face hτ, tailMap,
    inclFace_of_face (hτ.insert_succ ha1), inclFace_of_face (hτ.insert_self ha),
    ← tailMap]
  exact tailMap_incl g hτ.notMem_self hτ.notMem_succ

/-- **`δK + Kδ = id − Jq` for the graded maps, on faces.** -/
theorem coboundary_coneFace_add {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v) (ha : a ∈ V)
    (f : Finset ℕ → F) {σ : Finset ℕ} (hσ : IsFace V σ) :
    coboundary F V (coneFace F V a f) σ + coneFace F V a (coboundary F V f) σ
      = f σ - inclFace F V a (tailMapFace F V a f) σ := by
  have hK : simplicialCoboundary F (coneFace F V a f) σ
      = simplicialCoboundary F (cone F a f) σ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [coneFace_of_face (hσ.erase v)]
  have hsecond : coneFace F V a (coboundary F V f) σ
      = cone F a (simplicialCoboundary F f) σ := by
    rw [coneFace_of_face hσ]
    by_cases h : a ∈ σ ∨ a + 1 ∈ σ
    · rw [cone, if_pos h, cone, if_pos h]
    · push Not at h
      have hins : IsFace V (insert a σ) := by
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact ha
          · exact hσ.1 v hv
        · intro v hv hv1
          rcases Finset.mem_insert.mp hv with rfl | hv
          · rcases Finset.mem_insert.mp hv1 with h2 | h2
            · omega
            · exact h.2 h2
          · rcases Finset.mem_insert.mp hv1 with h2 | h2
            · have := hmin v (hσ.1 v hv); omega
            · exact hσ.2 v hv h2
      rw [cone_of_notMem h.1 h.2, cone_of_notMem h.1 h.2, coboundary_of_face hins]
  have hJ : inclFace F V a (tailMapFace F V a f) σ = incl F a (tailMap F a f) σ := by
    rw [inclFace_of_face hσ]
    by_cases h1 : a + 1 ∈ σ
    · rw [incl_of_mem h1, incl_of_mem h1,
        tailMapFace_of_face (hσ.erase_succ_tailVerts hmin h1)]
    · rw [incl_of_notMem h1, incl_of_notMem h1]
  rw [coboundary_of_face hσ, hK, hsecond, hJ]
  exact simplicialCoboundary_cone_add hmin f hσ

/-- **`qδ = −δq` for the graded maps, on tail faces.** -/
theorem coboundary_tailMapFace {V : Finset ℕ} {a : ℕ} (ha : a ∈ V) (ha1 : a + 1 ∈ V)
    (f : Finset ℕ → F) {τ : Finset ℕ} (hτ : IsFace (tailVerts V a) τ) :
    coboundary F (tailVerts V a) (tailMapFace F V a f) τ
      = - tailMapFace F V a (coboundary F V f) τ := by
  have hL : simplicialCoboundary F (tailMapFace F V a f) τ
      = simplicialCoboundary F (tailMap F a f) τ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [tailMapFace_of_face (hτ.erase v)]
  have hR : tailMapFace F V a (coboundary F V f) τ
      = tailMap F a (simplicialCoboundary F f) τ := by
    rw [tailMapFace_of_face hτ, tailMap, tailMap,
      coboundary_of_face (hτ.insert_succ ha1),
      coboundary_of_face (hτ.insert_self ha)]
  rw [coboundary_of_face hτ, hL, hR, tailMap_simplicialCoboundary f hτ.tailSet]
  ring

/-- **`δJ = −Jδ` for the graded maps, on faces.** -/
theorem coboundary_inclFace {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (g : Finset ℕ → F) {σ : Finset ℕ} (hσ : IsFace V σ) :
    coboundary F V (inclFace F V a g) σ
      = - inclFace F V a (coboundary F (tailVerts V a) g) σ := by
  have hL : simplicialCoboundary F (inclFace F V a g) σ
      = simplicialCoboundary F (incl F a g) σ := by
    rw [simplicialCoboundary_apply, simplicialCoboundary_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [inclFace_of_face (hσ.erase v)]
  have hR : inclFace F V a (coboundary F (tailVerts V a) g) σ
      = incl F a (simplicialCoboundary F g) σ := by
    rw [inclFace_of_face hσ]
    by_cases h1 : a + 1 ∈ σ
    · rw [incl_of_mem h1, incl_of_mem h1,
        coboundary_of_face (hσ.erase_succ_tailVerts hmin h1)]
    · rw [incl_of_notMem h1, incl_of_notMem h1]
  rw [coboundary_of_face hσ, hL, hR]
  exact simplicialCoboundary_incl hmin g hσ

/-! ### The identities as equalities of cochains -/

/-- **`qδ = −δq` as an equality of cochains.** -/
theorem tailMapFace_coboundary_eq {V : Finset ℕ} {a : ℕ} (ha : a ∈ V) (ha1 : a + 1 ∈ V)
    (f : Finset ℕ → F) :
    tailMapFace F V a (coboundary F V f)
      = - coboundary F (tailVerts V a) (tailMapFace F V a f) := by
  funext τ
  by_cases hτ : IsFace (tailVerts V a) τ
  · rw [Pi.neg_apply, coboundary_tailMapFace ha ha1 f hτ, neg_neg]
  · rw [tailMapFace_of_not_face hτ, Pi.neg_apply, coboundary_of_not_face hτ, neg_zero]

/-- **`δJ = −Jδ` as an equality of cochains.** -/
theorem coboundary_inclFace_eq {V : Finset ℕ} {a : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (g : Finset ℕ → F) :
    coboundary F V (inclFace F V a g)
      = - inclFace F V a (coboundary F (tailVerts V a) g) := by
  funext σ
  by_cases hσ : IsFace V σ
  · exact coboundary_inclFace hmin g hσ
  · rw [coboundary_of_not_face hσ, Pi.neg_apply, inclFace_of_not_face hσ, neg_zero]

/-- **`qJ = id` as an equality of cochains on tail-supported cochains.** -/
theorem tailMapFace_inclFace_eq {V : Finset ℕ} {a j : ℕ} (ha : a ∈ V) (ha1 : a + 1 ∈ V)
    {g : Finset ℕ → F} (hg : g ∈ supported F (tailVerts V a) j) :
    tailMapFace F V a (inclFace F V a g) = g := by
  funext τ
  by_cases hτ : IsFace (tailVerts V a) τ
  · exact tailMapFace_inclFace g hτ ha ha1
  · rw [tailMapFace_of_not_face hτ, hg τ (Or.inr hτ)]

/-- **`δK + Kδ = id − Jq` as an equality of cochains on face-supported cochains.** -/
theorem coboundary_coneFace_add_eq {V : Finset ℕ} {a j : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (ha : a ∈ V) {f : Finset ℕ → F} (hf : f ∈ supported F V j) :
    coboundary F V (coneFace F V a f) + coneFace F V a (coboundary F V f)
      = f - inclFace F V a (tailMapFace F V a f) := by
  funext σ
  by_cases hσ : IsFace V σ
  · exact coboundary_coneFace_add hmin ha f hσ
  · rw [Pi.add_apply, coboundary_of_not_face hσ, coneFace_of_not_face hσ, add_zero,
      Pi.sub_apply, inclFace_of_not_face hσ, hf σ (Or.inr hσ), sub_zero]

/-! ### The graded maps as linear maps -/

/-- The guarded tail contraction as an `F`-linear map. -/
def tailMapFaceₗ (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := tailMapFace F V a
  map_add' f g := by
    funext τ
    by_cases h : IsFace (tailVerts V a) τ
    · rw [tailMapFace_of_face h, Pi.add_apply, tailMapFace_of_face h,
        tailMapFace_of_face h, tailMap, tailMap, tailMap]
      simp only [Pi.add_apply]
      ring
    · rw [tailMapFace_of_not_face h, Pi.add_apply, tailMapFace_of_not_face h,
        tailMapFace_of_not_face h, add_zero]
  map_smul' r f := by
    funext τ
    by_cases h : IsFace (tailVerts V a) τ
    · rw [tailMapFace_of_face h, RingHom.id_apply, Pi.smul_apply,
        tailMapFace_of_face h, tailMap, tailMap]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [tailMapFace_of_not_face h, RingHom.id_apply, Pi.smul_apply,
        tailMapFace_of_not_face h, smul_zero]

@[simp]
theorem tailMapFaceₗ_apply (V : Finset ℕ) (a : ℕ) (f : Finset ℕ → F) :
    tailMapFaceₗ F V a f = tailMapFace F V a f := rfl

/-- The guarded tail inclusion as an `F`-linear map. -/
def inclFaceₗ (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := inclFace F V a
  map_add' g h := by
    funext σ
    by_cases hface : IsFace V σ
    · rw [inclFace_of_face hface, Pi.add_apply, inclFace_of_face hface,
        inclFace_of_face hface]
      by_cases h1 : a + 1 ∈ σ
      · rw [incl_of_mem h1, incl_of_mem h1, incl_of_mem h1, Pi.add_apply]
      · rw [incl_of_notMem h1, incl_of_notMem h1, incl_of_notMem h1, add_zero]
    · rw [inclFace_of_not_face hface, Pi.add_apply, inclFace_of_not_face hface,
        inclFace_of_not_face hface, add_zero]
  map_smul' r g := by
    funext σ
    by_cases hface : IsFace V σ
    · rw [inclFace_of_face hface, RingHom.id_apply, Pi.smul_apply, inclFace_of_face hface]
      by_cases h1 : a + 1 ∈ σ
      · rw [incl_of_mem h1, incl_of_mem h1, Pi.smul_apply]
      · rw [incl_of_notMem h1, incl_of_notMem h1, smul_zero]
    · rw [inclFace_of_not_face hface, RingHom.id_apply, Pi.smul_apply,
        inclFace_of_not_face hface, smul_zero]

@[simp]
theorem inclFaceₗ_apply (V : Finset ℕ) (a : ℕ) (g : Finset ℕ → F) :
    inclFaceₗ F V a g = inclFace F V a g := rfl

/-- The guarded cone as an `F`-linear map. -/
def coneFaceₗ (F : Type*) [CommRing F] (V : Finset ℕ) (a : ℕ) :
    (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := coneFace F V a
  map_add' f g := by
    funext σ
    by_cases hface : IsFace V σ
    · rw [coneFace_of_face hface, Pi.add_apply, coneFace_of_face hface,
        coneFace_of_face hface]
      by_cases h : a ∈ σ ∨ a + 1 ∈ σ
      · rw [cone, if_pos h, cone, if_pos h, cone, if_pos h, add_zero]
      · push Not at h
        rw [cone_of_notMem h.1 h.2, cone_of_notMem h.1 h.2, cone_of_notMem h.1 h.2,
          Pi.add_apply]
    · rw [coneFace_of_not_face hface, Pi.add_apply, coneFace_of_not_face hface,
        coneFace_of_not_face hface, add_zero]
  map_smul' r f := by
    funext σ
    by_cases hface : IsFace V σ
    · rw [coneFace_of_face hface, RingHom.id_apply, Pi.smul_apply, coneFace_of_face hface]
      by_cases h : a ∈ σ ∨ a + 1 ∈ σ
      · rw [cone, if_pos h, cone, if_pos h, smul_zero]
      · push Not at h
        rw [cone_of_notMem h.1 h.2, cone_of_notMem h.1 h.2, Pi.smul_apply]
    · rw [coneFace_of_not_face hface, RingHom.id_apply, Pi.smul_apply,
        coneFace_of_not_face hface, smul_zero]

@[simp]
theorem coneFaceₗ_apply (V : Finset ℕ) (a : ℕ) (f : Finset ℕ → F) :
    coneFaceₗ F V a f = coneFace F V a f := rfl

/-! ### Reduced cohomology in the occupation grading -/

/-- Reduced cocycles in occupation degree `j`. -/
def cocycles (F : Type*) [CommRing F] (V : Finset ℕ) (j : ℕ) : Submodule F (Finset ℕ → F) :=
  supported F V j ⊓ LinearMap.ker (coboundaryₗ F V)

/-- Reduced coboundaries in occupation degree `j`. -/
def coboundaries (F : Type*) [CommRing F] (V : Finset ℕ) : ℕ → Submodule F (Finset ℕ → F)
  | 0 => ⊥
  | (i + 1) => Submodule.map (coboundaryₗ F V) (supported F V i)

theorem coboundaries_le_cocycles (V : Finset ℕ) (j : ℕ) :
    coboundaries F V j ≤ cocycles F V j := by
  match j with
  | 0 => exact bot_le
  | (i + 1) =>
    rintro x ⟨f, hf, rfl⟩
    refine ⟨coboundary_mem_supported hf, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact coboundary_coboundary V f

/-- Reduced cohomology of the independence complex on `V` in occupation degree `j`. -/
abbrev cohomology (F : Type*) [CommRing F] (V : Finset ℕ) (j : ℕ) : Type _ :=
  (cocycles F V j) ⧸ (Submodule.comap (cocycles F V j).subtype (coboundaries F V j))

theorem coboundary_eq_zero_of_mem_cocycles {V : Finset ℕ} {j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ cocycles F V j) : coboundary F V f = 0 := by
  have h := hf.2
  rw [SetLike.mem_coe, LinearMap.mem_ker] at h
  exact h

/-! ### The reduction on cocycles -/

/-- **Every cocycle differs from `J q f` by the explicit coboundary `δ K f`.** -/
theorem cocycles_sub_inclFace_tailMapFace {V : Finset ℕ} {a j : ℕ}
    (hmin : ∀ v ∈ V, a ≤ v) (ha : a ∈ V) {f : Finset ℕ → F} (hf : f ∈ cocycles F V j) :
    f - inclFace F V a (tailMapFace F V a f) = coboundary F V (coneFace F V a f) := by
  have hδ : coboundary F V f = 0 := coboundary_eq_zero_of_mem_cocycles hf
  have hzero : coneFace F V a (coboundary F V f) = 0 := by
    rw [hδ]
    exact (coneFaceₗ F V a).map_zero
  rw [← coboundary_coneFace_add_eq hmin ha hf.1, hzero, add_zero]

/-! ### `q` and `J` transport cocycles and coboundaries -/

theorem tailMapFace_zero (V : Finset ℕ) (a : ℕ) :
    tailMapFace F V a (0 : Finset ℕ → F) = 0 := (tailMapFaceₗ F V a).map_zero

theorem inclFace_zero (V : Finset ℕ) (a : ℕ) :
    inclFace F V a (0 : Finset ℕ → F) = 0 := (inclFaceₗ F V a).map_zero

theorem coneFace_zero (V : Finset ℕ) (a : ℕ) :
    coneFace F V a (0 : Finset ℕ → F) = 0 := (coneFaceₗ F V a).map_zero

theorem coboundary_zero (V : Finset ℕ) : coboundary F V (0 : Finset ℕ → F) = 0 :=
  (coboundaryₗ F V).map_zero

theorem tailMapFace_mem_cocycles {V : Finset ℕ} {a j : ℕ} (ha : a ∈ V) (ha1 : a + 1 ∈ V)
    {f : Finset ℕ → F} (hf : f ∈ cocycles F V (j + 1)) :
    tailMapFace F V a f ∈ cocycles F (tailVerts V a) j := by
  refine ⟨tailMapFace_mem_supported hf.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show coboundary F (tailVerts V a) (tailMapFace F V a f) = 0
  have h := tailMapFace_coboundary_eq ha ha1 f
  rw [coboundary_eq_zero_of_mem_cocycles hf, tailMapFace_zero] at h
  exact neg_eq_zero.mp h.symm

theorem inclFace_mem_cocycles {V : Finset ℕ} {a j : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    {g : Finset ℕ → F} (hg : g ∈ cocycles F (tailVerts V a) j) :
    inclFace F V a g ∈ cocycles F V (j + 1) := by
  refine ⟨inclFace_mem_supported hg.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show coboundary F V (inclFace F V a g) = 0
  have h := coboundary_inclFace_eq hmin g
  rw [coboundary_eq_zero_of_mem_cocycles hg, inclFace_zero, neg_zero] at h
  exact h

theorem tailMapFace_mem_coboundaries {V : Finset ℕ} {a j : ℕ} (ha : a ∈ V) (ha1 : a + 1 ∈ V)
    {f : Finset ℕ → F} (hf : f ∈ coboundaries F V (j + 1)) :
    tailMapFace F V a f ∈ coboundaries F (tailVerts V a) j := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hval : tailMapFace F V a ((coboundaryₗ F V) h)
      = - coboundary F (tailVerts V a) (tailMapFace F V a h) :=
    tailMapFace_coboundary_eq ha ha1 h
  match j with
  | 0 =>
    have hzero : tailMapFace F V a h = 0 := by
      funext τ
      show tailMapFace F V a h τ = 0
      by_cases hτ : IsFace (tailVerts V a) τ
      · rw [tailMapFace_of_face hτ, tailMap,
          hh _ (Or.inl (by
            rw [Finset.card_insert_of_notMem hτ.notMem_succ]
            omega)),
          hh _ (Or.inl (by
            rw [Finset.card_insert_of_notMem hτ.notMem_self]
            omega)), sub_zero]
      · rw [tailMapFace_of_not_face hτ]
    rw [hval, hzero, coboundary_zero, neg_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    rw [hval]
    refine Submodule.neg_mem _ ⟨tailMapFace F V a h, ?_, rfl⟩
    exact tailMapFace_mem_supported hh

theorem inclFace_mem_coboundaries {V : Finset ℕ} {a j : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    {g : Finset ℕ → F} (hg : g ∈ coboundaries F (tailVerts V a) j) :
    inclFace F V a g ∈ coboundaries F V (j + 1) := by
  match j with
  | 0 =>
    have hgb : g ∈ (⊥ : Submodule F (Finset ℕ → F)) := hg
    have hg0 : g = 0 := (Submodule.mem_bot F).mp hgb
    rw [hg0, inclFace_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    obtain ⟨h, hh, rfl⟩ := hg
    have hval : inclFace F V a ((coboundaryₗ F (tailVerts V a)) h)
        = - coboundary F V (inclFace F V a h) := by
      have hj := coboundary_inclFace_eq hmin h
      show inclFace F V a (coboundary F (tailVerts V a) h)
        = - coboundary F V (inclFace F V a h)
      rw [hj]
      ring
    rw [hval]
    refine Submodule.neg_mem _ ⟨inclFace F V a h, ?_, rfl⟩
    exact inclFace_mem_supported hh

/-! ### The cohomology isomorphism with a shift of one in occupation degree -/

/-- The tail contraction restricted to cocycles. -/
def tailMapCocycles (F : Type*) [CommRing F] (V : Finset ℕ) (a j : ℕ) (ha : a ∈ V)
    (ha1 : a + 1 ∈ V) : cocycles F V (j + 1) →ₗ[F] cocycles F (tailVerts V a) j :=
  LinearMap.restrict (tailMapFaceₗ F V a)
    (fun _ hx => tailMapFace_mem_cocycles ha ha1 hx)

/-- The tail inclusion restricted to cocycles. -/
def inclCocycles (F : Type*) [CommRing F] (V : Finset ℕ) (a j : ℕ)
    (hmin : ∀ v ∈ V, a ≤ v) : cocycles F (tailVerts V a) j →ₗ[F] cocycles F V (j + 1) :=
  LinearMap.restrict (inclFaceₗ F V a) (fun _ hx => inclFace_mem_cocycles hmin hx)

/-- The induced map on reduced cohomology, lowering the occupation degree by one. -/
def tailMapCohomology (F : Type*) [CommRing F] (V : Finset ℕ) (a j : ℕ) (ha : a ∈ V)
    (ha1 : a + 1 ∈ V) : cohomology F V (j + 1) →ₗ[F] cohomology F (tailVerts V a) j :=
  Submodule.mapQ _ _ (tailMapCocycles F V a j ha ha1) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ coboundaries F V (j + 1) := hx
    show tailMapFace F V a (x : Finset ℕ → F) ∈ coboundaries F (tailVerts V a) j
    exact tailMapFace_mem_coboundaries ha ha1 hxv)

/-- The induced map on reduced cohomology, raising the occupation degree by one. -/
def inclCohomology (F : Type*) [CommRing F] (V : Finset ℕ) (a j : ℕ)
    (hmin : ∀ v ∈ V, a ≤ v) :
    cohomology F (tailVerts V a) j →ₗ[F] cohomology F V (j + 1) :=
  Submodule.mapQ _ _ (inclCocycles F V a j hmin) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ coboundaries F (tailVerts V a) j := hx
    show inclFace F V a (x : Finset ℕ → F) ∈ coboundaries F V (j + 1)
    exact inclFace_mem_coboundaries hmin hxv)

theorem tailMapCohomology_inclCohomology {V : Finset ℕ} {a j : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (ha : a ∈ V) (ha1 : a + 1 ∈ V) (y : cohomology F (tailVerts V a) j) :
    tailMapCohomology F V a j ha ha1 (inclCohomology F V a j hmin y) = y := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [inclCohomology, Submodule.mapQ_apply, tailMapCohomology, Submodule.mapQ_apply]
  refine congrArg _ (Subtype.ext ?_)
  show tailMapFace F V a (inclFace F V a g.val) = g.val
  exact tailMapFace_inclFace_eq ha ha1 g.property.1

theorem inclCohomology_tailMapCohomology {V : Finset ℕ} {a j : ℕ} (hmin : ∀ v ∈ V, a ≤ v)
    (ha : a ∈ V) (ha1 : a + 1 ∈ V) (x : cohomology F V (j + 1)) :
    inclCohomology F V a j hmin (tailMapCohomology F V a j ha ha1 x) = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [tailMapCohomology, Submodule.mapQ_apply, inclCohomology, Submodule.mapQ_apply,
    Submodule.Quotient.eq]
  show (inclFace F V a (tailMapFace F V a f.val) : Finset ℕ → F) - f.val
    ∈ coboundaries F V (j + 1)
  have hkey := cocycles_sub_inclFace_tailMapFace hmin ha f.property
  have hsub : (inclFace F V a (tailMapFace F V a f.val) : Finset ℕ → F) - f.val
      = - coboundary F V (coneFace F V a f.val) := by
    rw [← hkey]
    ring
  rw [hsub]
  exact Submodule.neg_mem _
    ⟨coneFace F V a f.val, coneFace_mem_supported f.property.1, rfl⟩

/-- **The leaf reduction.** If `a` is the least vertex of `V` and `a + 1 ∈ V`, the tail
contraction and the tail inclusion are inverse isomorphisms of reduced cohomology, with a shift
of one in occupation degree, onto the complex with the closed neighbourhood of `a + 1` deleted. -/
def cohomologyEquiv (F : Type*) [CommRing F] (V : Finset ℕ) (a j : ℕ) (hL : IsLeaf V a) :
    cohomology F V (j + 1) ≃ₗ[F] cohomology F (tailVerts V a) j :=
  LinearEquiv.ofLinear (tailMapCohomology F V a j hL.mem hL.memSucc)
    (inclCohomology F V a j hL.min)
    (LinearMap.ext fun y => tailMapCohomology_inclCohomology hL.min hL.mem hL.memSucc y)
    (LinearMap.ext fun x => inclCohomology_tailMapCohomology hL.min hL.mem hL.memSucc x)

end
end VertexIndependence
end GaloisForLFunctions.HTGeometry
