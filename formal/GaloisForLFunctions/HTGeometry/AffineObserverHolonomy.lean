import GaloisForLFunctions.HTGeometry.ConstraintLaplacian
import GaloisForLFunctions.HTGeometry.NestedConvexCapacity

/-!
# Affine observer holonomy and the global-section field equation

Observer fibres `H v` are compared along oriented edges by unitary transports `U e` with
translation defects `b e`; an **exact global presentation** is a family `x` with
`x (tgt e) = U e (x (src e)) + b e` for every edge.

A rooted spanning-tree gauge `(A, a)` reduces the tree equations to `x v = A v (x o) + a v`, so
exact global presentations are exactly the root values solving the affine chord equations

`x − Hol e x = c e`,

whose least-squares normal operator `Δ_hol = D* D` and source current `J_src = D* c` give the
**observer field equation** `Δ_hol x = J_src` together with the separate exactness condition
`D x = c`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## Rooted tree gauges -/

/-- A rooted spanning-tree gauge for affine observer transport: a parent function with a
well-founded rank, the unitary transports and translation defects along tree edges, and the
resulting based transports `A v` and accumulated defects `a v`. -/
structure TreeGauge (𝕜 : Type*) [RCLike 𝕜] {V : Type*} (H : V → Type*)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace 𝕜 (H v)] (o : V) where
  /-- The tree parent of a vertex. -/
  parent : V → V
  /-- A rank witnessing well-founded descent to the root. -/
  rank : V → ℕ
  /-- The root is its own parent. -/
  parent_root : parent o = o
  /-- Every non-root vertex has a parent of strictly smaller rank. -/
  rank_lt : ∀ v, v ≠ o → rank (parent v) < rank v
  /-- The unitary transport along the tree edge into `v`. -/
  U : (v : V) → (H (parent v) ≃ₗᵢ[𝕜] H v)
  /-- The translation defect of the tree edge into `v`. -/
  b : (v : V) → H v
  /-- The based transport from the root fibre. -/
  A : (v : V) → (H o ≃ₗᵢ[𝕜] H v)
  /-- The accumulated affine defect at `v`. -/
  a : (v : V) → H v
  /-- The based transport is the identity at the root. -/
  A_root : ∀ z, A o z = z
  /-- The accumulated defect vanishes at the root. -/
  a_root : a o = 0
  /-- The based transport is built by tree composition. -/
  A_step : ∀ v, v ≠ o → ∀ z, A v z = U v (A (parent v) z)
  /-- The accumulated defect is built by affine tree composition. -/
  a_step : ∀ v, v ≠ o → a v = U v (a (parent v)) + b v

namespace TreeGauge

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} {H : V → Type*}
  [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace 𝕜 (H v)] {o : V}
  (T : TreeGauge 𝕜 H o)

/-- The tree-edge equations of an observer family. -/
def IsTreeExact (x : ∀ v, H v) : Prop :=
  ∀ v, v ≠ o → x v = T.U v (x (T.parent v)) + T.b v

/-- The based form of a family. -/
def IsBased (x : ∀ v, H v) : Prop :=
  ∀ v, x v = T.A v (x o) + T.a v

/-- **The spanning-tree reduction.**  A family satisfies all tree-edge equations exactly when it
is the based extension of its root value. -/
theorem isTreeExact_iff_isBased (x : ∀ v, H v) : T.IsTreeExact x ↔ T.IsBased x := by
  constructor
  · intro htree v
    induction hv : T.rank v using Nat.strong_induction_on generalizing v with
    | _ n ih =>
      by_cases hvo : v = o
      · subst hvo
        rw [T.A_root, T.a_root, add_zero]
      · have hpar : x (T.parent v) = T.A (T.parent v) (x o) + T.a (T.parent v) := by
          refine ih (T.rank (T.parent v)) ?_ (T.parent v) rfl
          rw [← hv]
          exact T.rank_lt v hvo
        rw [htree v hvo, hpar, map_add, ← T.A_step v hvo, T.a_step v hvo]
        abel
  · intro hbased v hvo
    rw [hbased v, hbased (T.parent v), map_add, ← T.A_step v hvo, T.a_step v hvo]
    abel

end TreeGauge

/-! ## Chords, holonomy and the source current -/

/-- Affine chord data over a rooted tree gauge. -/
structure ChordData (𝕜 : Type*) [RCLike 𝕜] {V : Type*} (H : V → Type*)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace 𝕜 (H v)] (C : Type*) where
  /-- The source vertex of a chord. -/
  src : C → V
  /-- The target vertex of a chord. -/
  tgt : C → V
  /-- The unitary comparison along a chord. -/
  U : (e : C) → (H (src e) ≃ₗᵢ[𝕜] H (tgt e))
  /-- The translation defect of a chord. -/
  b : (e : C) → H (tgt e)

namespace ChordData

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} {H : V → Type*}
  [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace 𝕜 (H v)] {o : V} {C : Type*}
  (T : TreeGauge 𝕜 H o) (K : ChordData 𝕜 H C)

/-- The chord equations of an observer family. -/
def IsChordExact (x : ∀ v, H v) : Prop :=
  ∀ e : C, x (K.tgt e) = K.U e (x (K.src e)) + K.b e

/-- The based linear holonomy of a chord. -/
noncomputable def holonomy (e : C) : H o ≃ₗᵢ[𝕜] H o :=
  ((T.A (K.src e)).trans (K.U e)).trans (T.A (K.tgt e)).symm

/-- The affine source current of a chord. -/
noncomputable def current (e : C) : H o :=
  (T.A (K.tgt e)).symm (K.U e (T.a (K.src e)) + K.b e - T.a (K.tgt e))

/-- **Theorem 3.1.**  For a based family, a chord equation is exactly the affine holonomy fixed
equation at the root. -/
theorem chord_eq_iff_holonomy {x : ∀ v, H v} (hbased : T.IsBased x) (e : C) :
    x (K.tgt e) = K.U e (x (K.src e)) + K.b e
      ↔ x o - holonomy T K e (x o) = current T K e := by
  set At := T.A (K.tgt e) with hAt
  set As := T.A (K.src e) with hAs
  have hsrc : x (K.src e) = As (x o) + T.a (K.src e) := hbased (K.src e)
  have htgt : x (K.tgt e) = At (x o) + T.a (K.tgt e) := hbased (K.tgt e)
  have hhol : holonomy T K e (x o) = At.symm (K.U e (As (x o))) := rfl
  have hcur : current T K e
      = At.symm (K.U e (T.a (K.src e)) + K.b e - T.a (K.tgt e)) := rfl
  have hcur' : current T K e
      = At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e) - At.symm (T.a (K.tgt e)) := by
    rw [hcur, map_sub, map_add]
  constructor
  · intro heq
    rw [hsrc, htgt] at heq
    have h1 : At.symm (At (x o) + T.a (K.tgt e)) = x o + At.symm (T.a (K.tgt e)) := by
      rw [map_add, LinearIsometryEquiv.symm_apply_apply]
    have h2 : At.symm (K.U e (As (x o) + T.a (K.src e)) + K.b e)
        = At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e) := by
      rw [map_add, map_add, map_add]
    have happ : x o + At.symm (T.a (K.tgt e))
        = At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
          + At.symm (K.b e) := by
      rw [← h1, ← h2, heq]
    rw [hhol, hcur']
    have h0 : (x o + At.symm (T.a (K.tgt e)))
        - (At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
          + At.symm (K.b e)) = 0 := by
      rw [happ]; abel
    have key : (x o - At.symm (K.U e (As (x o))))
        - (At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e)
          - At.symm (T.a (K.tgt e))) = 0 := by
      calc (x o - At.symm (K.U e (As (x o))))
            - (At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e)
              - At.symm (T.a (K.tgt e)))
          = (x o + At.symm (T.a (K.tgt e)))
            - (At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
              + At.symm (K.b e)) := by abel
        _ = 0 := h0
    exact sub_eq_zero.mp key
  · intro heq
    rw [hhol, hcur'] at heq
    have h0 : (x o - At.symm (K.U e (As (x o))))
        - (At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e)
          - At.symm (T.a (K.tgt e))) = 0 := by
      rw [heq]; abel
    have happ : x o + At.symm (T.a (K.tgt e))
        = At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
          + At.symm (K.b e) := by
      have hcalc : (x o + At.symm (T.a (K.tgt e)))
          - (At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
            + At.symm (K.b e)) = 0 := by
        calc (x o + At.symm (T.a (K.tgt e)))
              - (At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
                + At.symm (K.b e))
            = (x o - At.symm (K.U e (As (x o))))
              - (At.symm (K.U e (T.a (K.src e))) + At.symm (K.b e)
                - At.symm (T.a (K.tgt e))) := by abel
          _ = 0 := h0
      exact sub_eq_zero.mp hcalc
    have hAt' : At (x o + At.symm (T.a (K.tgt e))) = At (x o) + T.a (K.tgt e) := by
      rw [map_add, LinearIsometryEquiv.apply_symm_apply]
    have hRHS : At (At.symm (K.U e (As (x o))) + At.symm (K.U e (T.a (K.src e)))
        + At.symm (K.b e))
        = K.U e (As (x o)) + K.U e (T.a (K.src e)) + K.b e := by
      rw [map_add, map_add, LinearIsometryEquiv.apply_symm_apply,
        LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    have hfinal : At (x o) + T.a (K.tgt e)
        = K.U e (As (x o)) + K.U e (T.a (K.src e)) + K.b e := by
      rw [← hAt', ← hRHS, happ]
    rw [hsrc, htgt, map_add]
    exact hfinal

/-- **Theorem 3.1.**  Exact global presentations correspond exactly to the root values solving all
affine chord equations. -/
theorem isExact_iff (x : ∀ v, H v) :
    (T.IsTreeExact x ∧ K.IsChordExact x)
      ↔ (T.IsBased x ∧ ∀ e : C, x o - holonomy T K e (x o) = current T K e) := by
  constructor
  · rintro ⟨htree, hchord⟩
    have hbased := (T.isTreeExact_iff_isBased x).mp htree
    exact ⟨hbased, fun e => (chord_eq_iff_holonomy T K hbased e).mp (hchord e)⟩
  · rintro ⟨hbased, hchord⟩
    refine ⟨(T.isTreeExact_iff_isBased x).mpr hbased, fun e => ?_⟩
    exact (chord_eq_iff_holonomy T K hbased e).mpr (hchord e)

/-- With vanishing tree defects the accumulated defect vanishes. -/
theorem treeGauge_a_eq_zero (hb : ∀ v, T.b v = 0) (v : V) : T.a v = 0 := by
  induction hv : T.rank v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hvo : v = o
    · subst hvo
      exact T.a_root
    · have hpar : T.a (T.parent v) = 0 := by
        refine ih (T.rank (T.parent v)) ?_ (T.parent v) rfl
        rw [← hv]
        exact T.rank_lt v hvo
      rw [T.a_step v hvo, hb v, add_zero, hpar, map_zero]

/-- In the linear case the exact global presentations are the joint holonomy fixed points. -/
theorem isExact_linear_iff (hb : ∀ v, T.b v = 0) (hbc : ∀ e : C, K.b e = 0)
    (x : ∀ v, H v) :
    (T.IsTreeExact x ∧ K.IsChordExact x)
      ↔ (T.IsBased x ∧ ∀ e : C, holonomy T K e (x o) = x o) := by
  have hzero : ∀ v, T.a v = 0 := treeGauge_a_eq_zero T hb
  rw [isExact_iff]
  refine and_congr Iff.rfl (forall_congr' fun e => ?_)
  have hcur : current T K e = 0 := by
    rw [current, hzero (K.src e), hbc e, hzero (K.tgt e)]
    simp
  rw [hcur, sub_eq_zero, eq_comm]

end ChordData

end GaloisForLFunctions.HTGeometry
