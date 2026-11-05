import DifferentialGeometry.Topology.Simplex.InactiveFaceContraction
import DifferentialGeometry.Topology.Simplex.Reindex
import DifferentialGeometry.Topology.Simplex.SupportFace
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.LocallyFinite

/-!
# Compatible contractions on finite simplex boundaries

The faces containing a chosen vertex contract linearly to that vertex.
Homotopy extension carries this contraction over the opposite face.
Finite closed covers glue these compatible local homotopies.
-/

noncomputable section

open ContinuousMap Set
open DifferentialGeometry.Simplex

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- Compatible continuous maps on a finite closed cover glue continuously. -/
def finiteClosedCoverMap {X Y J : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite J]
    (S : J → Set X) (hclosed : ∀ j, IsClosed (S j)) (hcover : ⋃ j, S j = univ)
    (f : ∀ j, C(S j, Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    C(X, Y) where
  toFun := Set.liftCover S (fun j => f j) hcompat hcover
  continuous_toFun := by
    apply (locallyFinite_of_finite S).continuous hcover hclosed
    intro j
    rw [continuousOn_iff_continuous_restrict]
    simpa +unfoldPartialApp only [Set.restrict, Set.liftCover_coe] using (f j).continuous

theorem finiteClosedCoverMap_apply {X Y J : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite J]
    (S : J → Set X) (hclosed : ∀ j, IsClosed (S j)) (hcover : ⋃ j, S j = univ)
    (f : ∀ j, C(S j, Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (j : J) (x : S j) : finiteClosedCoverMap S hclosed hcover f hcompat x = f j x := by
  simp only [finiteClosedCoverMap, ContinuousMap.coe_mk, Set.liftCover_coe]

/-- Relabeling simplex vertices restricts to a homeomorphism of boundaries. -/
def boundaryReindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    boundary ι ≃ₜ boundary κ where
  toFun x := ⟨reindexHomeomorph e x.val, (reindexHomeomorph_mem_boundary e x.val).mpr x.property⟩
  invFun y := ⟨(reindexHomeomorph e).symm y.val, by
    apply (reindexHomeomorph_mem_boundary e _).mp
    simpa only [Homeomorph.apply_symm_apply] using y.property⟩
  left_inv x := Subtype.ext ((reindexHomeomorph e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((reindexHomeomorph e).apply_symm_apply y.val)
  continuous_toFun := ((reindexHomeomorph e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexHomeomorph e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem reindex_vertexContraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (a : ι)
    (t : unitInterval) (q : stdSimplex ℝ ι) :
    reindexHomeomorph e (vertexContraction a (t, q)) =
      vertexContraction (e a) (t, reindexHomeomorph e q) := by
  apply Subtype.ext
  funext j
  simp only [reindexHomeomorph_apply, vertexContraction_apply]
  simp only [e.eq_symm_apply]

private theorem exists_boundary_contraction_of_reindex {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι) (n : ℕ) (e : ι ≃ Fin (n + 3)) (he : e a = 0) :
    ∃ K : C(unitInterval × boundary ι, boundary ι),
      (∀ p, K (0, p) = p) ∧
      ∀ (t : unitInterval) (p : boundary ι),
        (∃ j : ι, j ≠ a ∧ p.val.val j = 0) →
          (K (t, p)).val = vertexContraction a (t, p.val) := by
  obtain ⟨L, hL0, hLA⟩ := exists_boundary_homotopy_contracting_faces_through_zero n
  let h := boundaryReindex e
  let K : C(unitInterval × boundary ι, boundary ι) :=
    (⟨h.symm, h.symm.continuous⟩ : C(_, _)).comp
      (L.comp (ContinuousMap.prodMap (ContinuousMap.id _) ⟨h, h.continuous⟩))
  refine ⟨K, ?_, ?_⟩
  · intro p
    change h.symm (L (0, h p)) = p
    rw [hL0, Homeomorph.symm_apply_apply]
  · intro t p hp
    obtain ⟨j, hja, hj⟩ := hp
    have hactive : ∃ l : Fin (n + 3), l ≠ 0 ∧ (h p).val.val l = 0 := by
      refine ⟨e j, ?_, ?_⟩
      · intro hzero
        exact hja (e.injective (hzero.trans he.symm))
      · change p.val.val (e.symm (e j)) = 0
        simpa only [e.symm_apply_apply] using hj
    apply (reindexHomeomorph e).injective
    have hcancel : reindexHomeomorph e (K (t, p)).val = (L (t, h p)).val :=
      (reindexHomeomorph e).apply_symm_apply _
    rw [hcancel, hLA t (h p) hactive, reindex_vertexContraction, he]
    rfl

private theorem finTwo_inactive_eq_vertex (p : boundary (Fin 2))
    (hp : ∃ j : Fin 2, j ≠ 0 ∧ p.val.val j = 0) :
    p.val = stdSimplex.vertex (S := ℝ) 0 := by
  obtain ⟨j, hj, hz⟩ := hp
  have hj1 : j = 1 := by fin_cases j <;> simp_all
  subst j
  have hs := p.val.property.2
  simp only [Fin.sum_univ_two, hz, add_zero] at hs
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [hs, hz]

private theorem exists_boundary_contraction_of_two {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι) (e : ι ≃ Fin 2) (he : e a = 0) :
    ∃ K : C(unitInterval × boundary ι, boundary ι),
      (∀ p, K (0, p) = p) ∧
      ∀ (t : unitInterval) (p : boundary ι),
        (∃ j : ι, j ≠ a ∧ p.val.val j = 0) →
          (K (t, p)).val = vertexContraction a (t, p.val) := by
  refine ⟨⟨Prod.snd, continuous_snd⟩, fun _ => rfl, ?_⟩
  intro t p hp
  obtain ⟨j, hja, hj⟩ := hp
  have hactive : ∃ l : Fin 2, l ≠ 0 ∧ (boundaryReindex e p).val.val l = 0 := by
    refine ⟨e j, ?_, ?_⟩
    · intro hzero
      exact hja (e.injective (hzero.trans he.symm))
    · change p.val.val (e.symm (e j)) = 0
      simpa only [e.symm_apply_apply] using hj
  apply (reindexHomeomorph e).injective
  change reindexHomeomorph e p.val = reindexHomeomorph e (vertexContraction a (t, p.val))
  have hpv : reindexHomeomorph e p.val = stdSimplex.vertex (S := ℝ) 0 :=
    finTwo_inactive_eq_vertex _ hactive
  rw [reindex_vertexContraction, he, hpv, vertexContraction_vertex]

/-- On every nonempty-dimensional simplex boundary, all faces through a fixed
vertex contract by the same linear homotopy. The whole boundary carries an
extension of this contraction. -/
theorem exists_boundary_contraction_at_vertex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (hcard : 2 ≤ Fintype.card ι) :
    ∃ K : C(unitInterval × boundary ι, boundary ι),
      (∀ p, K (0, p) = p) ∧
      ∀ (t : unitInterval) (p : boundary ι),
        (∃ j : ι, j ≠ a ∧ p.val.val j = 0) →
          (K (t, p)).val = vertexContraction a (t, p.val) := by
  by_cases hc : Fintype.card ι = 2
  · let e₀ : ι ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using hc)
    let e : ι ≃ Fin 2 := e₀.trans (Equiv.swap (e₀ a) 0)
    exact exists_boundary_contraction_of_two a e (by simp [e])
  · have h3 : 3 ≤ Fintype.card ι := by omega
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 3 := ⟨Fintype.card ι - 3, by omega⟩
    let e₀ : ι ≃ Fin (n + 3) := Fintype.equivOfCardEq (by simpa using hn)
    let e : ι ≃ Fin (n + 3) := e₀.trans (Equiv.swap (e₀ a) 0)
    exact exists_boundary_contraction_of_reindex a n e (by simp [e])

private def bouquetBase {J : Type*} {X : J → Type*} (b : ∀ j, X j) :
    Unit ⊕ (Σ j, X j) → Prop
  | .inl _ => True
  | .inr ⟨j, x⟩ => x = b j

private def bouquetSetoid {J : Type*} (X : J → Type*) (b : ∀ j, X j) :
    Setoid (Unit ⊕ (Σ j, X j)) where
  r x y := x = y ∨ bouquetBase b x ∧ bouquetBase b y
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · exact Or.inr ⟨hxy.1, hyz.2⟩

/-- The wedge of a family of pointed spaces, including the one-point empty wedge. -/
def BasedBouquet {J : Type*} (X : J → Type*) (b : ∀ j, X j) :=
  Quotient (bouquetSetoid X b)

instance {J : Type*} (X : J → Type*) [∀ j, TopologicalSpace (X j)] (b : ∀ j, X j) :
    TopologicalSpace (BasedBouquet X b) :=
  inferInstanceAs (TopologicalSpace (Quotient (bouquetSetoid X b)))

def bouquetPoint {J : Type*} {X : J → Type*} (b : ∀ j, X j) : BasedBouquet X b :=
  Quotient.mk _ (Sum.inl ())

def bouquetInclusion {J : Type*} {X : J → Type*} [∀ j, TopologicalSpace (X j)]
    (b : ∀ j, X j) (j : J) : C(X j, BasedBouquet X b) where
  toFun x := Quotient.mk _ (Sum.inr ⟨j, x⟩)
  continuous_toFun := continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)

theorem bouquetInclusion_base {J : Type*} {X : J → Type*} [∀ j, TopologicalSpace (X j)]
    (b : ∀ j, X j) (j : J) : bouquetInclusion b j (b j) = bouquetPoint b := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, trivial⟩

/-- A family of maps agreeing at their basepoints descends to the wedge. -/
def bouquetDesc {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (f : ∀ j, C(X j, Y)) (y : Y) (hf : ∀ j, f j (b j) = y) :
    C(BasedBouquet X b, Y) := by
  let F : Unit ⊕ (Σ j, X j) → Y := Sum.elim (fun _ => y) (fun z => f z.1 z.2)
  have hbase : ∀ z, bouquetBase b z → F z = y := by
    rintro (u | ⟨j, x⟩) hz
    · rfl
    · change x = b j at hz
      subst x
      exact hf j
  have hF : ∀ x z, (bouquetSetoid X b).r x z → F x = F z := by
    intro x z h
    rcases h with rfl | h
    · rfl
    · exact (hbase x h.1).trans (hbase z h.2).symm
  refine ⟨Quotient.lift F hF, ?_⟩
  exact continuous_quot_lift _ (continuous_const.sumElim (continuous_sigma fun j => (f j).continuous))

theorem bouquetDesc_point {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (f : ∀ j, C(X j, Y)) (y : Y) (hf : ∀ j, f j (b j) = y) :
    bouquetDesc b f y hf (bouquetPoint b) = y := rfl

theorem bouquetDesc_inclusion {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (f : ∀ j, C(X j, Y)) (y : Y) (hf : ∀ j, f j (b j) = y)
    (j : J) (x : X j) : bouquetDesc b f y hf (bouquetInclusion b j x) = f j x := rfl

theorem bouquet_induction {J : Type*} {X : J → Type*} [∀ j, TopologicalSpace (X j)]
    (b : ∀ j, X j) {P : BasedBouquet X b → Prop}
    (hp : P (bouquetPoint b)) (hi : ∀ j x, P (bouquetInclusion b j x)) : ∀ z, P z := by
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    rcases z with u | ⟨j, x⟩
    · cases u
      exact hp
    · exact hi j x

/-- Compatible pointed homotopies descend continuously. Currying avoids any
assumption that a product of quotient maps is again a quotient map. -/
def bouquetHomotopyMap {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (H : ∀ j, C(unitInterval × X j, Y)) (p : C(unitInterval, Y))
    (hH : ∀ j t, H j (t, b j) = p t) : C(unitInterval × BasedBouquet X b, Y) :=
  let F j : C(X j, C(unitInterval, Y)) := ((H j).comp ContinuousMap.prodSwap).curry
  let hF : ∀ j, F j (b j) = p := fun j => ContinuousMap.ext (hH j)
  (bouquetDesc b F p hF).uncurry.comp ContinuousMap.prodSwap

theorem bouquetHomotopyMap_inclusion {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (H : ∀ j, C(unitInterval × X j, Y)) (p : C(unitInterval, Y))
    (hH : ∀ j t, H j (t, b j) = p t) (j : J) (t : unitInterval) (x : X j) :
    bouquetHomotopyMap b H p hH (t, bouquetInclusion b j x) = H j (t, x) := rfl

theorem bouquetHomotopyMap_point {J Y : Type*} {X : J → Type*}
    [∀ j, TopologicalSpace (X j)] [TopologicalSpace Y]
    (b : ∀ j, X j) (H : ∀ j, C(unitInterval × X j, Y)) (p : C(unitInterval, Y))
    (hH : ∀ j t, H j (t, b j) = p t) (t : unitInterval) :
    bouquetHomotopyMap b H p hH (t, bouquetPoint b) = p t := rfl

#print axioms exists_boundary_contraction_at_vertex
#print axioms bouquetHomotopyMap

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
