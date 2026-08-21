import GaloisForLFunctions.HTGeometry.SubdivisionDiameter
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The simplices occurring in a subdivided chain

Two predicates track the geometry of the simplices actually occurring in a chain: that all their
vertices lie in a prescribed set, and that their diameters are bounded.  Both are stable under the
operations building the subdivision — the boundary only omits vertices, and the cone adds one new
vertex — so they propagate through the recursion `Sd v = b(v) ∗ Sd (∂ v)`.

Combined with the barycentric shrinking estimate this is what bounds the mesh of an iterated
subdivision.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

universe u

variable (R : Type u) [CommRing R] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every simplex occurring in the chain has all its vertices in `S`. -/
def VerticesIn (S : Set E) {n : ℕ} (c : (Fin (n + 1) → E) →₀ R) : Prop :=
  ∀ w ∈ c.support, ∀ i, w i ∈ S

/-- Every simplex occurring in the chain has diameter at most `D`. -/
def DiamLe (D : ℝ) {n : ℕ} (c : (Fin (n + 1) → E) →₀ R) : Prop :=
  ∀ w ∈ c.support, ∀ i j, ‖w i - w j‖ ≤ D

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem VerticesIn.mono {S T : Set E} (hST : S ⊆ T) {n : ℕ} {c : (Fin (n + 1) → E) →₀ R}
    (h : VerticesIn R S c) : VerticesIn R T c :=
  fun w hw i => hST (h w hw i)

omit [NormedSpace ℝ E] in
theorem DiamLe.mono {D D' : ℝ} (hDD : D ≤ D') {n : ℕ} {c : (Fin (n + 1) → E) →₀ R}
    (h : DiamLe R D c) : DiamLe R D' c :=
  fun w hw i j => le_trans (h w hw i j) hDD

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The simplices of a cone are cones on the simplices of the original chain. -/
theorem support_affCone_subset (b : E) (n : ℕ) (c : (Fin (n + 1) → E) →₀ R)
    {w : Fin (n + 2) → E} (hw : w ∈ (affCone R E b n c).support) :
    ∃ w' ∈ c.support, w = Fin.cons b w' := by
  by_contra hcon
  push Not at hcon
  rw [Finsupp.mem_support_iff] at hw
  refine hw ?_
  show Finsupp.mapDomain
    (fun u : Fin (n + 1) → E => (Fin.cons b u : Fin (n + 2) → E)) c w = 0
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  exact Finsupp.single_eq_of_ne (fun heq => hcon a ha heq)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Coning preserves the property that all vertices lie in a set, provided the apex does. -/
theorem VerticesIn.affCone {S : Set E} {b : E} (hb : b ∈ S) {n : ℕ}
    {c : (Fin (n + 1) → E) →₀ R} (h : VerticesIn R S c) :
    VerticesIn R S (affCone R E b n c) := by
  intro w hw i
  obtain ⟨w', hw', rfl⟩ := support_affCone_subset R b n c hw
  refine Fin.cases ?_ ?_ i
  · simpa using hb
  · intro m
    simpa using h w' hw' m

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem affBd_single {n : ℕ} (v : Fin (n + 2) → E) :
    affBd R E n (Finsupp.single v (1 : R))
      = ∑ i : Fin (n + 2), Finsupp.single (v ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)) :=
  d_single R E v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The simplices of a boundary are the faces. -/
theorem support_affBd_single_subset {n : ℕ} (v : Fin (n + 2) → E)
    {w : Fin (n + 1) → E} (hw : w ∈ (affBd R E n (Finsupp.single v (1 : R))).support) :
    ∃ i : Fin (n + 2), w = v ∘ i.succAbove := by
  rw [affBd_single] at hw
  by_contra hcon
  push Not at hcon
  rw [Finsupp.mem_support_iff] at hw
  refine hw ?_
  rw [Finset.sum_apply']
  refine Finset.sum_eq_zero fun i _ => ?_
  exact Finsupp.single_eq_of_ne (fun heq => hcon i heq)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The support of a linear image of a chain is contained in the union of the supports of the
images of its simplices. -/
theorem support_linear_apply_subset {α : Type*} {β : Type*} (L : (α →₀ R) →ₗ[R] (β →₀ R))
    (c : α →₀ R) {b : β} (hb : b ∈ (L c).support) :
    ∃ a ∈ c.support, b ∈ (L (Finsupp.single a (1 : R))).support := by
  by_contra hcon
  push Not at hcon
  rw [Finsupp.mem_support_iff] at hb
  refine hb ?_
  have hc : c = ∑ a ∈ c.support, Finsupp.single a (c a) := by
    rw [← Finsupp.sum, Finsupp.sum_single]
  have hL : L c = ∑ a ∈ c.support, (c a) • L (Finsupp.single a (1 : R)) := by
    conv_lhs => rw [hc]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Finsupp.single a (c a) : α →₀ R) = (c a) • Finsupp.single a (1 : R) by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul]
  rw [hL, Finset.sum_apply']
  refine Finset.sum_eq_zero fun a ha => ?_
  have hzero : (L (Finsupp.single a (1 : R))) b = 0 := by
    by_contra hne
    exact hcon a ha (Finsupp.mem_support_iff.mpr hne)
  rw [Finsupp.smul_apply, hzero, smul_zero]

/-- The barycenter is within `n/(n+1) · D` of the whole convex hull of the vertices. -/
theorem norm_bary_sub_mem_hull_le {n : ℕ} {v : Fin (n + 1) → E} {D : ℝ}
    (h : ∀ i j, ‖v i - v j‖ ≤ D) {x : E} (hx : x ∈ convexHull ℝ (Set.range v)) :
    ‖bary E v - x‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  have hsub : convexHull ℝ (Set.range v)
      ⊆ Metric.closedBall (bary E v) (((n : ℝ) / ((n : ℝ) + 1)) * D) := by
    refine convexHull_min ?_ (convex_closedBall _ _)
    rintro y ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    exact norm_bary_sub_vertex_le h i
  have hmem := hsub hx
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at hmem
  exact hmem

/-- The barycenter lies in the convex hull of the vertices. -/
theorem bary_mem_hull {n : ℕ} (v : Fin (n + 1) → E) :
    bary E v ∈ convexHull ℝ (Set.range v) := by
  have hconv : Convex ℝ (convexHull ℝ (Set.range v)) := convex_convexHull ℝ _
  have hmem : ∀ i : Fin (n + 1), v i ∈ convexHull ℝ (Set.range v) := fun i =>
    subset_convexHull ℝ _ ⟨i, rfl⟩
  have hw : ∀ i : Fin (n + 1), (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := fun _ => by positivity
  have hw1 : ∑ _i : Fin (n + 1), ((n : ℝ) + 1)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hres := Convex.sum_mem hconv (fun i _ => hw i) hw1 (fun i _ => hmem i)
  have hbary : bary E v = ∑ i : Fin (n + 1), ((n : ℝ) + 1)⁻¹ • v i := by
    rw [bary, Finset.smul_sum]
  rw [hbary]
  exact hres

/-- **The mesh estimate for barycentric subdivision.**  Every simplex occurring in `Sd v` has its
vertices in the convex hull of the vertices of `v`, and diameter at most `n/(n+1)` times the
diameter of `v`. -/
theorem sd_mesh : ∀ (n : ℕ) (v : Fin (n + 1) → E) (D : ℝ), (∀ i j, ‖v i - v j‖ ≤ D) →
    VerticesIn R (convexHull ℝ (Set.range v)) (affSd R E n (Finsupp.single v (1 : R)))
    ∧ DiamLe R (((n : ℝ) / ((n : ℝ) + 1)) * D)
        (affSd R E n (Finsupp.single v (1 : R))) := by
  intro n
  induction n with
  | zero =>
    intro v D h
    have hsd : affSd R E 0 (Finsupp.single v (1 : R)) = Finsupp.single v (1 : R) :=
      affSd_zero R E _
    refine ⟨fun w hw i => ?_, fun w hw i j => ?_⟩
    · rw [hsd] at hw
      have hwv : w = v := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
      rw [hwv]
      exact subset_convexHull ℝ _ ⟨i, rfl⟩
    · rw [hsd] at hw
      have hwv : w = v := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
      have hij : i = j := by
        have hi := i.isLt
        have hj := j.isLt
        exact Fin.ext (by omega)
      rw [hwv, hij]
      simp
  | succ n ih =>
    intro v D h
    have hD : 0 ≤ D := by simpa using h 0 0
    have hrec : affSd R E (n + 1) (Finsupp.single v (1 : R))
        = affCone R E (bary E v) n (affSd R E n (affBd R E n (Finsupp.single v (1 : R)))) :=
      affSd_single R E v
    set B := affBd R E n (Finsupp.single v (1 : R)) with hB

    have hinner : VerticesIn R (convexHull ℝ (Set.range v)) (affSd R E n B)
        ∧ DiamLe R (((n : ℝ) / ((n : ℝ) + 1)) * D) (affSd R E n B) := by
      constructor
      · intro w hw i
        obtain ⟨F, hF, hwF⟩ := support_linear_apply_subset R (affSd R E n) B hw
        obtain ⟨k, hFk⟩ := support_affBd_single_subset R v hF
        have hFbound : ∀ a b, ‖F a - F b‖ ≤ D := by
          intro a b
          rw [hFk]
          exact h _ _
        have hhull := (ih F D hFbound).1 w hwF i
        have hsubrange : Set.range F ⊆ Set.range v := by
          rw [hFk]
          rintro y ⟨a, rfl⟩
          exact ⟨_, rfl⟩
        exact convexHull_mono hsubrange hhull
      · intro w hw i j
        obtain ⟨F, hF, hwF⟩ := support_linear_apply_subset R (affSd R E n) B hw
        obtain ⟨k, hFk⟩ := support_affBd_single_subset R v hF
        have hFbound : ∀ a b, ‖F a - F b‖ ≤ D := by
          intro a b
          rw [hFk]
          exact h _ _
        exact (ih F D hFbound).2 w hwF i j
    have hmono : ((n : ℝ) / ((n : ℝ) + 1)) * D ≤ (((n : ℝ) + 1) / (((n : ℝ) + 1) + 1)) * D := by
      have h1 : (n : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / (((n : ℝ) + 1) + 1) := by
        rw [← sub_nonneg]
        have hid : ((n : ℝ) + 1) / (((n : ℝ) + 1) + 1) - (n : ℝ) / ((n : ℝ) + 1)
            = 1 / (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1)) := by
          field_simp
          ring
        rw [hid]
        positivity
      exact mul_le_mul_of_nonneg_right h1 hD
    refine ⟨?_, ?_⟩
    · rw [hrec]
      exact VerticesIn.affCone R (bary_mem_hull v) hinner.1
    · rw [hrec]
      intro w hw i j
      obtain ⟨w', hw', rfl⟩ := support_affCone_subset R (bary E v) n _ hw
      have hbary : ∀ m : Fin (n + 1),
          ‖bary E v - w' m‖ ≤ (((n : ℝ) + 1) / (((n : ℝ) + 1) + 1)) * D := by
        intro m
        have hx : w' m ∈ convexHull ℝ (Set.range v) := hinner.1 w' hw' m
        have hb := norm_bary_sub_mem_hull_le h hx
        push_cast at hb
        exact hb
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · have hcz : ((Fin.cons (bary E v) w' : Fin (n + 2) → E) 0) = bary E v := rfl
          rw [hcz, sub_self, norm_zero]
          positivity
        · intro m
          simpa using hbary m
      · intro m
        refine Fin.cases ?_ ?_ j
        · have := hbary m
          rw [← norm_neg] at this
          simpa using this
        · intro m'
          have := hinner.2 w' hw' m m'
          simpa using le_trans this hmono

/-- The mesh estimate for an arbitrary chain inside a convex set. -/
theorem sd_mesh_chain {n : ℕ} {S : Set E} (hS : Convex ℝ S) {D : ℝ}
    {c : (Fin (n + 1) → E) →₀ R} (hV : VerticesIn R S c) (hD : DiamLe R D c) :
    VerticesIn R S (affSd R E n c)
      ∧ DiamLe R (((n : ℝ) / ((n : ℝ) + 1)) * D) (affSd R E n c) := by
  constructor
  · intro w hw i
    obtain ⟨v, hv, hwv⟩ := support_linear_apply_subset R (affSd R E n) c hw
    have hhull := (sd_mesh R n v D (fun a b => hD v hv a b)).1 w hwv i
    have hrange : Set.range v ⊆ S := by
      rintro y ⟨a, rfl⟩
      exact hV v hv a
    exact convexHull_min hrange hS hhull
  · intro w hw i j
    obtain ⟨v, hv, hwv⟩ := support_linear_apply_subset R (affSd R E n) c hw
    exact (sd_mesh R n v D (fun a b => hD v hv a b)).2 w hwv i j

/-- Iterated barycentric subdivision. -/
noncomputable def sdIter (n : ℕ) :
    ℕ → (((Fin (n + 1) → E) →₀ R) →ₗ[R] ((Fin (n + 1) → E) →₀ R))
  | 0 => LinearMap.id
  | (k + 1) => (affSd R E n).comp (sdIter n k)

theorem sdIter_zero {n : ℕ} (c : (Fin (n + 1) → E) →₀ R) : sdIter R n 0 c = c := rfl

theorem sdIter_succ {n k : ℕ} (c : (Fin (n + 1) → E) →₀ R) :
    sdIter R n (k + 1) c = affSd R E n (sdIter R n k c) := rfl

/-- **The mesh of an iterated subdivision shrinks geometrically.** -/
theorem sdIter_mesh {n : ℕ} {S : Set E} (hS : Convex ℝ S) {D : ℝ}
    {c : (Fin (n + 1) → E) →₀ R} (hV : VerticesIn R S c) (hD : DiamLe R D c) (k : ℕ) :
    VerticesIn R S (sdIter R n k c)
      ∧ DiamLe R ((((n : ℝ) / ((n : ℝ) + 1)) ^ k) * D) (sdIter R n k c) := by
  induction k with
  | zero =>
    refine ⟨fun w hw i => hV w hw i, fun w hw i j => ?_⟩
    have := hD w hw i j
    simpa using this
  | succ k ih =>
    have hstep := sd_mesh_chain R hS ih.1 ih.2
    refine ⟨hstep.1, ?_⟩
    intro w hw i j
    have hb := hstep.2 w hw i j
    calc ‖w i - w j‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * ((((n : ℝ) / ((n : ℝ) + 1)) ^ k) * D) := hb
      _ = (((n : ℝ) / ((n : ℝ) + 1)) ^ (k + 1)) * D := by ring

end GaloisForLFunctions.HTGeometry
