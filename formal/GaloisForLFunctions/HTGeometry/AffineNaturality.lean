import GaloisForLFunctions.HTGeometry.SubdivisionSupport

/-!
# Naturality of the affine subdivision operators

A linear map of the ambient space carries affine simplices to affine simplices and so induces a map
of affine chain complexes.  Every operator built out of faces and barycenters commutes with it:
the boundary because faces are reindexings of the vertices, the cone because a linear map sends the
barycenter of a tuple to the barycenter of its image, and hence the subdivision operator and its
chain homotopy, both of which are assembled from cones on barycenters by induction on the degree.

Naturality is what allows a subdivision defined once and for all on the standard simplex to be
transported to every singular simplex compatibly with faces.

The second half records that all of these operators keep the vertices of a chain inside a fixed
convex set.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

section Naturality

variable (R : Type u) [CommRing R] {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The map of affine chains induced by a linear map of the ambient space. -/
noncomputable def affPush (L : E →ₗ[ℝ] F) (n : ℕ) :
    ((Fin (n + 1) → E) →₀ R) →ₗ[R] ((Fin (n + 1) → F) →₀ R) :=
  Finsupp.lmapDomain R R (fun v => (L : E → F) ∘ v)

theorem affPush_single (L : E →ₗ[ℝ] F) (n : ℕ) (v : Fin (n + 1) → E) (r : R) :
    affPush R L n (Finsupp.single v r) = Finsupp.single ((L : E → F) ∘ v) r :=
  Finsupp.mapDomain_single

/-- A linear map sends the barycenter of a tuple to the barycenter of its image. -/
theorem bary_map (L : E →ₗ[ℝ] F) {n : ℕ} (v : Fin (n + 1) → E) :
    L (bary E v) = bary F ((L : E → F) ∘ v) := by
  simp only [bary, map_smul, map_sum]
  rfl

theorem affPush_affBd (L : E →ₗ[ℝ] F) {n : ℕ} (c : (Fin (n + 2) → E) →₀ R) :
    affPush R L n (affBd R E n c) = affBd R F n (affPush R L (n + 1) c) := by
  have hmap : (affPush R L n).comp (affBd R E n)
      = (affBd R F n).comp (affPush R L (n + 1)) := by
    refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
    show affPush R L n (affBd R E n (Finsupp.single v (1 : R)))
        = affBd R F n (affPush R L (n + 1) (Finsupp.single v (1 : R)))
    rw [affBd_single, map_sum, affPush_single, affBd_single]
    exact Finset.sum_congr rfl fun i _ => affPush_single R L n _ _
  exact LinearMap.congr_fun hmap c

theorem comp_cons (L : E →ₗ[ℝ] F) {n : ℕ} (b : E) (v : Fin (n + 1) → E) :
    (L : E → F) ∘ (Fin.cons b v : Fin (n + 2) → E)
      = Fin.cons (L b) ((L : E → F) ∘ v) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro m
    simp

theorem affPush_affCone (L : E →ₗ[ℝ] F) (b : E) {n : ℕ} (c : (Fin (n + 1) → E) →₀ R) :
    affPush R L (n + 1) (affCone R E b n c) = affCone R F (L b) n (affPush R L n c) := by
  have hmap : (affPush R L (n + 1)).comp (affCone R E b n)
      = (affCone R F (L b) n).comp (affPush R L n) := by
    refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
    show affPush R L (n + 1) (affCone R E b n (Finsupp.single v (1 : R)))
        = affCone R F (L b) n (affPush R L n (Finsupp.single v (1 : R)))
    rw [show affCone R E b n (Finsupp.single v (1 : R))
        = Finsupp.single (Fin.cons b v) (1 : R) from coneMap_single' R E b n v 1,
      affPush_single, affPush_single,
      show affCone R F (L b) n (Finsupp.single ((L : E → F) ∘ v) (1 : R))
        = Finsupp.single (Fin.cons (L b) ((L : E → F) ∘ v)) (1 : R) from
        coneMap_single' R F (L b) n _ 1, comp_cons]
  exact LinearMap.congr_fun hmap c

/-- **The subdivision operator is natural in the ambient space.** -/
theorem affPush_affSd (L : E →ₗ[ℝ] F) :
    ∀ (n : ℕ) (c : (Fin (n + 1) → E) →₀ R),
      affPush R L n (affSd R E n c) = affSd R F n (affPush R L n c) := by
  intro n
  induction n with
  | zero => intro c; rw [affSd_zero, affSd_zero]
  | succ n ih =>
    intro c
    have hmap : (affPush R L (n + 1)).comp (affSd R E (n + 1))
        = (affSd R F (n + 1)).comp (affPush R L (n + 1)) := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show affPush R L (n + 1) (affSd R E (n + 1) (Finsupp.single v (1 : R)))
          = affSd R F (n + 1) (affPush R L (n + 1) (Finsupp.single v (1 : R)))
      rw [affSd_single, affPush_affCone, bary_map, ih, affPush_affBd, affPush_single]
      exact (affSd_single R F _).symm
    exact LinearMap.congr_fun hmap c

/-- **The subdivision homotopy is natural in the ambient space.** -/
theorem affPush_affT (L : E →ₗ[ℝ] F) :
    ∀ (n : ℕ) (c : (Fin (n + 1) → E) →₀ R),
      affPush R L (n + 1) (affT R E n c) = affT R F n (affPush R L n c) := by
  intro n
  induction n with
  | zero => intro c; rw [affT_zero, affT_zero, map_zero]
  | succ n ih =>
    intro c
    have hmap : (affPush R L (n + 2)).comp (affT R E (n + 1))
        = (affT R F (n + 1)).comp (affPush R L (n + 1)) := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show affPush R L (n + 2) (affT R E (n + 1) (Finsupp.single v (1 : R)))
          = affT R F (n + 1) (affPush R L (n + 1) (Finsupp.single v (1 : R)))
      have hinner : affPush R L (n + 1)
          (affSd R E (n + 1) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
            - affT R E n (affBd R E n (Finsupp.single v (1 : R))))
          = affSd R F (n + 1) (Finsupp.single ((L : E → F) ∘ v) (1 : R))
            - Finsupp.single ((L : E → F) ∘ v) (1 : R)
            - affT R F n (affBd R F n (Finsupp.single ((L : E → F) ∘ v) (1 : R))) := by
        rw [map_sub, map_sub, affPush_affSd, affPush_single, ih, affPush_affBd, affPush_single]
      rw [affT_single, affPush_affCone, bary_map, hinner, affPush_single]
      exact (affT_single R F _).symm
    exact LinearMap.congr_fun hmap c

end Naturality

section Vertices

variable (R : Type u) [CommRing R] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem exists_diam_bound {n : ℕ} (v : Fin (n + 1) → E) : ∃ D : ℝ, ∀ i j, ‖v i - v j‖ ≤ D := by
  refine ⟨∑ i, ∑ j, ‖v i - v j‖, fun a b => ?_⟩
  calc ‖v a - v b‖ ≤ ∑ j, ‖v a - v j‖ :=
        Finset.single_le_sum (f := fun j => ‖v a - v j‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, ‖v i - v j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖v i - v j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ a)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem verticesIn_affBd {S : Set E} {n : ℕ} {c : (Fin (n + 2) → E) →₀ R}
    (h : VerticesIn R S c) : VerticesIn R S (affBd R E n c) := by
  intro w hw i
  obtain ⟨v, hv, hwv⟩ := support_linear_apply_subset R (affBd R E n) c hw
  obtain ⟨j, rfl⟩ := support_affBd_single_subset R v hwv
  exact h v hv _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem verticesIn_sub {S : Set E} {n : ℕ} {c d : (Fin (n + 1) → E) →₀ R}
    (hc : VerticesIn R S c) (hd : VerticesIn R S d) : VerticesIn R S (c - d) := by
  classical
  intro w hw i
  rcases Finset.mem_union.mp (Finsupp.support_sub hw) with h | h
  · exact hc w h i
  · exact hd w h i

/-- The subdivision keeps the vertices of a chain inside a convex set. -/
theorem verticesIn_affSd {S : Set E} (hS : Convex ℝ S) {n : ℕ} {c : (Fin (n + 1) → E) →₀ R}
    (h : VerticesIn R S c) : VerticesIn R S (affSd R E n c) := by
  intro w hw i
  obtain ⟨v, hv, hwv⟩ := support_linear_apply_subset R (affSd R E n) c hw
  obtain ⟨D, hD⟩ := exists_diam_bound v
  have hhull := (sd_mesh R n v D hD).1 w hwv i
  refine convexHull_min ?_ hS hhull
  rintro y ⟨a, rfl⟩
  exact h v hv a

/-- The subdivision homotopy keeps the vertices of a chain inside a convex set. -/
theorem verticesIn_affT {S : Set E} (hS : Convex ℝ S) :
    ∀ (n : ℕ) {c : (Fin (n + 1) → E) →₀ R}, VerticesIn R S c →
      VerticesIn R S (affT R E n c) := by
  intro n
  induction n with
  | zero =>
    intro c _ w hw
    rw [affT_zero] at hw
    exact absurd hw (by simp)
  | succ n ih =>
    intro c h w hw i
    obtain ⟨v, hv, hwv⟩ := support_linear_apply_subset R (affT R E (n + 1)) c hw
    have hvS : ∀ a, v a ∈ S := fun a => h v hv a
    have hsingle : VerticesIn R S (Finsupp.single v (1 : R)) := by
      intro u hu a
      have hu' : u = v := Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
      subst hu'
      exact hvS a
    have hb : bary E v ∈ S := by
      refine convexHull_min ?_ hS (bary_mem_hull v)
      rintro y ⟨a, rfl⟩
      exact hvS a
    have hinner : VerticesIn R S
        (affSd R E (n + 1) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
          - affT R E n (affBd R E n (Finsupp.single v (1 : R)))) :=
      verticesIn_sub R (verticesIn_sub R (verticesIn_affSd R hS hsingle) hsingle)
        (ih (verticesIn_affBd R hsingle))
    have := VerticesIn.affCone R hb hinner
    rw [← affT_single] at this
    exact this w hwv i

end Vertices

end GaloisForLFunctions.HTGeometry
