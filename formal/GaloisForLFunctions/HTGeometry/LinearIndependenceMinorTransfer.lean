/-
# The maximal-minor criterion and field transfer of linear independence

A finite family of coordinate vectors over a field is linearly independent exactly when some
square column selection of the matrix it forms is nonsingular.  Both directions of that criterion
are proved here for arbitrary finite index types over an arbitrary field.

Because determinants commute with ring homomorphisms and a homomorphism of fields is injective,
the criterion makes linear independence of such a family invariant under every field
homomorphism, in both directions.  This is the descent step that lets a matroid represented over
one field of characteristic zero be represented over another.
-/
import Mathlib

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- A matrix with linearly independent rows has an invertible square column selection. -/
theorem exists_injective_det_submatrix_ne_zero
    {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {M : Matrix ι κ F} (h : LinearIndependent F (fun i => M i)) :
    ∃ s : ι → κ, Function.Injective s ∧ (M.submatrix id s).det ≠ 0 := by
  classical
  have hrow : LinearIndependent F M.row := h
  have hrank : M.rank = Fintype.card ι := hrow.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← Matrix.rank, hrank]
    simp
  have hspan : Submodule.span F (Set.range (fun j : κ => Mᵀ j)) = ⊤ := by
    rw [← htop, Matrix.range_mulVecLin]
    rfl
  obtain ⟨b, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent F (Set.range (fun j : κ => Mᵀ j))
  have hbtop : Submodule.span F b = ⊤ := by rw [hbspan]; exact hspan
  haveI : Fintype b := Set.Finite.fintype
    (Set.Finite.subset (Set.finite_range _) hbsub)
  have hcard : Fintype.card b = Fintype.card ι := by
    have hbasis : Module.finrank F (ι → F) = Fintype.card b := by
      have := finrank_span_eq_card hbind
      rw [Subtype.range_coe] at this
      rw [← this, hbtop]
      simp
    rw [← hbasis]
    simp
  have hchoice : ∀ v : b, ∃ j : κ, Mᵀ j = (v : ι → F) := by
    intro v
    obtain ⟨j, hj⟩ := hbsub v.2
    exact ⟨j, hj⟩
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    rw [← hf v, ← hf w, hvw]
  let e : ι ≃ b := Fintype.equivOfCardEq hcard.symm
  refine ⟨fun k => f (e k), hfinj.comp e.injective, ?_⟩
  have hind : LinearIndependent F (fun k : ι => Mᵀ (f (e k))) := by
    have hcomp := hbind.comp e e.injective
    have heq : (fun k : ι => Mᵀ (f (e k))) = (Subtype.val ∘ ⇑e) :=
      funext fun k => hf (e k)
    rw [heq]
    exact hcomp
  have hrows : LinearIndependent F ((M.submatrix id (fun k => f (e k)))ᵀ.row) := hind
  have hunit : IsUnit ((M.submatrix id (fun k => f (e k)))ᵀ) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet : IsUnit ((M.submatrix id (fun k => f (e k)))ᵀ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  rw [Matrix.det_transpose] at hdet
  exact hdet.ne_zero

/-- A nonsingular square column selection makes the rows linearly independent. -/
theorem linearIndependent_rows_of_det_submatrix_ne_zero
    {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {M : Matrix ι κ F} {s : ι → κ} (h : (M.submatrix id s).det ≠ 0) :
    LinearIndependent F (fun i => M i) := by
  apply LinearIndependent.of_comp (LinearMap.funLeft F F s)
  simpa [Function.comp_def, Matrix.row, Matrix.submatrix] using!
    (Matrix.linearIndependent_rows_of_det_ne_zero h)

/-- **Field homomorphisms neither create nor destroy linear relations among finite coordinate
vector families.**  Both directions rest on the nonsingular maximal minor criterion. -/
theorem linearIndependent_coords_map_iff
    {F F' ι κ : Type*} [Field F] [Field F']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (σ : F →+* F') (v : ι → κ → F) :
    LinearIndependent F' (fun i => fun j => σ (v i j)) ↔ LinearIndependent F v := by
  have hinj : Function.Injective σ := σ.injective
  constructor
  · intro h
    obtain ⟨s, _, hdet⟩ := exists_injective_det_submatrix_ne_zero
      (M := Matrix.of fun i j => σ (v i j)) h
    refine linearIndependent_rows_of_det_submatrix_ne_zero (M := Matrix.of v) (s := s) ?_
    intro hzero
    apply hdet
    have : ((Matrix.of fun i j => σ (v i j)).submatrix id s)
        = σ.mapMatrix ((Matrix.of v).submatrix id s) := rfl
    rw [this, ← RingHom.map_det, hzero, map_zero]
  · intro h
    obtain ⟨s, _, hdet⟩ := exists_injective_det_submatrix_ne_zero (M := Matrix.of v) h
    refine linearIndependent_rows_of_det_submatrix_ne_zero
      (M := Matrix.of fun i j => σ (v i j)) (s := s) ?_
    have : ((Matrix.of fun i j => σ (v i j)).submatrix id s)
        = σ.mapMatrix ((Matrix.of v).submatrix id s) := rfl
    rw [this, ← RingHom.map_det]
    exact fun hz => hdet (hinj (by simpa using hz))

end GaloisForLFunctions.HTGeometry
