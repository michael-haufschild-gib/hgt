import GaloisForLFunctions.HTGeometry.Sl2AdjointIrreducible
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Adjoint stability passes to the Zariski closure

For a `2×2` matrix of determinant one the inverse is the adjugate, which is a *polynomial* in the
entries.  So for fixed `A` and a fixed linear functional `φ`, the map `g ↦ φ(g·A·adj g)` is a
polynomial function of the entries of `g`.  If a subspace `V` is stable under conjugation by a
subgroup `G`, then for every `A ∈ V` that polynomial vanishes on `G` for every `φ` killing `V`;
Zariski density of `G` extends the vanishing to every determinant-one matrix, and a subspace of a
finite-dimensional space is the common kernel of the functionals killing it.

* `adjugate_two` — the adjugate of a `2×2` matrix, explicitly;
* `conj_mem_of_dense` — adjoint stability extends from `G` to every determinant-one matrix;
* `upperConj_mem_of_dense`, `lowerConj_mem_of_dense` — the two unipotent lines, which is the form
  `sl2_of_adStable` consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

theorem adjugate_two (g : Matrix (Fin 2) (Fin 2) U) :
    Matrix.adjugate g = !![g 1 1, -(g 0 1); -(g 1 0), g 0 0] :=
  Matrix.adjugate_fin_two g

theorem det_unipotentUpper (t : U) : (unipotentUpper t).det = 1 := by
  rw [unipotentUpper, Matrix.det_fin_two_of]
  ring

theorem det_unipotentLower (t : U) : (unipotentLower t).det = 1 := by
  rw [unipotentLower, Matrix.det_fin_two_of]
  ring

theorem adjugate_unipotentUpper (t : U) :
    Matrix.adjugate (unipotentUpper t) = unipotentUpper (-t) := by
  rw [adjugate_two, unipotentUpper, unipotentUpper]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

theorem adjugate_unipotentLower (t : U) :
    Matrix.adjugate (unipotentLower t) = unipotentLower (-t) := by
  rw [adjugate_two, unipotentLower, unipotentLower]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

/-- **Adjoint stability passes to every determinant-one matrix.**  The density hypothesis is stated
where it is used: the polynomial function `g ↦ φ(g·A·adj g)`, which vanishes on `G`, vanishes on
every determinant-one matrix. -/
theorem conj_mem_of_dense
    (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hstable : ∀ g ∈ G, ∀ A ∈ V, g * A * Matrix.adjugate g ∈ V)
    (hdense : ∀ (A : Matrix (Fin 2) (Fin 2) U) (φ : Matrix (Fin 2) (Fin 2) U →ₗ[U] U),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) U, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    {g : Matrix (Fin 2) (Fin 2) U} (hg : g.det = 1)
    {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) :
    g * A * Matrix.adjugate g ∈ V := by
  by_contra hnot
  obtain ⟨φ, hφne, hφV⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hnot (inferInstance : Module.Projective U _)
  have hzero : ∀ v ∈ V, φ v = 0 := by
    intro v hv
    have : φ v ∈ V.map φ := Submodule.mem_map_of_mem hv
    rw [hφV] at this
    simpa using this
  exact hφne (hdense A φ (fun h hh => hzero _ (hstable h hh A hA)) g hg)

/-- The upper unipotent form. -/
theorem upperConj_mem_of_dense
    (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hstable : ∀ g ∈ G, ∀ A ∈ V, g * A * Matrix.adjugate g ∈ V)
    (hdense : ∀ (A : Matrix (Fin 2) (Fin 2) U) (φ : Matrix (Fin 2) (Fin 2) U →ₗ[U] U),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) U, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    (t : U) {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) : upperConj t A ∈ V := by
  have h := conj_mem_of_dense V G hstable hdense (det_unipotentUpper t) hA
  rwa [adjugate_unipotentUpper] at h

/-- The lower unipotent form. -/
theorem lowerConj_mem_of_dense
    (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hstable : ∀ g ∈ G, ∀ A ∈ V, g * A * Matrix.adjugate g ∈ V)
    (hdense : ∀ (A : Matrix (Fin 2) (Fin 2) U) (φ : Matrix (Fin 2) (Fin 2) U →ₗ[U] U),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) U, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    (t : U) {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) : lowerConj t A ∈ V := by
  have h := conj_mem_of_dense V G hstable hdense (det_unipotentLower t) hA
  rwa [adjugate_unipotentLower] at h

/-- **The span of the Lie algebra of a Zariski-dense subgroup is all of `sl₂`.** -/
theorem sl2_of_dense [CharZero U]
    (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hstable : ∀ g ∈ G, ∀ A ∈ V, g * A * Matrix.adjugate g ∈ V)
    (hdense : ∀ (A : Matrix (Fin 2) (Fin 2) U) (φ : Matrix (Fin 2) (Fin 2) U →ₗ[U] U),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) U, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) (hAne : A ≠ 0) (htr : A 1 1 = -A 0 0)
    {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z 1 1 = -Z 0 0) : Z ∈ V :=
  sl2_of_adStable V (fun t _ hB => upperConj_mem_of_dense V G hstable hdense t hB)
    (fun t _ hB => lowerConj_mem_of_dense V G hstable hdense t hB) hA hAne htr hZ

end

end GaloisForLFunctions.HTGeometry
