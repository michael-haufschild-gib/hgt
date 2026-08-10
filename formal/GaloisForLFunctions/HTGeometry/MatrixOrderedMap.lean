import GaloisForLFunctions.HTGeometry.MatrixOrderedSpace

/-!
# Completely positive maps and pullback matrix orderings

A linear map between `*`-vector spaces amplifies entrywise to every matrix level, and the
amplifications commute with compression.  This module records that computation and its two
structural consequences:

* `IsCompletelyPositive` — positivity of every amplification — is closed under composition and
  contains the identity;
* `isMatrixOrdering_comap` — the pullback of a matrix ordering along a linear map is again a
  matrix ordering.  This is how concrete operator systems arise: a self-adjoint subspace of a
  C*-algebra carries the matrix ordering pulled back along its inclusion.

Together with `IsCompletelyPositive.le_comap_iff` these say that complete positivity of `φ` is
exactly the statement that the source ordering refines the pullback of the target ordering.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v w

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- Entrywise amplification of a linear map to a matrix level. -/
def ampMap {n : Type u} (φ : V →ₗ[ℂ] W) (x : Matrix n n V) : Matrix n n W :=
  x.map φ

@[simp]
theorem ampMap_apply {n : Type u} (φ : V →ₗ[ℂ] W) (x : Matrix n n V) (i j : n) :
    ampMap φ x i j = φ (x i j) := rfl

@[simp]
theorem ampMap_zero {n : Type u} (φ : V →ₗ[ℂ] W) : ampMap φ (0 : Matrix n n V) = 0 := by
  ext i j; simp

theorem ampMap_add {n : Type u} (φ : V →ₗ[ℂ] W) (x y : Matrix n n V) :
    ampMap φ (x + y) = ampMap φ x + ampMap φ y := by
  ext i j; simp

theorem ampMap_smul {n : Type u} (φ : V →ₗ[ℂ] W) (c : ℂ) (x : Matrix n n V) :
    ampMap φ (c • x) = c • ampMap φ x := by
  ext i j; simp

/-- **Amplification commutes with compression.** -/
theorem ampMap_compress {m n : Type u} [Fintype m] (φ : V →ₗ[ℂ] W) (α : Matrix m n ℂ)
    (x : Matrix m m V) : ampMap φ (compress α x) = compress α (ampMap φ x) := by
  ext i j
  simp only [ampMap_apply, compress_apply, map_sum, map_smul, ampMap_apply]

theorem ampMap_amplify {n : Type u} [DecidableEq n] (φ : V →ₗ[ℂ] W) (e : V) :
    ampMap φ (amplifyUnit n e) = amplifyUnit n (φ e) := by
  ext i j
  by_cases h : i = j <;> simp [amplifyUnit_apply, h]

/-! ## Compression and the involution -/

variable [StarAddMonoid V] [StarModule ℂ V]

/-- Compression commutes with the involution. -/
theorem compress_conjTranspose {m n : Type u} [Fintype m] (α : Matrix m n ℂ) (x : Matrix m m V) :
    (compress α x)ᴴ = compress α xᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, compress_apply, compress_apply]
  simp only [star_sum, star_smul, star_star, Matrix.conjTranspose_apply]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => smul_comm _ _ _

/-- A compression of a self-adjoint matrix is self-adjoint. -/
theorem isSelfAdjoint_compress {m n : Type u} [Fintype m] (α : Matrix m n ℂ) {x : Matrix m m V}
    (hx : xᴴ = x) : (compress α x)ᴴ = compress α x := by
  rw [compress_conjTranspose, hx]

/-! ## Complete positivity -/

variable [StarAddMonoid W] [StarModule ℂ W]

variable (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V))
variable (D : ∀ (n : Type u) [Fintype n], Set (Matrix n n W))

/-- A linear map is completely positive when every amplification is positive. -/
def IsCompletelyPositive (φ : V →ₗ[ℂ] W) : Prop :=
  ∀ (n : Type u) [Fintype n], ∀ x ∈ C n, ampMap φ x ∈ D n

omit [StarAddMonoid V] [StarModule ℂ V] in
theorem isCompletelyPositive_id : IsCompletelyPositive C C (LinearMap.id) := by
  intro n _ x hx
  have : ampMap (LinearMap.id : V →ₗ[ℂ] V) x = x := by ext i j; simp
  rwa [this]

variable {C D}

omit [StarAddMonoid V] [StarModule ℂ V] [StarAddMonoid W] [StarModule ℂ W] in
theorem IsCompletelyPositive.comp {U : Type*} [AddCommGroup U] [Module ℂ U] [StarAddMonoid U]
    [StarModule ℂ U] {E : ∀ (n : Type u) [Fintype n], Set (Matrix n n U)}
    {φ : V →ₗ[ℂ] W} {ψ : W →ₗ[ℂ] U} (hφ : IsCompletelyPositive C D φ)
    (hψ : IsCompletelyPositive D E ψ) : IsCompletelyPositive C E (ψ.comp φ) := by
  intro n _ x hx
  have hEq : ampMap (ψ.comp φ) x = ampMap ψ (ampMap φ x) := by ext i j; simp
  rw [hEq]
  exact hψ n _ (hφ n x hx)

/-! ## Pullback orderings -/

/-- The matrix ordering pulled back along a linear map. -/
def comapOrdering (φ : V →ₗ[ℂ] W) (D : ∀ (n : Type u) [Fintype n], Set (Matrix n n W)) :
    ∀ (n : Type u) [Fintype n], Set (Matrix n n V) :=
  fun n _ => {x | xᴴ = x ∧ ampMap φ x ∈ D n}

omit [StarModule ℂ W] in
/-- **The pullback of a matrix ordering along a linear map is a matrix ordering.**  This is how
concrete operator systems arise: pull the positivity of a C*-algebra back along the inclusion of a
self-adjoint subspace. -/
theorem isMatrixOrdering_comap (φ : V →ₗ[ℂ] W) (hD : IsMatrixOrdering D) :
    IsMatrixOrdering (comapOrdering φ D) where
  isSelfAdjoint := fun _ _ _ hx => hx.1
  zero_mem := fun n _ => ⟨by simp, by rw [ampMap_zero]; exact hD.zero_mem n⟩
  add_mem := fun n _ x hx y hy =>
    ⟨by rw [Matrix.conjTranspose_add, hx.1, hy.1], by
      rw [ampMap_add]; exact hD.add_mem n _ hx.2 _ hy.2⟩
  compress_mem := fun m n _ _ α x hx =>
    ⟨isSelfAdjoint_compress α hx.1, by
      rw [ampMap_compress]; exact hD.compress_mem m n α _ hx.2⟩

omit [StarModule ℂ V] [StarAddMonoid W] [StarModule ℂ W] in
/-- Complete positivity is exactly the statement that the source ordering refines the pullback of
the target ordering. -/
theorem isCompletelyPositive_iff_le_comap {φ : V →ₗ[ℂ] W}
    (hC : ∀ (n : Type u) [Fintype n], ∀ x ∈ C n, xᴴ = x) :
    IsCompletelyPositive C D φ ↔ ∀ (n : Type u) [Fintype n], C n ⊆ comapOrdering φ D n := by
  constructor
  · intro h n _ x hx
    exact ⟨hC n x hx, h n x hx⟩
  · intro h n _ x hx
    exact (h n hx).2

/-! ## Transport of an order unit -/

omit [StarAddMonoid V] [StarModule ℂ V] [StarAddMonoid W] [StarModule ℂ W] in
/-- A completely positive map sends amplified units to amplified units of the image. -/
theorem IsCompletelyPositive.amplify_image_mem {φ : V →ₗ[ℂ] W} (hφ : IsCompletelyPositive C D φ)
    {n : Type u} [Fintype n] [DecidableEq n] {e : V} (he : amplifyUnit n e ∈ C n) :
    amplifyUnit n (φ e) ∈ D n := by
  have h := hφ n _ he
  rwa [ampMap_amplify] at h

end GaloisForLFunctions.HTGeometry
