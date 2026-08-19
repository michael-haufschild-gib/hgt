import GaloisForLFunctions.HTGeometry.SiegelProjMono

/-!
# Leading minors of an integral form are at least one

A form with integer entries has integer leading minors, and a positive integer is at least one.
Combined with the comparison of leading minors, a uniform ellipticity bound `A ≥ λ·B` against an
integral positive definite `B` therefore bounds every leading minor of `A` below by `λ^k`.

This is the lower bound that lattice basis reduction descends against, and it replaces the
measure-theoretic Minkowski route: the integrality of the standard Gram matrix of integer vectors
does the same work with no geometry of numbers at all.

* `det_leadingBlock_intCast` : integral forms have integral leading minors.
* `one_le_det_leadingBlock_of_int` : a positive one is at least one.
* `pow_le_det_leadingBlock` : **the lower bound.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- A form with integer entries has integral leading minors. -/
theorem det_leadingBlock_intCast {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin n) ℤ} (hAB : ∀ a b, A a b = (B a b : ℝ)) {k : ℕ} (hk : k ≤ n) :
    ∃ z : ℤ, (leadingBlock hk A).det = (z : ℝ) := by
  refine ⟨(B.submatrix (Fin.castLE hk) (Fin.castLE hk)).det, ?_⟩
  have hmap : leadingBlock hk A
      = (B.submatrix (Fin.castLE hk) (Fin.castLE hk)).map (fun z : ℤ => (z : ℝ)) := by
    ext a b
    exact hAB _ _
  rw [hmap]
  exact (RingHom.map_det (Int.castRingHom ℝ) _).symm

/-- A positive integral leading minor is at least one. -/
theorem one_le_det_leadingBlock_of_int {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin n) ℤ} (hAB : ∀ a b, A a b = (B a b : ℝ)) {k : ℕ} (hk : k ≤ n)
    (hpos : 0 < (leadingBlock hk A).det) : 1 ≤ (leadingBlock hk A).det := by
  obtain ⟨z, hz⟩ := det_leadingBlock_intCast hAB hk
  rw [hz] at hpos ⊢
  have hz1 : 1 ≤ z := by
    have : (0 : ℤ) < z := by exact_mod_cast hpos
    omega
  exact_mod_cast hz1

/-- **The lower bound for the leading minors.**  If `A` dominates `λ` times an integral positive
definite form, every leading minor of `A` is at least `λ^k`. -/
theorem pow_le_det_leadingBlock {J K : JacobiData n} {lam : ℝ} (hlam : 0 ≤ lam)
    (hdom : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    {B : Matrix (Fin n) (Fin n) ℤ} (hKB : ∀ a b, K.form a b = (B a b : ℝ))
    {k : ℕ} (hk : k ≤ n) :
    lam ^ k ≤ (leadingBlock hk J.form).det := by
  have hKpos : 0 < (leadingBlock hk K.form).det := by
    rw [det_leadingBlock_form hk K]
    exact Finset.prod_pos fun m _ => K.pos _
  have hK1 : 1 ≤ (leadingBlock hk K.form).det :=
    one_le_det_leadingBlock_of_int hKB hk hKpos
  have hmono := det_leadingBlock_mono hlam hdom hk
  have hlamk : (0 : ℝ) ≤ lam ^ k := pow_nonneg hlam k
  calc lam ^ k = lam ^ k * 1 := by ring
    _ ≤ lam ^ k * (leadingBlock hk K.form).det := mul_le_mul_of_nonneg_left hK1 hlamk
    _ ≤ (leadingBlock hk J.form).det := hmono

end GaloisForLFunctions.HTGeometry
