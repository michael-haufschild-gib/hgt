import Mathlib

/-!
# Plücker coordinates and their field of definition

The Plücker coordinates of the subspace spanned by the rows of a matrix are its maximal minors.
Changing the spanning basis multiplies every coordinate by one common determinant, so the ratios of
Plücker coordinates depend only on the subspace.

If the spanning matrix can be chosen with entries in a subfield -- that is, if the subspace is
defined over that subfield -- then every minor lies in the subfield, and therefore so does every
normalized Plücker ratio.  This is the descent statement: a subspace obtained by base change from a
smaller field has all its Grassmannian coordinates in that field.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

section Pluecker

variable {K : Type*} [CommRing K] {k n : ℕ}

/-- The Plücker coordinate of the row span of `B` at the column selection `I`. -/
def pluecker (B : Matrix (Fin k) (Fin n) K) (I : Fin k → Fin n) : K :=
  (B.submatrix id I).det

/-- Selecting columns commutes with left multiplication. -/
theorem submatrix_mul_left (C : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin k) (Fin n) K)
    (I : Fin k → Fin n) :
    (C * B).submatrix id I = C * B.submatrix id I := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- **A basis change scales every Plücker coordinate by one determinant.** -/
theorem pluecker_mul (C : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin k) (Fin n) K)
    (I : Fin k → Fin n) :
    pluecker (C * B) I = C.det * pluecker B I := by
  rw [pluecker, submatrix_mul_left, Matrix.det_mul, pluecker]

end Pluecker

section Ratio

variable {K : Type*} [Field K] {k n : ℕ}

/-- **Plücker ratios do not depend on the spanning basis.** -/
theorem pluecker_ratio_mul (C : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin k) (Fin n) K)
    (I J : Fin k → Fin n) (hC : C.det ≠ 0) :
    pluecker (C * B) J / pluecker (C * B) I = pluecker B J / pluecker B I := by
  rw [pluecker_mul, pluecker_mul, mul_div_mul_left _ _ hC]

end Ratio

section Descent

variable {F K : Type*} [Field F] [Field K] {k n : ℕ}

/-- A minor of a matrix with entries in a subfield lies in that subfield. -/
theorem pluecker_mem_range (f : F →+* K) {B : Matrix (Fin k) (Fin n) K}
    (hB : ∀ i j, B i j ∈ Set.range f) (I : Fin k → Fin n) :
    pluecker B I ∈ Set.range f := by
  classical
  choose B' hB' using hB
  set C : Matrix (Fin k) (Fin n) F := Matrix.of B' with hC
  have hmap : B = C.map f := by
    ext i j
    exact (hB' i j).symm
  refine ⟨pluecker C I, ?_⟩
  rw [pluecker, pluecker, hmap, Matrix.submatrix_map]
  exact RingHom.map_det f _

/-- **Plücker descent.**  A subspace spanned by a matrix with entries in a subfield has all its
normalized Plücker ratios in that subfield. -/
theorem pluecker_ratio_mem_range (f : F →+* K) {B : Matrix (Fin k) (Fin n) K}
    (hB : ∀ i j, B i j ∈ Set.range f) (I J : Fin k → Fin n) (hI : pluecker B I ≠ 0) :
    pluecker B J / pluecker B I ∈ Set.range f := by
  obtain ⟨a, ha⟩ := pluecker_mem_range f hB J
  obtain ⟨b, hb⟩ := pluecker_mem_range f hB I
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact hI hb.symm
  refine ⟨a / b, ?_⟩
  rw [map_div₀, ha, hb]

end Descent

end GaloisForLFunctions.HTGeometry
