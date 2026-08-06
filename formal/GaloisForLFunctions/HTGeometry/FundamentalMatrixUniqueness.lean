import GaloisForLFunctions.HTGeometry.FundamentalMatrixSourceBoundary

/-!
# Integrability and uniqueness of a fundamental matrix

A fundamental matrix forces the adjoint local system to satisfy the integrability condition
`tau_i(M_j) M_i = tau_j(M_i) M_j`, which is the cocycle condition of a flat connection: existence of
a solution matrix is not automatic, and this is exactly what it costs.

Two fundamental matrices of the same local system differ on the right by a matrix of constants.  So
the differential field a fundamental matrix generates, and therefore the whole curved rank law, does
not depend on which fundamental matrix is chosen.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

variable {κ : Type u} [Fintype κ] [DecidableEq κ]

/-! ### Cancelling a fundamental matrix -/

omit [Algebra C K] [Algebra C L] [IsScalarTower C K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L] [Fintype κ] [DecidableEq κ] in
/-- A base matrix is determined by its image in the ambient field. -/
theorem baseMat_injective {A B : Matrix κ κ K}
    (h : (baseMat A : Matrix κ κ L) = baseMat B) : A = B := by
  ext p q
  have hpq : (baseMat A : Matrix κ κ L) p q = (baseMat B : Matrix κ κ L) p q := by rw [h]
  simp only [baseMat, Matrix.map_apply] at hpq
  exact (algebraMap K L).injective hpq

omit [Algebra C K] [Algebra C L] [IsScalarTower C K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
/-- A right factor which is invertible can be cancelled. -/
theorem baseMat_eq_of_mul_eq {A B : Matrix κ κ K} {Y Yinv : Matrix κ κ L}
    (hYY : Y * Yinv = 1)
    (h : (baseMat A : Matrix κ κ L) * Y = (baseMat B : Matrix κ κ L) * Y) : A = B := by
  refine baseMat_injective (L := L) ?_
  calc (baseMat A : Matrix κ κ L)
      = baseMat A * (Y * Yinv) := by rw [hYY, mul_one]
    _ = (baseMat A * Y) * Yinv := by rw [mul_assoc]
    _ = (baseMat B * Y) * Yinv := by rw [h]
    _ = baseMat B * (Y * Yinv) := by rw [mul_assoc]
    _ = baseMat B := by rw [hYY, mul_one]

/-! ### Integrability -/

omit [Algebra C K] [Algebra C L] [IsScalarTower C K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
/-- **A fundamental matrix forces the integrability condition.**  If the source directions commute,
the adjoint local system satisfies the flat-connection cocycle condition. -/
theorem fundamental_integrability
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    {Y Yinv : Matrix κ κ L} {M : I → Matrix κ κ K}
    (hYY : Y * Yinv = 1)
    (hfund : ∀ i, Y.map (sigma i) = baseMat (M i) * Y)
    (hcommute : ∀ i j (x : L), sigma i (sigma j x) = sigma j (sigma i x)) (i j : I) :
    (tau i).toRingHom.mapMatrix (M j) * M i = (tau j).toRingHom.mapMatrix (M i) * M j := by
  have hbase : ∀ (a : I) (A : Matrix κ κ K),
      (baseMat A : Matrix κ κ L).map (sigma a) = baseMat ((tau a).toRingHom.mapMatrix A) := by
    intro a A
    ext p q
    simpa [baseMat] using hcomp a (A p q)
  have hstep : ∀ a b : I, (Y.map (sigma b)).map (sigma a)
      = baseMat ((tau a).toRingHom.mapMatrix (M b)) * (baseMat (M a) * Y) := by
    intro a b
    rw [hfund b, Matrix.map_mul, hbase a (M b), hfund a]
  have hcomm : (Y.map (sigma j)).map (sigma i) = (Y.map (sigma i)).map (sigma j) := by
    ext p q
    simpa using hcommute i j (Y p q)
  have hmul : (baseMat ((tau i).toRingHom.mapMatrix (M j) * M i) : Matrix κ κ L) * Y
      = (baseMat ((tau j).toRingHom.mapMatrix (M i) * M j) : Matrix κ κ L) * Y := by
    rw [baseMat_mul, baseMat_mul, mul_assoc, mul_assoc, ← hstep i j, ← hstep j i, hcomm]
  exact baseMat_eq_of_mul_eq (L := L) hYY hmul

/-! ### Uniqueness up to constants -/

omit [Differential K] [Differential L] [DifferentialAlgebra K L] [Fintype κ] [DecidableEq κ] in
/-- An entry fixed by every source direction lies in every intermediate field. -/
theorem invariant_entry_mem
    (hfixed : ∀ y : L, (∀ i, sigma i y = y) → ∃ c : C, algebraMap C L c = y)
    {D : Matrix κ κ L} (hD : ∀ i, D.map (sigma i) = D) (B : IntermediateField K L) (p q : κ) :
    D p q ∈ B := by
  obtain ⟨c, hc⟩ := hfixed (D p q) fun i => by
    have h : (D.map (sigma i)) p q = D p q := by rw [hD i]
    simpa using h
  rw [← hc, IsScalarTower.algebraMap_apply C K L]
  exact B.algebraMap_mem _

omit [Algebra C K] [Algebra C L] [IsScalarTower C K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
/-- **The ratio of two fundamental matrices is a matrix of constants.** -/
theorem fundamental_ratio_invariant
    {Y Yinv Z : Matrix κ κ L} {M Minv : I → Matrix κ κ K}
    (hYY : Y * Yinv = 1) (hYY' : Yinv * Y = 1)
    (hMM : ∀ i, M i * Minv i = 1) (hMM' : ∀ i, Minv i * M i = 1)
    (hfundY : ∀ i, Y.map (sigma i) = baseMat (M i) * Y)
    (hfundZ : ∀ i, Z.map (sigma i) = baseMat (M i) * Z) (i : I) :
    (Yinv * Z).map (sigma i) = Yinv * Z := by
  rw [map_sigma_mul sigma i, map_sigma_fundamental_inv sigma hYY hYY' hMM hMM' hfundY i,
    hfundZ i]
  calc Yinv * baseMat (Minv i) * (baseMat (M i) * Z)
      = Yinv * (baseMat (Minv i) * baseMat (M i)) * Z := by simp [mul_assoc]
    _ = Yinv * Z := by
        rw [← baseMat_mul, hMM' i, baseMat_one, mul_one]

/-- **The field generated by a fundamental matrix is intrinsic.**  Two fundamental matrices of the
same local system generate the same differential field over the base, so the curved rank law does
not depend on the choice. -/
theorem fundamentalField_eq_of_fundamental
    (hfixed : ∀ y : L, (∀ i, sigma i y = y) → ∃ c : C, algebraMap C L c = y)
    {Y Yinv Z Zinv : Matrix κ κ L} {M Minv : I → Matrix κ κ K}
    (hYY : Y * Yinv = 1) (hYY' : Yinv * Y = 1)
    (hZZ : Z * Zinv = 1) (hZZ' : Zinv * Z = 1)
    (hMM : ∀ i, M i * Minv i = 1) (hMM' : ∀ i, Minv i * M i = 1)
    (hfundY : ∀ i, Y.map (sigma i) = baseMat (M i) * Y)
    (hfundZ : ∀ i, Z.map (sigma i) = baseMat (M i) * Z) :
    fundamentalField K Z Zinv = fundamentalField K Y Yinv := by
  have hmemZ : ∀ p q, Z p q ∈ fundamentalField K Y Yinv := by
    intro p q
    have hZeq : Z = Y * (Yinv * Z) := by rw [← mul_assoc, hYY, one_mul]
    have hD : ∀ p q, (Yinv * Z) p q ∈ fundamentalField K Y Yinv := fun p q =>
      invariant_entry_mem (C := C) sigma hfixed
        (fundamental_ratio_invariant sigma hYY hYY' hMM hMM' hfundY hfundZ) _ p q
    rw [hZeq, Matrix.mul_apply]
    refine (fundamentalField K Y Yinv).sum_mem fun r _ => ?_
    exact (fundamentalField K Y Yinv).mul_mem (fundamental_mem_field Y Yinv p r) (hD r q)
  have hmemZinv : ∀ p q, Zinv p q ∈ fundamentalField K Y Yinv := by
    intro p q
    have hZeq : Zinv = (Zinv * Y) * Yinv := by rw [mul_assoc, hYY, mul_one]
    have hD : ∀ p q, (Zinv * Y) p q ∈ fundamentalField K Y Yinv := fun p q =>
      invariant_entry_mem (C := C) sigma hfixed
        (fundamental_ratio_invariant sigma hZZ hZZ' hMM hMM' hfundZ hfundY) _ p q
    rw [hZeq, Matrix.mul_apply]
    refine (fundamentalField K Y Yinv).sum_mem fun r _ => ?_
    exact (fundamentalField K Y Yinv).mul_mem (hD p r) (fundamentalInv_mem_field Y Yinv r q)
  have hmemY : ∀ p q, Y p q ∈ fundamentalField K Z Zinv := by
    intro p q
    have hYeq : Y = Z * (Zinv * Y) := by rw [← mul_assoc, hZZ, one_mul]
    have hD : ∀ p q, (Zinv * Y) p q ∈ fundamentalField K Z Zinv := fun p q =>
      invariant_entry_mem (C := C) sigma hfixed
        (fundamental_ratio_invariant sigma hZZ hZZ' hMM hMM' hfundZ hfundY) _ p q
    rw [hYeq, Matrix.mul_apply]
    refine (fundamentalField K Z Zinv).sum_mem fun r _ => ?_
    exact (fundamentalField K Z Zinv).mul_mem (fundamental_mem_field Z Zinv p r) (hD r q)
  have hmemYinv : ∀ p q, Yinv p q ∈ fundamentalField K Z Zinv := by
    intro p q
    have hYeq : Yinv = (Yinv * Z) * Zinv := by rw [mul_assoc, hZZ, mul_one]
    have hD : ∀ p q, (Yinv * Z) p q ∈ fundamentalField K Z Zinv := fun p q =>
      invariant_entry_mem (C := C) sigma hfixed
        (fundamental_ratio_invariant sigma hYY hYY' hMM hMM' hfundY hfundZ) _ p q
    rw [hYeq, Matrix.mul_apply]
    refine (fundamentalField K Z Zinv).sum_mem fun r _ => ?_
    exact (fundamentalField K Z Zinv).mul_mem (hD p r) (fundamentalInv_mem_field Z Zinv r q)
  refine le_antisymm ?_ ?_
  · refine differentialAdjoin_le K ?_ (derivationClosed_differentialAdjoin K _)
    rintro - (⟨⟨p, q⟩, rfl⟩ | ⟨⟨p, q⟩, rfl⟩)
    · exact hmemZ p q
    · exact hmemZinv p q
  · refine differentialAdjoin_le K ?_ (derivationClosed_differentialAdjoin K _)
    rintro - (⟨⟨p, q⟩, rfl⟩ | ⟨⟨p, q⟩, rfl⟩)
    · exact hmemY p q
    · exact hmemYinv p q

end

end GaloisForLFunctions.HTGeometry
