/-
# Power sums of a simple root packet are trace powers

A matrix with a full packet of *distinct* characteristic roots has simple spectrum, so the packet is
exactly the diagonal of any Schur triangulation.  Hence every power sum of the packet is the
corresponding trace power of the matrix.

At exponent one this is classical; at exponent two it is the identity `∑ λᵢ² = Tr(M²)` that a
Newton-identity route would need, and which mathlib does not carry.  The proof here uses no Newton
identity: the characteristic polynomial of a triangulation is the product of the diagonal linear
factors, so each root of the packet is a diagonal entry, and counting distinct values forces the
two families to have the same image; summing over the image finishes.

Main results:
* `det_scalar_sub_eq_prod_diag` — the characteristic values of a Schur triangulation.
* `sum_pow_rootPacket_eq_trace_pow_fin`, `sum_pow_rootPacket_eq_trace_pow` — **the power sums of a
  simple root packet are the trace powers**.
-/
import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {m : Type*} [Fintype m] [DecidableEq m] {U T M : Matrix m m ℂ}

/-- **The characteristic values of a Schur triangulation are its diagonal entries.** -/
theorem det_scalar_sub_eq_prod_diag [LinearOrder m] (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (x : ℂ) :
    (Matrix.scalar m x - M).det = ∏ i, (x - T i i) := by
  have hM := eq_conj_of_schur hU2 hMT
  have hsc : (Matrix.scalar m x : Matrix m m ℂ) = x • (1 : Matrix m m ℂ) := by
    rw [Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hscal : U * (Matrix.scalar m x) * Uᴴ = Matrix.scalar m x := by
    rw [hsc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]
  have hconj : Matrix.scalar m x - M = U * (Matrix.scalar m x - T) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hscal, ← hM]
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  have htri : (Matrix.scalar m x - T).BlockTriangular id := by
    intro i j hij
    rw [Matrix.sub_apply, hT hij, sub_zero, Matrix.scalar_apply]
    exact Matrix.diagonal_apply_ne _ hij.ne'
  rw [Matrix.det_of_upperTriangular htri]
  have hentry : ∀ i, (Matrix.scalar m x - T) i i = x - T i i := by
    intro i
    rw [Matrix.sub_apply, Matrix.scalar_apply]
    congr 1
    exact Matrix.diagonal_apply_eq _ i
  simp only [hentry]
  rw [mul_comm (U.det), mul_assoc, det_unitary_mul_det_conjTranspose hU2, mul_one]

/-- **The power sums of a simple root packet are the trace powers**, for a matrix indexed by
`Fin n`. -/
theorem sum_pow_rootPacket_eq_trace_pow_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (lam : Fin n → ℂ) (hinj : Function.Injective lam)
    (hroot : ∀ i, matrixCharpolyRelation (M, lam i) = 0) (k : ℕ) :
    ∑ i, lam i ^ k = (M ^ k).trace := by
  classical
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation n M
  have hdet : ∀ x : ℂ, (Matrix.scalar (Fin n) x - M).det = ∏ i, (x - T i i) :=
    det_scalar_sub_eq_prod_diag hU2 hT hMT
  have hmem : ∀ i, ∃ j, lam i = T j j := by
    intro i
    have h0 : ∏ j, (lam i - T j j) = 0 := by
      rw [← hdet (lam i)]
      exact hroot i
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h0
    exact ⟨j, sub_eq_zero.mp hj⟩
  set Sl : Finset ℂ := Finset.image lam Finset.univ with hSl
  set St : Finset ℂ := Finset.image (fun i => T i i) Finset.univ with hSt
  have hsub : Sl ⊆ St := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj⟩ := hmem i
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
  have hcardl : Sl.card = n := by
    rw [hSl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcardt : St.card ≤ n := by
    calc St.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have hcardeq : St.card = n := le_antisymm hcardt (hcardl ▸ Finset.card_le_card hsub)
  have hSeq : Sl = St := Finset.eq_of_subset_of_card_le hsub (by rw [hcardl, hcardeq])
  have hTinj : Function.Injective (fun i : Fin n => T i i) := by
    have hcard : (Finset.image (fun i : Fin n => T i i) Finset.univ).card
        = (Finset.univ : Finset (Fin n)).card := by
      rw [← hSt, hcardeq, Finset.card_univ, Fintype.card_fin]
    have hinjOn := Finset.injOn_of_card_image_eq hcard
    exact fun a b hab => hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
  calc ∑ i, lam i ^ k = ∑ x ∈ Sl, x ^ k := by
        rw [hSl, Finset.sum_image (fun x _ y _ h => hinj h)]
    _ = ∑ x ∈ St, x ^ k := by rw [hSeq]
    _ = ∑ i, (T i i) ^ k := by rw [hSt, Finset.sum_image (fun x _ y _ h => hTinj h)]
    _ = (M ^ k).trace := (trace_pow_eq_sum_diag hU1 hU2 hT hMT k).symm

/-- **The power sums of a simple root packet are the trace powers**, for any finite index type. -/
theorem sum_pow_rootPacket_eq_trace_pow {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (lam : I → ℂ) (hinj : Function.Injective lam)
    (hroot : ∀ i, matrixCharpolyRelation (M, lam i) = 0) (k : ℕ) :
    ∑ i, lam i ^ k = (M ^ k).trace := by
  classical
  set e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm with he
  have hscal : ∀ x : ℂ,
      (Matrix.scalar I x).submatrix e e = Matrix.scalar (Fin (Fintype.card I)) x := by
    intro x
    ext i j
    rw [Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (fun h => hij (e.injective h)),
        Matrix.diagonal_apply_ne _ hij]
  have hrootF : ∀ i : Fin (Fintype.card I),
      matrixCharpolyRelation (M.submatrix e e, lam (e i)) = 0 := by
    intro i
    show (Matrix.scalar (Fin (Fintype.card I)) (lam (e i)) - M.submatrix e e).det = 0
    have hEq : Matrix.scalar (Fin (Fintype.card I)) (lam (e i)) - M.submatrix e e
        = (Matrix.scalar I (lam (e i)) - M).submatrix e e := by
      rw [← hscal (lam (e i))]
      ext a b
      simp [Matrix.submatrix_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.diagonal_apply_ne _ hab,
          Matrix.diagonal_apply_ne _ (fun h => hab (e.injective h))]
    rw [hEq, Matrix.det_submatrix_equiv_self]
    exact hroot (e i)
  have hinjF : Function.Injective (fun i => lam (e i)) := hinj.comp e.injective
  have hsum := sum_pow_rootPacket_eq_trace_pow_fin (M.submatrix e e) (fun i => lam (e i)) hinjF
    hrootF k
  rw [trace_pow_submatrix e M k] at hsum
  rw [← hsum]
  exact (Fintype.sum_equiv e (fun i => lam (e i) ^ k) (fun i => lam i ^ k) fun i => rfl).symm

end GaloisForLFunctions.HTGeometry
