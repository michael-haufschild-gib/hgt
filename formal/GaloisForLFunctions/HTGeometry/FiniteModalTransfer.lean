import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-!
# Finite modal transfer laws

A linear observation filter that is diagonal on a finite modal packet rescales the amplitude of
mode `i` by a transfer value `transfer i`.  The maximal Hankel determinant is consequently
multiplied by the product of all transfer values.  This gives an exact algebraic distinction
between a faithful observation channel and a mode-erasing filter; it depends only on observable
values, not on an interpretation of the index as physical time.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- A finite modal packet after a filter acts diagonally on its modes. -/
def finiteModalTransferSequence {K : Type*} [CommSemiring K] {d : ℕ}
    (transfer weight node : Fin d → K) : ℕ → K :=
  finiteModalSequence (fun i ↦ weight i * transfer i) node

/-- The maximal Hankel determinant is multiplied by the product of the transfer values. -/
theorem det_algebraicHankelMatrix_finiteModalTransferSequence
    {K : Type*} [CommRing K] {d : ℕ} (transfer weight node : Fin d → K) :
    (algebraicHankelMatrix (finiteModalTransferSequence transfer weight node) d).det =
      (algebraicHankelMatrix (finiteModalSequence weight node) d).det *
        ∏ i, transfer i := by
  rw [finiteModalTransferSequence,
    det_algebraicHankelMatrix_finiteModalSequence,
    det_algebraicHankelMatrix_finiteModalSequence,
    Finset.prod_mul_distrib]
  ring

/-- A transfer zero forces the corresponding maximal modal determinant to vanish. -/
theorem det_algebraicHankelMatrix_finiteModalTransferSequence_eq_zero_of_transfer_eq_zero
    {K : Type*} [Field K] {d : ℕ} {transfer weight node : Fin d → K}
    {i : Fin d} (hi : transfer i = 0) :
    (algebraicHankelMatrix (finiteModalTransferSequence transfer weight node) d).det = 0 := by
  rw [det_algebraicHankelMatrix_finiteModalTransferSequence]
  have hproduct : (∏ j, transfer j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [hproduct, mul_zero]

/-- For an active packet, the filtered maximal block is nonsingular exactly when no transfer
value vanishes. -/
theorem det_algebraicHankelMatrix_finiteModalTransferSequence_ne_zero_iff
    {K : Type*} [Field K] {d : ℕ} {transfer weight node : Fin d → K}
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0) :
    (algebraicHankelMatrix (finiteModalTransferSequence transfer weight node) d).det ≠ 0 ↔
      ∀ i, transfer i ≠ 0 := by
  rw [det_algebraicHankelMatrix_finiteModalTransferSequence]
  have hbase :
      (algebraicHankelMatrix (finiteModalSequence weight node) d).det ≠ 0 :=
    det_algebraicHankelMatrix_finiteModalSequence_ne_zero hnode hweight
  constructor
  · intro hfiltered i hi
    have hproduct : (∏ j, transfer j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    apply hfiltered
    rw [hproduct, mul_zero]
  · intro htransfer
    exact mul_ne_zero hbase (Finset.prod_ne_zero_iff.mpr fun i _ ↦ htransfer i)

/-- **Faithful-filter exact mode-count law.**  Distinct active modes retain their exact noiseless
Hankel mode count through any diagonal filter whose transfer values are all nonzero. -/
theorem finiteModalTransferSequence_exact_hankel_mode_count
    {K : Type*} [Field K] {d : ℕ} {transfer weight node : Fin d → K}
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0)
    (htransfer : ∀ i, transfer i ≠ 0) :
    (algebraicHankelMatrix (finiteModalTransferSequence transfer weight node) d).det ≠ 0 ∧
      (algebraicHankelMatrix (finiteModalTransferSequence transfer weight node) (d + 1)).det = 0 := by
  exact finiteModalSequence_exact_hankel_mode_count hnode
    (fun i ↦ mul_ne_zero (hweight i) (htransfer i))

end

end HTGeometry
