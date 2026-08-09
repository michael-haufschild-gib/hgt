import GaloisForLFunctions.HTGeometry.TwoReplicaEdgeCommutatorSwapBasis

/-!
# Hilbert–Schmidt geometry of sitewise two-replica tensor products

A sitewise tensor product of local two-replica matrices has the trace, the adjoint and the
Hilbert–Schmidt pairing of a product: each is computed factor by factor.  These are the three
facts that turn the local orthogonality relations between the singlet algebra `span{I, F}` and the
replica differences `D_a`, `F D_a` into orthogonality of the edge-defect sectors on the whole
register.
-/

open Matrix Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The trace of a sitewise tensor product is the product of the local traces. -/
theorem trace_finiteTwoReplicaLocalMatrix
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    Matrix.trace (finiteTwoReplicaLocalMatrix M) = ∏ v, Matrix.trace (M v) := by
  simp only [Matrix.trace, Matrix.diag_apply, finiteTwoReplicaLocalMatrix]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset TwoReplicaLocalIndex))
    (fun v (i : TwoReplicaLocalIndex) => M v i i), Fintype.piFinset_univ]
  exact Fintype.sum_equiv (finiteTwoReplicaConfigurationEquiv V) _ _ fun _ => rfl

/-- The adjoint of a sitewise tensor product is the sitewise tensor product of the adjoints. -/
theorem conjTranspose_finiteTwoReplicaLocalMatrix
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    (finiteTwoReplicaLocalMatrix M)ᴴ = finiteTwoReplicaLocalMatrix fun v => (M v)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, finiteTwoReplicaLocalMatrix]
  exact star_prod _ _

/-- The Hilbert–Schmidt pairing of two sitewise tensor products is the product of the local
Hilbert–Schmidt pairings. -/
theorem trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix
    (M N : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    Matrix.trace ((finiteTwoReplicaLocalMatrix M)ᴴ * finiteTwoReplicaLocalMatrix N)
      = ∏ v, Matrix.trace ((M v)ᴴ * N v) := by
  rw [conjTranspose_finiteTwoReplicaLocalMatrix, finiteTwoReplicaLocalMatrix_mul,
    trace_finiteTwoReplicaLocalMatrix]

/-- A sitewise tensor product with one Hilbert–Schmidt-orthogonal slot pairs to zero. -/
theorem trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix_eq_zero
    (M N : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) {w : V}
    (hw : Matrix.trace ((M w)ᴴ * N w) = 0) :
    Matrix.trace ((finiteTwoReplicaLocalMatrix M)ᴴ * finiteTwoReplicaLocalMatrix N) = 0 := by
  rw [trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix]
  exact Finset.prod_eq_zero (Finset.mem_univ w) hw

/-! ### The local Hilbert–Schmidt relations of the two-replica singlet layer -/

/-- The identity/swap words are self-adjoint. -/
theorem isHermitian_twoReplicaLocalSwapRaw (x : Bool) :
    (twoReplicaLocalSwapRaw x).IsHermitian := by
  cases x with
  | false => simp [twoReplicaLocalSwapRaw]
  | true => simpa [twoReplicaLocalSwapRaw] using isHermitian_twoReplicaSwap

/-- The swap translate of a replica difference is anti-self-adjoint. -/
theorem conjTranspose_swap_mul_twoReplicaLocalDiff (a : Fin 3) :
    (twoReplicaSwap * twoReplicaLocalDiff a)ᴴ = -(twoReplicaSwap * twoReplicaLocalDiff a) := by
  rw [Matrix.conjTranspose_mul, isHermitian_twoReplicaSwap, isHermitian_twoReplicaLocalDiff a,
    twoReplicaLocalDiff_mul_swap]

/-- A replica difference is Hilbert–Schmidt orthogonal to the local singlet algebra. -/
theorem trace_conjTranspose_diff_mul_swapRaw (a : Fin 3) (x : Bool) :
    Matrix.trace ((twoReplicaLocalDiff a)ᴴ * twoReplicaLocalSwapRaw x) = 0 := by
  rw [isHermitian_twoReplicaLocalDiff a, Matrix.trace_mul_comm,
    trace_twoReplicaLocalSwapRaw_mul_diff]

theorem trace_conjTranspose_swapRaw_mul_diff (a : Fin 3) (x : Bool) :
    Matrix.trace ((twoReplicaLocalSwapRaw x)ᴴ * twoReplicaLocalDiff a) = 0 := by
  rw [isHermitian_twoReplicaLocalSwapRaw x, trace_twoReplicaLocalSwapRaw_mul_diff]

/-- The swap translate of a replica difference is Hilbert–Schmidt orthogonal to the local singlet
algebra. -/
theorem trace_conjTranspose_swapDiff_mul_swapRaw (a : Fin 3) (x : Bool) :
    Matrix.trace ((twoReplicaSwap * twoReplicaLocalDiff a)ᴴ * twoReplicaLocalSwapRaw x) = 0 := by
  rw [conjTranspose_swap_mul_twoReplicaLocalDiff a, Matrix.neg_mul, Matrix.trace_neg,
    Matrix.trace_mul_comm, trace_twoReplicaLocalSwapRaw_mul_swap_mul_diff, neg_zero]

theorem trace_conjTranspose_swapRaw_mul_swapDiff (a : Fin 3) (x : Bool) :
    Matrix.trace ((twoReplicaLocalSwapRaw x)ᴴ * (twoReplicaSwap * twoReplicaLocalDiff a)) = 0 := by
  rw [isHermitian_twoReplicaLocalSwapRaw x, trace_twoReplicaLocalSwapRaw_mul_swap_mul_diff]

/-- The two mismatched local outputs are Hilbert–Schmidt orthogonal to one another. -/
theorem trace_conjTranspose_diff_mul_swapDiff (a : Fin 3) :
    Matrix.trace ((twoReplicaLocalDiff a)ᴴ * (twoReplicaSwap * twoReplicaLocalDiff a)) = 0 := by
  rw [isHermitian_twoReplicaLocalDiff a, trace_twoReplicaLocalDiff_mul_swap_mul_diff]

theorem trace_conjTranspose_swapDiff_mul_diff (a : Fin 3) :
    Matrix.trace ((twoReplicaSwap * twoReplicaLocalDiff a)ᴴ * twoReplicaLocalDiff a) = 0 := by
  rw [Matrix.conjTranspose_mul, isHermitian_twoReplicaSwap, isHermitian_twoReplicaLocalDiff a,
    Matrix.mul_assoc, trace_twoReplicaLocalDiff_mul_swap_mul_diff]

end

end GaloisForLFunctions.HTGeometry
