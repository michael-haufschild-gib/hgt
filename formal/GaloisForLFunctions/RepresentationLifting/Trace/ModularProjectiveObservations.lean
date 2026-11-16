import GaloisForLFunctions.RepresentationLifting.Trace.ProjectiveTraceDuality
import GaloisForLFunctions.RepresentationLifting.ModularTrace

/-!
# Projective observations of modular convolution and dual-number operators

Scalar trace can vanish on an entire regular representation or dual-number
centralizer. Pairing with all trace-zero matrices loses precisely the scalar
identity direction. For convolution this leaves every nonidentity coefficient;
for dual numbers it leaves the entire extension block and the projective
diagonal block.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {R ι G : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  [Group G] [Fintype G] [DecidableEq G]

omit [Fintype ι] [Fintype G] in
/-- A regular convolution matrix is scalar exactly when its kernels are the
same delta mass on each diagonal copy and vanish everywhere else. -/
theorem regularKernelMatrix_eq_scalar_iff (K : ι → ι → G → R) (c : R) :
    regularKernelMatrix K = c • (1 : Matrix (ι × G) (ι × G) R) ↔
      ∀ i j g, K i j g = if i = j ∧ g = 1 then c else 0 := by
  constructor
  · intro h i j g
    have he := congrArg (fun M => M (i, 1) (j, g)) h
    simpa [regularKernelMatrix, Matrix.one_apply, eq_comm] using he
  · intro h
    ext x y
    have hxy : x.2⁻¹ * y.2 = 1 ↔ x.2 = y.2 := by
      constructor
      · intro he
        have hm := congrArg (fun z => x.2 * z) he
        simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hm.symm
      · intro he
        rw [he, inv_mul_cancel]
    simp [regularKernelMatrix, h, Matrix.one_apply, Prod.ext_iff, hxy]

/-- The full ambiguity of trace-zero observations on regular convolution kernels. -/
theorem regularKernelMatrix_traceZero_annihilator_iff (p : ι)
    (K : ι → ι → G → R) :
    (∀ B : traceZeroMatrices R (ι × G), (regularKernelMatrix K * B.val).trace = 0) ↔
      ∃ c : R, ∀ i j g, K i j g = if i = j ∧ g = 1 then c else 0 := by
  rw [traceZero_annihilator_iff (p, 1)]
  exact exists_congr fun c => regularKernelMatrix_eq_scalar_iff K c

omit [Group G] [Fintype G] [DecidableEq G] [Fintype ι] in
/-- Scalar repeated triangular blocks have no extension block. -/
theorem dualNumberBlock_eq_scalar_iff (A D : Matrix ι ι R) (c : R) :
    Matrix.fromBlocks A D 0 A = c • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) ↔
      A = c • (1 : Matrix ι ι R) ∧ D = 0 := by
  constructor
  · intro h
    constructor
    · ext i j
      simpa [Matrix.one_apply] using congrArg (fun M => M (Sum.inl i) (Sum.inl j)) h
    · ext i j
      simpa using congrArg (fun M => M (Sum.inl i) (Sum.inr j)) h
  · rintro ⟨rfl, rfl⟩
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Trace-zero tests recover every extension entry and the diagonal block modulo scalars. -/
theorem dualNumberBlock_traceZero_annihilator_iff (p : ι) (A D : Matrix ι ι R) :
    (∀ B : traceZeroMatrices R (ι ⊕ ι),
      (Matrix.fromBlocks A D 0 A * B.val).trace = 0) ↔
      ∃ c : R, A = c • (1 : Matrix ι ι R) ∧ D = 0 := by
  rw [traceZero_annihilator_iff (Sum.inl p)]
  exact exists_congr fun c => dualNumberBlock_eq_scalar_iff A D c

#print axioms regularKernelMatrix_traceZero_annihilator_iff
#print axioms dualNumberBlock_traceZero_annihilator_iff

end GaloisForLFunctions.RepresentationLifting
