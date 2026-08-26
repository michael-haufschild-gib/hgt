import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-!
# Graded trace determinant rigidity

Finite-dimensional signed power traces cannot move a divisor.  Schur triangulation turns all
power traces into power sums of diagonal spectral values, and power-sum Torelli identifies their
multisets.  Consequently equal power traces force equal ordinary determinants.

For a graded lift with even block `E`, odd block `O`, and source block `C`, the identity

`tr(E^m) - tr(O^m) = tr(C^m)`

for every degree therefore forces the cross-multiplied superdeterminant identity

`det(I - zE) = det(I - zC) det(I - zO)`.

Thus every source zero remains a zero of the even determinant.  No finite graded or Krein
polarization can simultaneously preserve all signed traces and move a nonreal source divisor onto
the real axis; real even divisors already imply real source divisors.
-/

open Complex Matrix Finset
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The first `n` power traces already determine `det(I + zM)` for `n × n` matrices. -/
theorem det_one_add_smul_eq_of_trace_pow_eq_le_fin {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ k : ℕ, k ≤ n → (M ^ k).trace = (N ^ k).trace) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + z • M).det =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + z • N).det := by
  obtain ⟨UM, TM, hUM1, hUM2, hTM, hMT⟩ := exists_schur_triangulation n M
  obtain ⟨UN, TN, hUN1, hUN2, hTN, hNT⟩ := exists_schur_triangulation n N
  have hp : ∀ k : ℕ, k ≤ n → ∑ i, (TM i i) ^ k = ∑ i, (TN i i) ^ k := by
    intro k hk
    rw [← trace_pow_eq_sum_diag hUM1 hUM2 hTM hMT k,
      ← trace_pow_eq_sum_diag hUN1 hUN2 hTN hNT k]
    exact htrace k hk
  have hmulti : univ.val.map (fun i => TM i i) =
      univ.val.map (fun i => TN i i) := by
    apply GaloisForLFunctions.powerSum_torelli_finite
    exact hp
  have hprod : ∏ i, (1 + z * TM i i) = ∏ i, (1 + z * TN i i) := by
    change (univ.val.map (fun i => 1 + z * TM i i)).prod =
      (univ.val.map (fun i => 1 + z * TN i i)).prod
    congr 1
    simpa [Multiset.map_map, Function.comp_def] using
      congrArg (Multiset.map (fun a : ℂ => 1 + z * a)) hmulti
  rw [det_one_add_smul_eq_prod hUM2 hTM hMT z,
    det_one_add_smul_eq_prod hUN2 hTN hNT z]
  exact hprod

/-- Equal power traces determine `det(I + zM)` for matrices indexed by `Fin n`. -/
theorem det_one_add_smul_eq_of_trace_pow_eq_fin {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ k : ℕ, (M ^ k).trace = (N ^ k).trace) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + z • M).det =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + z • N).det := by
  obtain ⟨UM, TM, hUM1, hUM2, hTM, hMT⟩ := exists_schur_triangulation n M
  obtain ⟨UN, TN, hUN1, hUN2, hTN, hNT⟩ := exists_schur_triangulation n N
  have hp : ∀ k : ℕ, ∑ i, (TM i i) ^ k = ∑ i, (TN i i) ^ k := by
    intro k
    rw [← trace_pow_eq_sum_diag hUM1 hUM2 hTM hMT k,
      ← trace_pow_eq_sum_diag hUN1 hUN2 hTN hNT k]
    exact htrace k
  have hmulti : univ.val.map (fun i => TM i i) =
      univ.val.map (fun i => TN i i) := by
    apply GaloisForLFunctions.powerSum_torelli
    exact hp
  have hprod : ∏ i, (1 + z * TM i i) = ∏ i, (1 + z * TN i i) := by
    change (univ.val.map (fun i => 1 + z * TM i i)).prod =
      (univ.val.map (fun i => 1 + z * TN i i)).prod
    congr 1
    simpa [Multiset.map_map, Function.comp_def] using
      congrArg (Multiset.map (fun a : ℂ => 1 + z * a)) hmulti
  rw [det_one_add_smul_eq_prod hUM2 hTM hMT z,
    det_one_add_smul_eq_prod hUN2 hTN hNT z]
  exact hprod

/-- The first `card ι` power traces determine `det(I + zM)` on any finite index type. -/
theorem det_one_add_smul_eq_of_trace_pow_eq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ)
    (htrace : ∀ k : ℕ, k ≤ Fintype.card ι → (M ^ k).trace = (N ^ k).trace)
    (z : ℂ) :
    ((1 : Matrix ι ι ℂ) + z • M).det =
      ((1 : Matrix ι ι ℂ) + z • N).det := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let MF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.reindex e e M
  let NF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.reindex e e N
  have htraceF : ∀ k : ℕ, k ≤ Fintype.card ι →
      (MF ^ k).trace = (NF ^ k).trace := by
    intro k hk
    calc
      (MF ^ k).trace = (M ^ k).trace := trace_pow_reindex e M k
      _ = (N ^ k).trace := htrace k hk
      _ = (NF ^ k).trace := (trace_pow_reindex e N k).symm
  have hfin := det_one_add_smul_eq_of_trace_pow_eq_le_fin MF NF htraceF z
  have hM : ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      z • MF).det = ((1 : Matrix ι ι ℂ) + z • M).det := by
    rw [show (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
        z • MF = ((1 : Matrix ι ι ℂ) + z • M).submatrix e.symm e.symm by
      ext i j
      simp [MF, e, Matrix.reindex_apply, Matrix.one_apply]]
    exact Matrix.det_submatrix_equiv_self e.symm _
  have hN : ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      z • NF).det = ((1 : Matrix ι ι ℂ) + z • N).det := by
    rw [show (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
        z • NF = ((1 : Matrix ι ι ℂ) + z • N).submatrix e.symm e.symm by
      ext i j
      simp [NF, e, Matrix.reindex_apply, Matrix.one_apply]]
    exact Matrix.det_submatrix_equiv_self e.symm _
  exact hM.symm.trans (hfin.trans hN)

/-- Equal power traces determine `det(I + zM)` on any finite index type. -/
theorem det_one_add_smul_eq_of_trace_pow_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ)
    (htrace : ∀ k : ℕ, (M ^ k).trace = (N ^ k).trace) (z : ℂ) :
    ((1 : Matrix ι ι ℂ) + z • M).det =
      ((1 : Matrix ι ι ℂ) + z • N).det := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let MF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.reindex e e M
  let NF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.reindex e e N
  have htraceF : ∀ k : ℕ, (MF ^ k).trace = (NF ^ k).trace := by
    intro k
    calc
      (MF ^ k).trace = (M ^ k).trace := trace_pow_reindex e M k
      _ = (N ^ k).trace := htrace k
      _ = (NF ^ k).trace := (trace_pow_reindex e N k).symm
  have hfin := det_one_add_smul_eq_of_trace_pow_eq_fin MF NF htraceF z
  have hM : ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      z • MF).det = ((1 : Matrix ι ι ℂ) + z • M).det := by
    rw [show (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
        z • MF = ((1 : Matrix ι ι ℂ) + z • M).submatrix e.symm e.symm by
      ext i j
      simp [MF, e, Matrix.reindex_apply, Matrix.one_apply]]
    exact Matrix.det_submatrix_equiv_self e.symm _
  have hN : ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      z • NF).det = ((1 : Matrix ι ι ℂ) + z • N).det := by
    rw [show (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
        z • NF = ((1 : Matrix ι ι ℂ) + z • N).submatrix e.symm e.symm by
      ext i j
      simp [NF, e, Matrix.reindex_apply, Matrix.one_apply]]
    exact Matrix.det_submatrix_equiv_self e.symm _
  exact hM.symm.trans (hfin.trans hN)

/-- Subtractive finite-window determinant rigidity. -/
theorem det_one_sub_smul_eq_of_trace_pow_eq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ)
    (htrace : ∀ k : ℕ, k ≤ Fintype.card ι → (M ^ k).trace = (N ^ k).trace)
    (z : ℂ) :
    ((1 : Matrix ι ι ℂ) - z • M).det =
      ((1 : Matrix ι ι ℂ) - z • N).det := by
  simpa [sub_eq_add_neg] using
    det_one_add_smul_eq_of_trace_pow_eq_le M N htrace (-z)

/-- Subtractive determinant form of finite power-trace rigidity. -/
theorem det_one_sub_smul_eq_of_trace_pow_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ)
    (htrace : ∀ k : ℕ, (M ^ k).trace = (N ^ k).trace) (z : ℂ) :
    ((1 : Matrix ι ι ℂ) - z • M).det =
      ((1 : Matrix ι ι ℂ) - z • N).det := by
  simpa [sub_eq_add_neg] using
    det_one_add_smul_eq_of_trace_pow_eq M N htrace (-z)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Block-diagonal carrier for source and odd spectra. -/
def gradedBlockDiagonal (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  Matrix.fromBlocks C 0 0 O

omit [DecidableEq ι] [DecidableEq κ] in
/-- Multiplication of two graded block-diagonal carriers is componentwise. -/
theorem gradedBlockDiagonal_mul
    (A B : Matrix ι ι ℂ) (D E : Matrix κ κ ℂ) :
    gradedBlockDiagonal A D * gradedBlockDiagonal B E =
      gradedBlockDiagonal (A * B) (D * E) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gradedBlockDiagonal, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Powers of a graded block-diagonal carrier are componentwise. -/
theorem gradedBlockDiagonal_pow (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (m : ℕ) :
    (gradedBlockDiagonal C O) ^ m = gradedBlockDiagonal (C ^ m) (O ^ m) := by
  induction m with
  | zero =>
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [gradedBlockDiagonal, Matrix.one_apply]
  | succ m ih =>
      rw [pow_succ, ih, gradedBlockDiagonal_mul, pow_succ, pow_succ]

/-- Trace powers of a graded block diagonal are the sum of block trace powers. -/
theorem gradedBlockDiagonal_trace_pow
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ) (m : ℕ) :
    ((gradedBlockDiagonal C O) ^ m).trace =
      (C ^ m).trace + (O ^ m).trace := by
  rw [gradedBlockDiagonal_pow]
  simp [gradedBlockDiagonal, Matrix.trace, Fintype.sum_sum_type]

/-- Ordinary determinant of a graded block diagonal is the product of block determinants. -/
theorem gradedBlockDiagonal_det_one_sub
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ) (z : ℂ) :
    ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) -
        z • gradedBlockDiagonal C O).det =
      ((1 : Matrix ι ι ℂ) - z • C).det *
        ((1 : Matrix κ κ ℂ) - z • O).det := by
  have hblock : (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) -
      z • gradedBlockDiagonal C O =
      Matrix.fromBlocks ((1 : Matrix ι ι ℂ) - z • C) 0 0
        ((1 : Matrix κ κ ℂ) - z • O) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [gradedBlockDiagonal, Matrix.one_apply]
  rw [hblock]
  exact Matrix.det_fromBlocks_zero₁₂ _ _ _

/-- **Finite-window signed-trace rigidity.** Signed traces only through the total even rank
already force the complete determinant factorization. -/
theorem graded_signedTrace_preservation_le_forces_det_factor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ m : ℕ, m ≤ Fintype.card (ι ⊕ κ) →
      (E ^ m).trace - (O ^ m).trace = (C ^ m).trace)
    (z : ℂ) :
    ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det =
      ((1 : Matrix ι ι ℂ) - z • C).det *
        ((1 : Matrix κ κ ℂ) - z • O).det := by
  have htrace' : ∀ m : ℕ, m ≤ Fintype.card (ι ⊕ κ) → (E ^ m).trace =
      ((gradedBlockDiagonal C O) ^ m).trace := by
    intro m hm
    rw [gradedBlockDiagonal_trace_pow]
    exact sub_eq_iff_eq_add.mp (htrace m hm)
  rw [det_one_sub_smul_eq_of_trace_pow_eq_le E (gradedBlockDiagonal C O) htrace' z]
  exact gradedBlockDiagonal_det_one_sub C O z

/-- **Signed-trace determinant rigidity.** Exact supertraces force exact determinant
factorization.  This is the cross-multiplied finite superdeterminant identity. -/
theorem graded_signedTrace_preservation_forces_det_factor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ m : ℕ, (E ^ m).trace - (O ^ m).trace = (C ^ m).trace)
    (z : ℂ) :
    ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det =
      ((1 : Matrix ι ι ℂ) - z • C).det *
        ((1 : Matrix κ κ ℂ) - z • O).det := by
  have htrace' : ∀ m : ℕ, (E ^ m).trace =
      ((gradedBlockDiagonal C O) ^ m).trace := by
    intro m
    rw [gradedBlockDiagonal_trace_pow]
    exact sub_eq_iff_eq_add.mp (htrace m)
  rw [det_one_sub_smul_eq_of_trace_pow_eq E (gradedBlockDiagonal C O) htrace' z]
  exact gradedBlockDiagonal_det_one_sub C O z

/-- A real even divisor already locks the source divisor when signed traces are preserved only
through the total even rank. -/
theorem source_realDivisor_of_graded_signedTrace_le_realDivisor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ m : ℕ, m ≤ Fintype.card (ι ⊕ κ) →
      (E ^ m).trace - (O ^ m).trace = (C ^ m).trace)
    (hreal : ∀ z : ℂ,
      ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det = 0 → z.im = 0)
    {z : ℂ} (hz : ((1 : Matrix ι ι ℂ) - z • C).det = 0) :
    z.im = 0 := by
  apply hreal z
  rw [graded_signedTrace_preservation_le_forces_det_factor C O E htrace z, hz, zero_mul]

/-- A real even divisor in an exact signed-trace lift forces the source divisor itself to be real. -/
theorem source_realDivisor_of_graded_signedTrace_realDivisor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ m : ℕ, (E ^ m).trace - (O ^ m).trace = (C ^ m).trace)
    (hreal : ∀ z : ℂ,
      ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det = 0 → z.im = 0)
    {z : ℂ} (hz : ((1 : Matrix ι ι ℂ) - z • C).det = 0) :
    z.im = 0 := by
  apply hreal z
  rw [graded_signedTrace_preservation_forces_det_factor C O E htrace z, hz, zero_mul]

end

end GaloisForLFunctions.HTGeometry
