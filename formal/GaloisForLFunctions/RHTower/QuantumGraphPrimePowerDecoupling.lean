import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Prime-power supported unitary scattering decouples

Let `σ` be a unitary matrix on a finite index set `β` (the directed bonds of a metric graph), and
let `blk : β → ι` group the bonds into blocks (the two orientations of each edge).  Write `σ_e` for
the principal block of `σ` on the bonds labelled `e`.

**Theorem** (`eq_zero_of_det_eq_prod_principalBlock`).  If `det σ = ∏_e det σ_e`, then `σ` is block
diagonal: `σ i j = 0` whenever `blk i ≠ blk j`.

**Theorem** (`eq_zero_of_secular_eq_prod`).  If the secular determinant factors over the blocks,
`det(1 − σ·diag(z_{blk j})) = ∏_e det(1 − σ_e·diag(z_e))` for every `z : ι → ℂ`, then `σ` is block
diagonal.  Already the specialization `z ≡ t`, i.e. `det(1 − tσ) = ∏_e det(1 − tσ_e)` for all `t`
(the spectrum of `σ` with multiplicity is the union of the spectra of its diagonal blocks), forces
it (`eq_zero_of_det_one_sub_smul_eq_prod`).

**Theorem** (`eq_zero_of_isHermitian_det_one_sub_smul_eq_prod`).  The same holds for Hermitian `σ`
(self-adjoint transfer or discrete Schrödinger models).  Multiplying the identity at `t` and `−t`
gives `det(1 + uσ²) = ∏_e det(1 + uσ_e²)` for every `u`.  Comparing first coefficients gives
`tr σ² = ∑_e tr σ_e²` (`trace_mul_self_eq_sum_of_det_one_sub_smul_eq_prod`).  For Hermitian `σ`
these traces are the squared Frobenius norms, so every cross-block entry vanishes.

**Reading for the explicit formula.**  For a quantum graph with bond scattering matrix `σ` and edge
lengths `L_e`, the oscillatory part of the trace formula is the expansion
`log det(1 − σ D(z)) = −Σ_m Tr((σD(z))^m)/m`, `D(z) = diag(z_{blk b})`, `z_e = e^{ikL_e}`: the
coefficient of `z^α` is the amplitude of all periodic orbits that traverse edge `e` exactly `α_e`
times, and has length `Σ α_e L_e`.  If the lengths are linearly independent over `ℚ` (as the
`log p` are), the trace formula is supported on single-edge multiples `m L_e` exactly when
`log det(1 − σD(z))` has no mixed monomial, i.e. when the secular determinant factors over the
edges.  For the explicit formula of `ζ` this is forced by `Λ(n) = 0` off prime powers.  The theorem
then says that the vertex couplings transmit nothing between distinct edges, so the spectrum is the
union of the single-edge lattices; a unitary quantum graph cannot realize the prime side of the
explicit formula with interacting edges.

**Proof.**  For unitary `σ`, `|det σ| = 1` and every column has norm one.  By Hadamard's inequality
`|det σ_e| ≤ ∏_{j ∈ e} c_j`, where `c_j ≤ 1` is the norm of column `j` restricted to its own block.
Hence `1 = ∏_e |det σ_e| ≤ ∏_j c_j ≤ 1`, so every `c_j = 1` and the off-block part of every column
vanishes.  For the secular form, `det(t·1 − σ) = t^{|β|} det(1 − t⁻¹σ)` turns the identity into
`det(t·1 − σ) = ∏_e det(t·1 − σ_e)` for `t ≠ 0`, continuity extends it to `t = 0`, and
`det(−σ) = (−1)^{|β|} det σ` gives `det σ = ∏_e det σ_e`.
-/

open Matrix Finset

noncomputable section

namespace RHTower.QuantumGraphPrimePowerDecoupling

variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- The principal block of `σ` on the indices labelled `e`. -/
def principalBlock (σ : Matrix β β ℂ) (blk : β → ι) (e : ι) :
    Matrix {j // blk j = e} {j // blk j = e} ℂ :=
  σ.submatrix Subtype.val Subtype.val

/-- The norm of column `j` of `σ` restricted to the rows of the block of `j`. -/
def blockColumnNorm (σ : Matrix β β ℂ) (blk : β → ι) (j : β) : ℝ :=
  Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = blk j), ‖σ i j‖ ^ 2)

/-- Every column of a unitary matrix has norm one. -/
theorem sum_norm_sq_col_eq_one {σ : Matrix β β ℂ} (hσ : σ ∈ unitaryGroup β ℂ) (j : β) :
    ∑ i, ‖σ i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hσ) j) j
  rw [star_eq_conjTranspose, mul_apply, one_apply_eq] at h
  have h' : ((∑ i, ‖σ i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h, Complex.ofReal_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  exact_mod_cast h'

omit [Fintype ι] in
/-- **Hadamard's inequality on a principal block.** -/
theorem norm_det_principalBlock_le (σ : Matrix β β ℂ) (blk : β → ι) (e : ι) :
    ‖(principalBlock σ blk e).det‖ ≤
      ∏ j : {j // blk j = e}, Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = e), ‖σ i j‖ ^ 2) := by
  set κ := {j // blk j = e}
  let eqv := Fintype.equivFin κ
  let A : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card κ)) ℂ :=
    (principalBlock σ blk e).submatrix eqv.symm eqv.symm
  have hdet : A.det = (principalBlock σ blk e).det := det_submatrix_equiv_self eqv.symm _
  have hcol : ∀ b, ‖(WithLp.toLp 2 fun a => A a b : EuclideanSpace ℂ _)‖ =
      Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = e), ‖σ i (eqv.symm b).1‖ ^ 2) := by
    intro b
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp only [A, principalBlock, submatrix_apply]
    rw [Equiv.sum_comp eqv.symm (fun a : κ => ‖σ a.1 (eqv.symm b).1‖ ^ 2)]
    exact (sum_subtype (univ.filter (fun i => blk i = e)) (by simp)
      (fun i => ‖σ i (eqv.symm b).1‖ ^ 2)).symm
  calc ‖(principalBlock σ blk e).det‖ = ‖A.det‖ := by rw [hdet]
    _ ≤ ∏ b, ‖(WithLp.toLp 2 fun a => A a b : EuclideanSpace ℂ _)‖ :=
      ContinuousKernelFredholm.complex_hadamard_column_bound A
    _ = ∏ b, Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = e), ‖σ i (eqv.symm b).1‖ ^ 2) :=
      prod_congr rfl fun b _ => hcol b
    _ = ∏ j : κ, Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = e), ‖σ i j‖ ^ 2) :=
      Equiv.prod_comp eqv.symm (fun j : κ =>
        Real.sqrt (∑ i ∈ univ.filter (fun i => blk i = e), ‖σ i j.1‖ ^ 2))

omit [Fintype ι] in
theorem blockColumnNorm_le_one {σ : Matrix β β ℂ} (hσ : σ ∈ unitaryGroup β ℂ) (blk : β → ι)
    (j : β) : blockColumnNorm σ blk j ≤ 1 := by
  unfold blockColumnNorm
  rw [Real.sqrt_le_one]
  calc ∑ i ∈ univ.filter (fun i => blk i = blk j), ‖σ i j‖ ^ 2 ≤ ∑ i, ‖σ i j‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = 1 := sum_norm_sq_col_eq_one hσ j

/-- **Block rigidity.**  A unitary matrix whose determinant is the product of the determinants of its
principal blocks is block diagonal. -/
theorem eq_zero_of_det_eq_prod_principalBlock {σ : Matrix β β ℂ} (hσ : σ ∈ unitaryGroup β ℂ)
    (blk : β → ι) (hdet : σ.det = ∏ e, (principalBlock σ blk e).det) {i j : β}
    (hij : blk i ≠ blk j) : σ i j = 0 := by
  have hc0 : ∀ k, 0 ≤ blockColumnNorm σ blk k := fun k => Real.sqrt_nonneg _
  have hc1 := blockColumnNorm_le_one hσ blk
  have hone : ‖σ.det‖ = 1 := CStarRing.norm_of_mem_unitary (det_of_mem_unitary hσ)
  have hprod : 1 ≤ ∏ k, blockColumnNorm σ blk k := by
    calc (1 : ℝ) = ‖σ.det‖ := hone.symm
      _ = ∏ e, ‖(principalBlock σ blk e).det‖ := by rw [hdet, norm_prod]
      _ ≤ ∏ e, ∏ k : {k // blk k = e}, blockColumnNorm σ blk k := by
        refine prod_le_prod (fun _ _ => norm_nonneg _) fun e _ => ?_
        refine (norm_det_principalBlock_le σ blk e).trans (le_of_eq ?_)
        refine prod_congr rfl fun k _ => ?_
        unfold blockColumnNorm
        rw [k.2]
      _ = ∏ k, blockColumnNorm σ blk k := Fintype.prod_fiberwise blk _
  have hj : blockColumnNorm σ blk j = 1 := by
    refine le_antisymm (hc1 j) ?_
    calc (1 : ℝ) ≤ ∏ k, blockColumnNorm σ blk k := hprod
      _ = blockColumnNorm σ blk j * ∏ k ∈ univ.erase j, blockColumnNorm σ blk k :=
        (mul_prod_erase univ _ (mem_univ j)).symm
      _ ≤ blockColumnNorm σ blk j * 1 :=
        mul_le_mul_of_nonneg_left (prod_le_one (fun k _ => hc0 k) fun k _ => hc1 k) (hc0 j)
      _ = blockColumnNorm σ blk j := mul_one _
  have hin : ∑ k ∈ univ.filter (fun k => blk k = blk j), ‖σ k j‖ ^ 2 = 1 := by
    have h := hj
    unfold blockColumnNorm at h
    rwa [Real.sqrt_eq_one] at h
  have hout : ∑ k ∈ univ.filter (fun k => ¬ blk k = blk j), ‖σ k j‖ ^ 2 = 0 := by
    have h := sum_filter_add_sum_filter_not univ (fun k => blk k = blk j) (fun k => ‖σ k j‖ ^ 2)
    rw [hin, sum_norm_sq_col_eq_one hσ j] at h
    linarith
  have hterm := (sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp hout i
    (mem_filter.mpr ⟨mem_univ i, hij⟩)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hterm)

omit [DecidableEq β] in
theorem card_eq_sum_card_block (blk : β → ι) :
    Fintype.card β = ∑ e, Fintype.card {j // blk j = e} := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := blk) (t := univ) (fun _ _ => mem_coe.mpr
    (mem_univ _))]
  refine sum_congr rfl fun e _ => ?_
  rw [Fintype.card_subtype]

/-- The characteristic determinants factor once the reversed secular determinants do. -/
theorem det_smul_one_sub_eq_prod {σ : Matrix β β ℂ} (blk : β → ι)
    (h : ∀ t : ℂ, (1 - t • σ).det = ∏ e, (1 - t • principalBlock σ blk e).det) (t : ℂ) :
    (t • (1 : Matrix β β ℂ) - σ).det = ∏ e, (t • (1 : Matrix _ _ ℂ) - principalBlock σ blk e).det := by
  have hcont : ∀ (κ : Type _) [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ),
      Continuous fun t : ℂ => (t • (1 : Matrix κ κ ℂ) - M).det := fun κ _ _ M =>
    (continuous_id.smul continuous_const |>.sub continuous_const).matrix_det
  have hLR : (fun t : ℂ => (t • (1 : Matrix β β ℂ) - σ).det) =
      fun t => ∏ e, (t • (1 : Matrix _ _ ℂ) - principalBlock σ blk e).det := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (hcont β σ)
      (continuous_finsetProd _ fun e _ => hcont _ _) ?_
    intro s hs
    have hs0 : s ≠ 0 := hs
    have hsplit : ∀ (κ : Type _) [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ),
        (s • (1 : Matrix κ κ ℂ) - M).det = s ^ Fintype.card κ * (1 - s⁻¹ • M).det := by
      intro κ _ _ M
      rw [← det_smul, smul_sub, smul_smul, mul_inv_cancel₀ hs0, one_smul]
    simp only
    rw [hsplit, h, card_eq_sum_card_block blk, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun e _ => (hsplit _ _).symm
  exact congrFun hLR t

/-- **Spectral rigidity.**  If `det(1 − tσ) = ∏_e det(1 − tσ_e)` for every `t`, a unitary `σ` is block
diagonal. -/
theorem eq_zero_of_det_one_sub_smul_eq_prod {σ : Matrix β β ℂ} (hσ : σ ∈ unitaryGroup β ℂ)
    (blk : β → ι) (h : ∀ t : ℂ, (1 - t • σ).det = ∏ e, (1 - t • principalBlock σ blk e).det)
    {i j : β} (hij : blk i ≠ blk j) : σ i j = 0 := by
  refine eq_zero_of_det_eq_prod_principalBlock hσ blk ?_ hij
  have h0 := det_smul_one_sub_eq_prod blk h 0
  simp only [zero_smul, zero_sub, det_neg] at h0
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, ← card_eq_sum_card_block blk] at h0
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0

/-- **Secular rigidity.**  If the secular determinant `det(1 − σ·diag(z_{blk j}))` factors over the
blocks for every `z`, a unitary `σ` is block diagonal. -/
theorem eq_zero_of_secular_eq_prod {σ : Matrix β β ℂ} (hσ : σ ∈ unitaryGroup β ℂ) (blk : β → ι)
    (h : ∀ z : ι → ℂ, (1 - σ * diagonal fun j => z (blk j)).det =
      ∏ e, (1 - principalBlock σ blk e * diagonal fun _ => z e).det)
    {i j : β} (hij : blk i ≠ blk j) : σ i j = 0 := by
  refine eq_zero_of_det_one_sub_smul_eq_prod hσ blk (fun t => ?_) hij
  have ht := h fun _ => t
  have hd : ∀ (κ : Type _) [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ),
      M * diagonal (fun _ => t) = t • M := fun κ _ _ M => by
    ext a b
    simp [mul_diagonal, mul_comm]
  rw [hd β σ] at ht
  rw [ht]
  exact prod_congr rfl fun e _ => by rw [hd]

/-! ### Hermitian transfer matrices -/

theorem eval_det_one_add_X_smul {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ)
    (r : ℂ) :
    (det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).eval r = (1 + r • A).det := by
  rw [det_one_add_smul r A]
  conv_lhs => rw [det_one_add_X_smul A]
  simp [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
    mul_comm]

theorem coeff_prod_of_coeff_zero_eq_one {α : Type*} (s : Finset α) (f : α → Polynomial ℂ)
    (hf : ∀ a, (f a).coeff 0 = 1) :
    (∏ a ∈ s, f a).coeff 0 = 1 ∧ (∏ a ∈ s, f a).coeff 1 = ∑ a ∈ s, (f a).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one, hf a,
      ih.1, ih.2]
    exact ⟨one_mul 1, by ring⟩

/-- **Trace law.**  If the spectrum of `σ` with multiplicity is the union of the spectra of its
principal blocks, then `tr σ² = ∑_e tr σ_e²`. -/
theorem trace_mul_self_eq_sum_of_det_one_sub_smul_eq_prod {σ : Matrix β β ℂ} (blk : β → ι)
    (h : ∀ t : ℂ, (1 - t • σ).det = ∏ e, (1 - t • principalBlock σ blk e).det) :
    (σ * σ).trace = ∑ e, (principalBlock σ blk e * principalBlock σ blk e).trace := by
  have hfac : ∀ (κ : Type _) [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) (t : ℂ),
      (1 - t • M) * (1 - (-t) • M) = 1 + (-(t * t)) • (M * M) := by
    intro κ _ _ M t
    have hm : (t • M) * ((-t) • M) = (-(t * t)) • (M * M) := by
      rw [smul_mul_smul_comm, mul_neg]
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hm]
    simp only [neg_smul]
    abel
  have hsq : ∀ u : ℂ, (1 + u • (σ * σ)).det =
      ∏ e, (1 + u • (principalBlock σ blk e * principalBlock σ blk e)).det := by
    intro u
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_eq_mul_self (-u)
    have hu : u = -(t * t) := by rw [← ht, neg_neg]
    rw [hu, ← hfac β σ t, det_mul, h t, h (-t), ← prod_mul_distrib]
    exact prod_congr rfl fun e _ => by rw [← det_mul, hfac]
  set P : ι → Polynomial ℂ := fun e => det (1 + (Polynomial.X : Polynomial ℂ) •
    (principalBlock σ blk e * principalBlock σ blk e).map Polynomial.C)
  have hpoly : det (1 + (Polynomial.X : Polynomial ℂ) • (σ * σ).map Polynomial.C) = ∏ e, P e := by
    refine Polynomial.funext fun r => ?_
    rw [eval_det_one_add_X_smul, Polynomial.eval_prod, hsq r]
    exact prod_congr rfl fun e _ => (eval_det_one_add_X_smul _ r).symm
  have h0 : ∀ e, (P e).coeff 0 = 1 := fun e => by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_det_one_add_X_smul, zero_smul, add_zero, det_one]
  rw [← coeff_det_one_add_X_smul_one, hpoly, (coeff_prod_of_coeff_zero_eq_one univ P h0).2]
  exact sum_congr rfl fun e _ => coeff_det_one_add_X_smul_one _

theorem trace_mul_self_eq_sum_normSq_of_isHermitian {κ : Type*} [Fintype κ]
    {M : Matrix κ κ ℂ} (hM : M.IsHermitian) :
    (M * M).trace = ((∑ i, ∑ j, Complex.normSq (M i j) : ℝ) : ℂ) := by
  rw [trace]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [diag_apply, mul_apply]
  refine sum_congr rfl fun j _ => ?_
  have hji : M j i = star (M i j) := (hM.apply j i).symm
  rw [hji, Complex.star_def, Complex.mul_conj]

/-- **Hermitian rigidity.**  If the spectrum of a Hermitian `σ` with multiplicity is the union of the
spectra of its principal blocks, `σ` is block diagonal.  This covers self-adjoint transfer
(discrete Schrödinger) models. -/
theorem eq_zero_of_isHermitian_det_one_sub_smul_eq_prod {σ : Matrix β β ℂ} (hσ : σ.IsHermitian)
    (blk : β → ι) (h : ∀ t : ℂ, (1 - t • σ).det = ∏ e, (1 - t • principalBlock σ blk e).det)
    {i j : β} (hij : blk i ≠ blk j) : σ i j = 0 := by
  have hblk : ∀ e, (principalBlock σ blk e).IsHermitian := fun e =>
    hσ.submatrix Subtype.val
  have htr := trace_mul_self_eq_sum_of_det_one_sub_smul_eq_prod blk h
  rw [trace_mul_self_eq_sum_normSq_of_isHermitian hσ] at htr
  simp_rw [trace_mul_self_eq_sum_normSq_of_isHermitian (hblk _)] at htr
  rw [← Complex.ofReal_sum, Complex.ofReal_inj] at htr
  set f : β → β → ℝ := fun a b => Complex.normSq (σ a b)
  have hf0 : ∀ a b, 0 ≤ f a b := fun a b => Complex.normSq_nonneg _
  have hRHS : ∑ e, ∑ a : {a // blk a = e}, ∑ b : {b // blk b = e},
      Complex.normSq (principalBlock σ blk e a b) =
      ∑ a, ∑ b ∈ univ.filter (fun b => blk b = blk a), f a b := by
    have hinner : ∀ e (a : {a // blk a = e}), ∑ b : {b // blk b = e},
        Complex.normSq (principalBlock σ blk e a b) =
        ∑ b ∈ univ.filter (fun b => blk b = blk a.1), f a.1 b := by
      intro e a
      rw [a.2]
      exact (sum_subtype (univ.filter (fun b => blk b = e)) (by simp) (fun b => f a.1 b)).symm
    simp_rw [hinner]
    exact Fintype.sum_fiberwise blk (fun a => ∑ b ∈ univ.filter (fun b => blk b = blk a), f a b)
  have htr2 : ∑ a, ∑ b, f a b = ∑ a, ∑ b ∈ univ.filter (fun b => blk b = blk a), f a b :=
    htr.trans hRHS
  have hsplit : ∀ a ∈ univ, ∑ b, f a b = ∑ b ∈ univ.filter (fun b => blk b = blk a), f a b +
      ∑ b ∈ univ.filter (fun b => ¬ blk b = blk a), f a b := fun a _ =>
    (sum_filter_add_sum_filter_not univ _ _).symm
  rw [sum_congr rfl hsplit, sum_add_distrib] at htr2
  have hout : ∑ a, ∑ b ∈ univ.filter (fun b => ¬ blk b = blk a), f a b = 0 := by linarith
  have hrow := (sum_eq_zero_iff_of_nonneg fun a _ => sum_nonneg fun b _ => hf0 a b).mp hout i
    (mem_univ i)
  have hterm := (sum_eq_zero_iff_of_nonneg fun b _ => hf0 i b).mp hrow j
    (mem_filter.mpr ⟨mem_univ j, fun hji => hij hji.symm⟩)
  exact Complex.normSq_eq_zero.mp hterm

end RHTower.QuantumGraphPrimePowerDecoupling
