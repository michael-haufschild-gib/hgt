/-
# Unitary triangulation of a complex square matrix

Every complex square matrix is unitarily equivalent to an upper-triangular matrix: `Uᴴ M U = T`
with `U` unitary and `T` upper triangular.  Mathlib has the block-triangular predicate and the
determinant of a triangular matrix, but not this decomposition.

The proof is the classical induction on the size.  A matrix of positive size has an eigenvector,
because its characteristic polynomial has a root; normalizing that eigenvector and extending it to
an orthonormal basis produces a unitary `U` whose first column is the eigenvector, so that
`Uᴴ M U` has first column `(μ, 0, …, 0)`.  The lower-right block is triangulated by the induction
hypothesis and embedded back as `1 ⊕ V`.

Main results:
* `exists_eigenpair` — a complex matrix of positive size has an eigenvector.
* `exists_unitary_firstColumn` — a unit vector is the first column of a unitary matrix.
* `exists_schur_triangulation` — `Uᴴ M U = T`, `U` unitary, `T` upper triangular.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

variable {n : ℕ}

/-- **Existence of an eigenvector.**  A complex square matrix of positive size has a nonzero
vector `v` with `M v = μ v`: the characteristic polynomial has positive degree, hence a root `μ`,
and then `μ • 1 - M` is singular. -/
theorem exists_eigenpair (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (μ : ℂ) (v : Fin (n + 1) → ℂ), v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have hmonic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hdegnat : M.charpoly.natDegree = n + 1 := by
    simp [Matrix.charpoly_natDegree_eq_dim M]
  have hdeg : 0 < M.charpoly.degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegnat]
    exact_mod_cast Nat.succ_pos n
  obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
  have hdet : ((Matrix.scalar (Fin (n + 1))) μ - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨μ, v, hv0, ?_⟩
  have hs : ((Matrix.scalar (Fin (n + 1))) μ) *ᵥ v = μ • v := by
    ext i
    simp [Matrix.scalar, Matrix.mulVec, Matrix.diagonal, dotProduct]
  rw [Matrix.sub_mulVec, hs] at hv
  exact (sub_eq_zero.mp hv).symm

/-- **A unit vector is the first column of a unitary matrix.**  Extend it to an orthonormal basis
and use the basis vectors as columns. -/
theorem exists_unitary_firstColumn (w : Fin (n + 1) → ℂ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin (n + 1)))‖ = 1) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i, U i 0 = w i := by
  classical
  set wE : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 w with hwE
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Fintype.card (Fin (n + 1)) := by
    simp
  have horth :
      Orthonormal ℂ (Set.restrict ({0} : Set (Fin (n + 1))) (fun _ : Fin (n + 1) => wE)) := by
    constructor
    · intro i; simpa using hw
    · intro i j hij
      exact absurd (Subtype.ext (i.2.trans j.2.symm)) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b 0 = wE := hb 0 rfl
  have hite : ∀ j k, inner ℂ (b j) (b k) = if j = k then (1 : ℂ) else 0 :=
    fun j k => orthonormal_iff_ite.mp b.orthonormal j k
  have hcol : ∀ j k : Fin (n + 1),
      ∑ i, (starRingEnd ℂ) ((b j).ofLp i) * (b k).ofLp i = if j = k then (1 : ℂ) else 0 := by
    intro j k
    rw [← hite j k, PiLp.inner_apply]
    exact (Finset.sum_congr rfl fun i _ => (RCLike.inner_apply' _ _)).symm
  have hUU : (Matrix.of fun i j => (b j).ofLp i : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ *
      (Matrix.of fun i j => (b j).ofLp i) = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.star_def]
    exact hcol j k
  exact ⟨_, hUU, mul_eq_one_comm.mp hUU, fun i => by simp [hb0, hwE]⟩

/-- The embedding `V ↦ 1 ⊕ V` of an `n × n` matrix as the lower-right block of an
`(n+1) × (n+1)` matrix. -/
def embedSucc (V : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases (1 : ℂ) (fun _ => 0) j) (fun i' => Fin.cases (0 : ℂ) (V i') j) i

@[simp] theorem embedSucc_zero_zero (V : Matrix (Fin n) (Fin n) ℂ) : embedSucc V 0 0 = 1 := rfl

@[simp] theorem embedSucc_zero_succ (V : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    embedSucc V 0 j.succ = 0 := rfl

@[simp] theorem embedSucc_succ_zero (V : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    embedSucc V i.succ 0 = 0 := rfl

@[simp] theorem embedSucc_succ_succ (V : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    embedSucc V i.succ j.succ = V i j := rfl

theorem embedSucc_conjTranspose_mul_self {V : Matrix (Fin n) (Fin n) ℂ} (hV : Vᴴ * V = 1) :
    (embedSucc V)ᴴ * embedSucc V = 1 := by
  have hV' : ∀ i j : Fin n, ∑ k, (starRingEnd ℂ) (V k i) * V k j = if i = j then 1 else 0 := by
    intro i j
    have := congrArg (fun A => A i j) hV
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def]
      using this
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def,
    Fin.sum_univ_succ]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp
    | succ j' => simp [eq_comm, Fin.succ_ne_zero]
  | succ i' =>
    induction j using Fin.cases with
    | zero => simp
    | succ j' => simp [hV' i' j', Fin.succ_inj]

theorem embedSucc_mul_conjTranspose_self {V : Matrix (Fin n) (Fin n) ℂ} (hV : Vᴴ * V = 1) :
    embedSucc V * (embedSucc V)ᴴ = 1 :=
  mul_eq_one_comm.mp (embedSucc_conjTranspose_mul_self hV)

/-- **Schur triangulation.**  Every complex square matrix is unitarily conjugate to an
upper-triangular matrix. -/
theorem exists_schur_triangulation :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ),
      ∃ U T : Matrix (Fin n) (Fin n) ℂ,
        Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ T.BlockTriangular id ∧ Uᴴ * M * U = T := by
  intro n
  induction n with
  | zero =>
    intro M
    exact ⟨1, 0, by simp, by simp, blockTriangular_zero, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro M
    obtain ⟨μ, v, hv0, hv⟩ := exists_eigenpair M
    set E := EuclideanSpace ℂ (Fin (n + 1)) with hE
    set vE : E := WithLp.toLp 2 v with hvE
    have hvE0 : vE ≠ 0 := fun h => hv0 (by simpa [hvE] using congrArg (fun x : E => x.ofLp) h)
    set w : Fin (n + 1) → ℂ := ‖vE‖⁻¹ • v with hwdef
    have hwnorm : ‖(WithLp.toLp 2 w : E)‖ = 1 := by
      have hcast : (WithLp.toLp 2 w : E) = ‖vE‖⁻¹ • vE := rfl
      rw [hcast]
      exact norm_smul_inv_norm hvE0
    obtain ⟨U, hU1, hU2, hUcol⟩ := exists_unitary_firstColumn w hwnorm
    have hMw : M *ᵥ w = μ • w := by
      rw [hwdef, Matrix.mulVec_smul, hv, smul_comm]
    set N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Uᴴ * M * U with hN
    have hMU : ∀ k, (M * U) k 0 = μ * w k := by
      intro k
      have h1 : (M * U) k 0 = (M *ᵥ w) k := by
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun l _ => by rw [hUcol l]
      rw [h1, hMw]; simp
    have hNcol : ∀ i, N i 0 = if i = 0 then μ else 0 := by
      intro i
      have hassoc : N i 0 = ∑ k, Uᴴ i k * (M * U) k 0 := by
        rw [hN, Matrix.mul_assoc]; simp [Matrix.mul_apply]
      have hUw : ∑ k, Uᴴ i k * w k = if i = 0 then (1 : ℂ) else 0 := by
        have : (Uᴴ * U) i 0 = ∑ k, Uᴴ i k * w k := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [hUcol k]
        rw [← this, hU1]; simp [Matrix.one_apply]
      rw [hassoc]
      have : ∑ k, Uᴴ i k * (M * U) k 0 = μ * ∑ k, Uᴴ i k * w k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hMU k]; ring
      rw [this, hUw]
      by_cases h : i = 0 <;> simp [h]
    obtain ⟨V, T', hV1, hV2, hT', hVA⟩ := ih (N.submatrix Fin.succ Fin.succ)
    set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := embedSucc V with hW
    have hW1 : Wᴴ * W = 1 := by rw [hW]; exact embedSucc_conjTranspose_mul_self hV1
    have hW2 : W * Wᴴ = 1 := by rw [hW]; exact embedSucc_mul_conjTranspose_self hV1
    refine ⟨U * W, Wᴴ * N * W, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.conjTranspose_mul]
      calc Wᴴ * Uᴴ * (U * W) = Wᴴ * (Uᴴ * U) * W := by noncomm_ring
        _ = 1 := by rw [hU1, Matrix.mul_one, hW1]
    · rw [Matrix.conjTranspose_mul]
      calc U * W * (Wᴴ * Uᴴ) = U * (W * Wᴴ) * Uᴴ := by noncomm_ring
        _ = 1 := by rw [hW2, Matrix.mul_one, hU2]
    · intro i j hij
      have key : ∀ i j : Fin (n + 1), (Wᴴ * N * W) i j =
          ∑ k, (starRingEnd ℂ) (W k i) * ∑ l, N k l * W l j := by
        intro i j
        rw [Matrix.mul_assoc]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
      induction i using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          rw [key]
          have hinner : ∀ k, ∑ l, N k l * W l 0 = N k 0 := by
            intro k
            rw [Fin.sum_univ_succ]
            simp [hW]
          simp only [hinner]
          rw [Fin.sum_univ_succ]
          simp [hW, hNcol]
        | succ j' =>
          have hlt' : j' < i' := by simpa [Fin.succ_lt_succ_iff] using hij
          have heq : (Wᴴ * N * W) i'.succ j'.succ = T' i' j' := by
            rw [key, ← hVA, Matrix.mul_assoc]
            have hinner : ∀ k' : Fin n, ∑ l, N k'.succ l * W l j'.succ =
                ∑ l', N.submatrix Fin.succ Fin.succ k' l' * V l' j' := by
              intro k'
              rw [Fin.sum_univ_succ]
              simp [hW]
            rw [Fin.sum_univ_succ]
            simp only [hW, embedSucc_zero_succ, map_zero, zero_mul, zero_add,
              embedSucc_succ_succ]
            simp only [← hW, hinner]
            simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
              Matrix.submatrix_apply]
          rw [heq]
          exact hT' hlt'
    · rw [Matrix.conjTranspose_mul, hN]
      noncomm_ring

end GaloisForLFunctions.HTGeometry
