import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPrimeExponentGramBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Classical finite prime-box Gram bounds

The geometric prime-exponent bounds tensorize over every finite box. This uses
Mathlib's positive-semidefinite Kronecker product and tuple equivalence, then
pulls back along that equivalence. The public result supplies both matrix and
quadratic-form bounds with the classical prime-product constants.

These are supporting ingredients for the native dyadic-antichain Fermi theorem,
not new scientific contributions. The corresponding classical GCD matrix bounds
appear in Aistleitner--Berkes--Seip, arXiv:1210.0741, Theorem 6.
-/

open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- The classical geometric kernel on a finite prime-exponent interval. -/
private def primeExponentGramMatrix (r : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => r ^ ((i.val-j.val)+(j.val-i.val))

private theorem gramMatrix_hermitian (r : ℝ) (n : ℕ) :
    (primeExponentGramMatrix r n).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, primeExponentGramMatrix, star_trivial]
  rw [Nat.add_comm]

private theorem gramMatrix_form (r : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    star x ⬝ᵥ (primeExponentGramMatrix r n *ᵥ x) = primeExponentGramEnergy r x := by
  simp only [dotProduct, Matrix.mulVec, primeExponentGramMatrix, primeExponentGramEnergy,
    Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem real_diagonal_form {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    star x ⬝ᵥ x = ∑ i, (x i)^2 := by
  simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]

private theorem real_scalar_identity_hermitian {ι : Type*} [DecidableEq ι] (a : ℝ) :
    (a • (1 : Matrix ι ι ℝ)).IsHermitian := by
  ext i j
  by_cases h : i=j <;>
    simp [Matrix.conjTranspose_apply, Matrix.smul_apply, h, eq_comm]

/-- Scalar geometric bounds as positive-semidefinite matrix inequalities. -/
private theorem primeExponentGramMatrix_bounds (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (primeExponentGramMatrix r n - ((1-r)/(1+r)) • 1).PosSemidef ∧
      (((1+r)/(1-r)) • 1 - primeExponentGramMatrix r n).PosSemidef := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((gramMatrix_hermitian r n).sub (real_scalar_identity_hermitian _))
    intro x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, gramMatrix_form, real_diagonal_form]
    exact sub_nonneg.mpr (primeExponentGramEnergy_bounds r hr hr1 x).1
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((real_scalar_identity_hermitian _).sub (gramMatrix_hermitian r n))
    intro x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, gramMatrix_form, real_diagonal_form]
    exact sub_nonneg.mpr (primeExponentGramEnergy_bounds r hr hr1 x).2

/-- Two finite Gram bounds tensorize by the classical PSD Kronecker product. -/
private theorem realGram_kronecker_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : (A-a•1).PosSemidef ∧ (b•1-A).PosSemidef)
    (hB : (B-c•1).PosSemidef ∧ (d•1-B).PosSemidef) :
    (A ⊗ₖ B - (a*c)•1).PosSemidef ∧ ((b*d)•1-A ⊗ₖ B).PosSemidef := by
  have hBpos : B.PosSemidef := by
    have h := hB.1.add ((Matrix.PosSemidef.one : (1 : Matrix κ κ ℝ).PosSemidef).smul hc)
    simpa only [sub_add_cancel] using h
  have hIa := (Matrix.PosSemidef.one : (1 : Matrix ι ι ℝ).PosSemidef).smul ha
  have hIb := (Matrix.PosSemidef.one : (1 : Matrix ι ι ℝ).PosSemidef).smul hb
  constructor
  · have h := (hA.1.kronecker hBpos).add (hIa.kronecker hB.1)
    have heq : A ⊗ₖ B - (a*c)•1 =
        (A-a•1) ⊗ₖ B + (a•1) ⊗ₖ (B-c•1) := by
      ext ⟨i,k⟩ ⟨j,l⟩
      by_cases h1 : i=j <;> by_cases h2 : k=l <;>
        simp [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.add_apply, h1, h2] <;> ring
    rw [heq]
    exact h
  · have h := (hA.2.kronecker hBpos).add (hIb.kronecker hB.2)
    have heq : (b*d)•1-A ⊗ₖ B =
        (b•1-A) ⊗ₖ B + (b•1) ⊗ₖ (d•1-B) := by
      ext ⟨i,k⟩ ⟨j,l⟩
      by_cases h1 : i=j <;> by_cases h2 : k=l <;>
        simp [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.add_apply, h1, h2] <;> ring
    rw [heq]
    exact h


/-- Geometric Gram kernel on a finite box of prime exponents. -/
def primeBoxGramMatrix {k : ℕ} (r : Fin k → ℝ) (n : ℕ) :
    Matrix (Fin k → Fin n) (Fin k → Fin n) ℝ :=
  fun x y => ∏ i, (r i)^(((x i).val-(y i).val)+((y i).val-(x i).val))

/-- Classical finite prime-box bounds, independent of every exponent depth. -/
theorem primeBoxGramMatrix_bounds {k : ℕ} (r : Fin k → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (n : ℕ) :
    (primeBoxGramMatrix r n - (∏ i, (1-r i)/(1+r i))•1).PosSemidef ∧
      ((∏ i, (1+r i)/(1-r i))•1 - primeBoxGramMatrix r n).PosSemidef := by
  classical
  induction k with
  | zero =>
    have heq : primeBoxGramMatrix r n = 1 := by
      ext x y
      have hxy : x=y := funext fun i => Fin.elim0 i
      simp [primeBoxGramMatrix, Matrix.one_apply, hxy]
    constructor <;> simpa [heq] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0 → Fin n) (Fin 0 → Fin n) ℝ).PosSemidef)
  | succ k ih =>
    let t : Fin k → ℝ := fun i => r i.succ
    have h0 := hr 0
    have h01 := hr1 0
    have ha : 0 ≤ (1-r 0)/(1+r 0) :=
      div_nonneg (by linarith) (by linarith)
    have hb : 0 ≤ (1+r 0)/(1-r 0) :=
      div_nonneg (by linarith) (by linarith)
    have hc : 0 ≤ ∏ i : Fin k, (1-t i)/(1+t i) := by
      apply Finset.prod_nonneg
      intro i _
      exact div_nonneg (by dsimp [t]; linarith [hr1 i.succ])
        (by dsimp [t]; linarith [hr i.succ])
    have ht := realGram_kronecker_bounds
      (primeExponentGramMatrix (r 0) n) (primeBoxGramMatrix t n) ha hb hc
      (primeExponentGramMatrix_bounds (r 0) h0 h01 n)
      (ih t (fun i => hr i.succ) (fun i => hr1 i.succ))
    let e : (Fin (k+1) → Fin n) ≃ Fin n × (Fin k → Fin n) :=
      (Fin.consEquiv (fun _ : Fin (k+1) => Fin n)).symm
    have hGram : ((primeExponentGramMatrix (r 0) n) ⊗ₖ primeBoxGramMatrix t n).submatrix
        e e = primeBoxGramMatrix r n := by
      ext x y
      simp [Matrix.submatrix, primeExponentGramMatrix, primeBoxGramMatrix,
        Fin.prod_univ_succ, e, Fin.consEquiv, Fin.tail, t]
    have hOne : (1 : Matrix (Fin n × (Fin k → Fin n))
        (Fin n × (Fin k → Fin n)) ℝ).submatrix e e = 1 := by
      ext x y
      simp [Matrix.submatrix, Matrix.one_apply]
    have hl := ht.1.submatrix e
    have hu := ht.2.submatrix e
    change (((primeExponentGramMatrix (r 0) n) ⊗ₖ primeBoxGramMatrix t n).submatrix e e -
      ((1-r 0)/(1+r 0)*(∏ i, (1-t i)/(1+t i)))•
        (1 : Matrix (Fin n × (Fin k → Fin n)) (Fin n × (Fin k → Fin n)) ℝ).submatrix e e).PosSemidef at hl
    change (((1+r 0)/(1-r 0)*(∏ i, (1+t i)/(1-t i)))•
        (1 : Matrix (Fin n × (Fin k → Fin n)) (Fin n × (Fin k → Fin n)) ℝ).submatrix e e -
      ((primeExponentGramMatrix (r 0) n) ⊗ₖ primeBoxGramMatrix t n).submatrix e e).PosSemidef at hu
    rw [hGram, hOne] at hl hu
    simpa only [Fin.prod_univ_succ] using And.intro hl hu


/-- The finite prime-box product bounds for an arbitrary real coefficient vector. -/
theorem primeBoxGramMatrix_quadratic_bounds {k : ℕ} (r : Fin k → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (n : ℕ)
    (c : (Fin k → Fin n) → ℝ) :
    (∏ i, (1-r i)/(1+r i))*(∑ x, (c x)^2) ≤ c ⬝ᵥ (primeBoxGramMatrix r n *ᵥ c) ∧
      c ⬝ᵥ (primeBoxGramMatrix r n *ᵥ c) ≤ (∏ i, (1+r i)/(1-r i))*(∑ x, (c x)^2) := by
  have h := primeBoxGramMatrix_bounds r hr hr1 n
  have hl := h.1.dotProduct_mulVec_nonneg c
  have hu := h.2.dotProduct_mulVec_nonneg c
  have hc : star c = c := by ext x; simp
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, real_diagonal_form, hc] at hl hu
  exact ⟨sub_nonneg.mp hl, sub_nonneg.mp hu⟩

end GaloisForLFunctions.TransHorizonIncidenceMechanics
