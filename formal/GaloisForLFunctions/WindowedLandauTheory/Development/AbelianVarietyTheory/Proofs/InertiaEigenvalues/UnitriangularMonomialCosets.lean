import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import Mathlib.GroupTheory.DoubleCoset

/-! A monomial representative of an upper unitriangular double coset
determines both its permutation and its nonzero column entries. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions.HTGeometry
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- The monomial matrix sends column `j` to row `σ j` with entry `c j`. -/
def monomialUnit (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ) : Gn g n where
  val := signedMonomialMatrix σ c
  inv := signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹)
  val_inv := by
    rw [signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]
  inv_val := by
    rw [signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]

private theorem monomial_mul_apply
    (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ) (B : Mt g n) (i j : Fin n) :
    (signedMonomialMatrix σ c * B) i j = (c (σ.symm i) : ZMod g) * B (σ.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)]
  · simp [signedMonomialMatrix]
  · intro k _ hk
    have h : i ≠ σ k := fun e => hk (σ.injective (e.symm.trans (σ.apply_symm_apply i).symm))
    simp [signedMonomialMatrix, h]
  · simp

private theorem mul_monomial_apply
    (B : Mt g n) (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ) (i j : Fin n) :
    (B * signedMonomialMatrix σ c) i j = B i (σ j) * (c j : ZMod g) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [signedMonomialMatrix]
  · intro k _ hk
    simp [signedMonomialMatrix, hk]
  · simp

/-- Monomial conjugation permutes both indices and rescales each entry. -/
theorem monomialConj_apply (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ)
    (a : Gn g n) (i j : Fin n) :
    (((monomialUnit σ c)⁻¹ * a * monomialUnit σ c : Gn g n) : Mt g n) i j =
      (c i : ZMod g)⁻¹ * (a : Mt g n) (σ i) (σ j) * c j := by
  change (signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹) *
    (a : Mt g n) * signedMonomialMatrix σ c) i j = _
  rw [mul_monomial_apply, monomial_mul_apply]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, Units.val_inv_eq_inv_val]

private theorem pivot_compare
    (σ τ : Equiv.Perm (Fin n)) (c d : Fin n → (ZMod g)ˣ)
    (a b : upperUnitriangular g n) (he : monomialUnit σ c = (a : Gn g n) * monomialUnit τ d * b)
    (j : Fin n) : σ j ≤ τ j ∧ (σ j = τ j → c j = d j) := by
  have hb : (monomialUnit σ c : Gn g n) * ((b⁻¹ : upperUnitriangular g n) : Gn g n) =
      (a : Gn g n) * monomialUnit τ d :=
    (congrArg (fun x : Gn g n => x * (b : Gn g n)⁻¹) he).trans (mul_inv_cancel_right _ _)
  have e := congrArg (fun x : Gn g n => (x : Mt g n) (σ j) j) hb
  change (signedMonomialMatrix σ c * ((b⁻¹ : upperUnitriangular g n).val : Mt g n)) (σ j) j =
    ((a.val : Mt g n) * signedMonomialMatrix τ d) (σ j) j at e
  have hA : IsUniUp (a.val : Mt g n) := mem_upperUnitriangular.mp a.2
  have hB : IsUniUp ((b⁻¹ : upperUnitriangular g n).val : Mt g n) :=
    mem_upperUnitriangular.mp (b⁻¹).2
  rw [monomial_mul_apply, mul_monomial_apply, σ.symm_apply_apply, (hB j j).2 rfl, mul_one] at e
  constructor
  · apply le_of_not_gt
    intro h
    exact (Units.ne_zero (c j)) (e.trans (by rw [(hA _ _).1 h, zero_mul]))
  · intro h
    apply Units.ext
    exact e.trans (by rw [h, (hA (τ j) (τ j)).2 rfl, one_mul])

/-- Two monomial matrices in the same unitriangular double coset have equal
permutations and equal column entries. -/
theorem monomial_data_of_doubleCoset_eq
    (σ τ : Equiv.Perm (Fin n)) (c d : Fin n → (ZMod g)ˣ)
    (h : DoubleCoset.mk (upperUnitriangular g n) (upperUnitriangular g n) (monomialUnit σ c) =
      DoubleCoset.mk (upperUnitriangular g n) (upperUnitriangular g n) (monomialUnit τ d)) :
    σ = τ ∧ c = d := by
  let U := upperUnitriangular g n
  obtain ⟨a, ha, b, hb, he⟩ := (DoubleCoset.eq U U _ _).mp h.symm
  obtain ⟨a', ha', b', hb', he'⟩ := (DoubleCoset.eq U U _ _).mp h
  have e := pivot_compare σ τ c d ⟨a, ha⟩ ⟨b, hb⟩ he
  have e' := pivot_compare τ σ d c ⟨a', ha'⟩ ⟨b', hb'⟩ he'
  have hp (j : Fin n) : σ j = τ j := le_antisymm (e j).1 (e' j).1
  exact ⟨Equiv.ext hp, funext fun j => (e j).2 (hp j)⟩

end GlobalTheory.GLq
