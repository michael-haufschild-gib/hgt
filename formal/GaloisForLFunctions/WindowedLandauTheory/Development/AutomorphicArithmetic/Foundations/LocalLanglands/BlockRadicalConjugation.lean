import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitCoordinates
import Mathlib.Data.Matrix.PEquiv

/-! Every proper block radical contains a conjugate of a standard
two-block radical. Split the labels at a threshold between two
distinct values and permute the coordinate summands. -/

noncomputable section

open Matrix GlobalTheory.GLq

namespace GlobalTheory.GLp

/-- The labels of the ordered blocks with first size `a`. -/
def standardTwoBlockLabels (n a : ℕ) (i : Fin n) : ℕ :=
  if i.val < a then 0 else 1

theorem monotone_standardTwoBlockLabels (n a : ℕ) : Monotone (standardTwoBlockLabels n a) := by
  intro i j hij
  have h : i.val ≤ j.val := hij
  simp only [standardTwoBlockLabels]
  split_ifs <;> omega

theorem mem_standardTwoBlockRadical_iff {k : Type} [Field k] {n a : ℕ}
    (u : GL (Fin n) k) :
    u ∈ blockUnipotentRadical k (standardTwoBlockLabels n a) ↔
      ∀ i j : Fin n, ¬ (i.val < a ∧ a ≤ j.val) → (u.val - 1) i j = 0 := by
  rw [mem_blockUnipotentRadical]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  by_cases hi : i.val < a <;> by_cases hj : j.val < a <;>
    simp [standardTwoBlockLabels, hi, hj, not_le]

theorem exists_standardTwoBlockRadical_conjugate_le {k : Type} [Field k] {n : ℕ}
    (b : Fin n → ℕ) (hb : ∃ x y, b x < b y) :
    ∃ (q : GL (Fin n) k) (a : ℕ), 0 < a ∧ a < n ∧
      ∀ u ∈ blockUnipotentRadical k (standardTwoBlockLabels n a),
        q * u * q⁻¹ ∈ blockUnipotentRadical k b := by
  classical
  obtain ⟨x, y, hxy⟩ := hb
  let s := fun i => b i < b y
  obtain ⟨a, c, ha, hc, e, he⟩ := exists_fin_split s ⟨x, hxy⟩ ⟨y, lt_irrefl _⟩
  have hn : a + c = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  have he₁ : (e.symm.toPEquiv.toMatrix : Matrix (Fin (a + c)) (Fin (a + c)) k) *
      e.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  have he₂ : (e.toPEquiv.toMatrix : Matrix (Fin (a + c)) (Fin (a + c)) k) *
      e.symm.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  let P : Matrix (Fin (a + c)) (Fin (a + c)) k := e.symm.toPEquiv.toMatrix
  let Q : Matrix (Fin (a + c)) (Fin (a + c)) k := e.toPEquiv.toMatrix
  let q : GL (Fin (a + c)) k := ⟨P, Q, he₁, he₂⟩
  have hq (u : GL (Fin (a + c)) k) (i j : Fin (a + c)) :
      (q * u * q⁻¹).val i j = u.val (e.symm i) (e.symm j) := by
    change (P * u.val * Q) i j = _
    dsimp only [P, Q]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp
  refine ⟨q, a, ha, by omega, fun u hu => ?_⟩
  apply mem_blockUnipotentRadical.mpr
  intro i j hij
  have hn' : ¬ ((e.symm i).val < a ∧ a ≤ (e.symm j).val) := by
    rintro ⟨hi, hj⟩
    have hi' : s i := by simpa only [e.apply_symm_apply] using (he (e.symm i)).mpr hi
    have hj' : ¬ s j := by
      simpa only [e.apply_symm_apply] using (fun hs => (not_lt_of_ge hj) ((he (e.symm j)).mp hs))
    exact hj' (hij.trans_lt hi')
  have h := (mem_standardTwoBlockRadical_iff u).mp hu (e.symm i) (e.symm j) hn'
  rw [Matrix.sub_apply, sub_eq_zero] at h
  rw [Matrix.sub_apply, sub_eq_zero, hq, h]
  simp [Matrix.one_apply, e.symm.injective.eq_iff]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_standardTwoBlockRadical_conjugate_le
