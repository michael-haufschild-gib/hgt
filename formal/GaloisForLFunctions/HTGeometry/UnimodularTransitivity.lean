import GaloisForLFunctions.HTGeometry.DedekindStableRange

/-!
# `SL_n` acts transitively on unimodular vectors over a Dedekind domain

Over a principal ideal domain a unimodular vector extends to a basis, so `SL_n` moves it to `e₀`.
Over a general Dedekind domain that fails, and the replacement is Bass's stable range theorem: the
last coordinate can be absorbed into the others by a unitriangular factor, the resulting shorter
vector is again unimodular, a second unitriangular factor clears the last coordinate, and the
induction hypothesis finishes.  The base case `n = 2` is the explicit matrix `!![p, q; −v₁, v₀]`,
which works over *any* commutative ring.

This is the covering input of Siegel reduction over a ring of integers: it is what lets a primitive
vector be normalised before the reduction proper begins.

* `lastColMat`, `lastRowMat` — the two unitriangular factors, with determinant one;
* `extendMat` — extension by a `1` in the last diagonal slot;
* `exists_det_one_mulVec_eq_single` — the transitivity.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### The unitriangular factors -/

/-- Upper unitriangular with a prescribed last column. -/
def lastColMat (f : Fin (n+1) → R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.of fun i j => if i = j then 1 else if j = Fin.last n then f i else 0

theorem det_lastColMat (f : Fin (n+1) → R) : (lastColMat f).det = 1 := by
  have htri : (lastColMat f).BlockTriangular id := by
    intro i j hij
    simp only [lastColMat, Matrix.of_apply, id] at hij ⊢
    have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
    rw [if_neg hne]
    have hj : j ≠ Fin.last n := by
      intro h
      rw [h] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last i))
    rw [if_neg hj]
  rw [Matrix.det_of_upperTriangular htri]
  simp [lastColMat]

theorem lastColMat_mulVec (f : Fin (n+1) → R) (hf : f (Fin.last n) = 0) (v : Fin (n+1) → R)
    (i : Fin (n+1)) :
    (lastColMat f *ᵥ v) i = v i + f i * v (Fin.last n) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : i = Fin.last n
  · subst hi
    rw [hf, zero_mul, add_zero]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [lastColMat]
    · intro j _ hj
      simp only [lastColMat, Matrix.of_apply]
      rw [if_neg (Ne.symm hj), if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_add_of_mem i (Fin.last n) (Finset.mem_univ _) (Finset.mem_univ _) hi]
    · simp [lastColMat, hi]
    · intro j _ hj
      simp only [lastColMat, Matrix.of_apply]
      rw [if_neg (Ne.symm hj.1), if_neg hj.2, zero_mul]

/-- Lower unitriangular with a prescribed last row. -/
def lastRowMat (g : Fin (n+1) → R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.of fun i j => if i = j then 1 else if i = Fin.last n then g j else 0

theorem det_lastRowMat (g : Fin (n+1) → R) : (lastRowMat g).det = 1 := by
  have htri : ∀ i j, i < j → (lastRowMat g) i j = 0 := by
    intro i j hij
    simp only [lastRowMat, Matrix.of_apply]
    have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
    rw [if_neg hne]
    have hi : i ≠ Fin.last n := by
      intro h
      rw [h] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last j))
    rw [if_neg hi]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [lastRowMat]

theorem lastRowMat_mulVec_castSucc (g : Fin (n+1) → R) (v : Fin (n+1) → R) (i : Fin n) :
    (lastRowMat g *ᵥ v) i.castSucc = v i.castSucc := by
  classical
  rw [Matrix.mulVec, dotProduct]
  have hi : i.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last i).ne
  rw [Finset.sum_eq_single i.castSucc]
  · simp [lastRowMat]
  · intro j _ hj
    simp only [lastRowMat, Matrix.of_apply]
    rw [if_neg (Ne.symm hj), if_neg hi, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lastRowMat_mulVec_last (g : Fin (n+1) → R) (hg : g (Fin.last n) = 0) (v : Fin (n+1) → R) :
    (lastRowMat g *ᵥ v) (Fin.last n) = v (Fin.last n) + ∑ j, g j * v j := by
  classical
  rw [Matrix.mulVec, dotProduct]
  have hsplit : ∀ j : Fin (n+1),
      (lastRowMat g) (Fin.last n) j * v j
        = (if j = Fin.last n then v j else 0) + g j * v j := by
    intro j
    simp only [lastRowMat, Matrix.of_apply]
    by_cases hj : Fin.last n = j
    · subst hj
      rw [if_pos rfl, if_pos rfl, hg, zero_mul, one_mul, add_zero]
    · rw [if_neg hj]
      simp [Ne.symm hj]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ (Fin.last n) v]
  simp

/-! ### Extension by one -/

/-- Extend a matrix by a `1` in the last diagonal slot. -/
def extendMat (γ : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks γ 0 0 1)

theorem finSumFinEquiv_symm_castSucc (i : Fin n) :
    (finSumFinEquiv (m := n) (n := 1)).symm i.castSucc = Sum.inl i := by
  have h : (i.castSucc : Fin (n+1)) = Fin.castAdd 1 i := rfl
  rw [h, finSumFinEquiv_symm_apply_castAdd]

theorem finSumFinEquiv_symm_last :
    (finSumFinEquiv (m := n) (n := 1)).symm (Fin.last n) = Sum.inr 0 := by
  have h : (Fin.last n : Fin (n+1)) = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext; simp
  rw [h, finSumFinEquiv_symm_apply_natAdd]

theorem det_extendMat (γ : Matrix (Fin n) (Fin n) R) : (extendMat γ).det = γ.det := by
  rw [extendMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem extendMat_mulVec_castSucc (γ : Matrix (Fin n) (Fin n) R) (v : Fin (n+1) → R) (i : Fin n) :
    (extendMat γ *ᵥ v) i.castSucc = (γ *ᵥ (fun k => v k.castSucc)) i := by
  classical
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_castSucc]
  have hlast : extendMat γ i.castSucc (Fin.last n) = 0 := by
    simp only [extendMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_castSucc, finSumFinEquiv_symm_last]
    rfl
  rw [hlast, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [extendMat, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_castSucc]
  rfl

theorem extendMat_mulVec_last (γ : Matrix (Fin n) (Fin n) R) (v : Fin (n+1) → R) :
    (extendMat γ *ᵥ v) (Fin.last n) = v (Fin.last n) := by
  classical
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hc : ∀ j : Fin n, extendMat γ (Fin.last n) j.castSucc = 0 := by
    intro j
    simp only [extendMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_castSucc, finSumFinEquiv_symm_last]
    rfl
  have hl : extendMat γ (Fin.last n) (Fin.last n) = 1 := by
    simp only [extendMat, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
    rfl
  rw [hl, one_mul, Finset.sum_congr rfl (fun j _ => by rw [hc j, zero_mul]), Finset.sum_const_zero,
    zero_add]

/-! ### Transitivity -/

/-- **`SL_n` acts transitively on unimodular vectors over a Dedekind domain**, for `n ≥ 2`.  The
target is written coordinatewise to avoid a `Zero (Fin n)` instance in the induction. -/
theorem exists_det_one_mulVec_eq_single {R : Type*} [CommRing R] [IsDedekindDomain R] :
    ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → R, (∃ p : Fin n → R, ∑ i, p i * v i = 1) →
      ∃ γ : Matrix (Fin n) (Fin n) R, γ.det = 1 ∧
        ∀ i : Fin n, (γ *ᵥ v) i = if (i : ℕ) = 0 then 1 else 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro v hv
      obtain ⟨p, hp⟩ := hv
      rw [Fin.sum_univ_two] at hp
      refine ⟨Matrix.of ![![p 0, p 1], ![-(v 1), v 0]], ?_, ?_⟩
      · rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        linear_combination hp
      · intro i
        fin_cases i <;>
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue,
            Fin.zero_eta, Fin.mk_one]
        · norm_num
          linear_combination hp
        · norm_num
          ring
  | succ n hn ih =>
      intro v hv
      obtain ⟨p, hp⟩ := hv
      rw [Fin.sum_univ_castSucc] at hp
      obtain ⟨x, q, hxq⟩ := exists_stableRange_vector n hn (fun i => v i.castSucc)
        (v (Fin.last n)) ⟨fun i => p i.castSucc, p (Fin.last n), hp⟩
      set f : Fin (n+1) → R := Fin.snoc x (0 : R) with hf
      set E₁ : Matrix (Fin (n+1)) (Fin (n+1)) R := lastColMat f with hE₁
      set v₁ : Fin (n+1) → R := E₁ *ᵥ v with hv₁
      have hf_last : f (Fin.last n) = 0 := by rw [hf]; simp
      have hv₁c : ∀ i : Fin n, v₁ i.castSucc = v i.castSucc + x i * v (Fin.last n) := by
        intro i
        rw [hv₁, hE₁, lastColMat_mulVec _ hf_last, hf]
        simp
      have hv₁l : v₁ (Fin.last n) = v (Fin.last n) := by
        rw [hv₁, hE₁, lastColMat_mulVec _ hf_last, hf_last, zero_mul, add_zero]
      set w : Fin n → R := fun i => v₁ i.castSucc with hw
      have hwu : ∑ i, q i * w i = 1 := by
        rw [hw]
        simpa only [hv₁c] using hxq
      set g : Fin (n+1) → R := Fin.snoc (fun i => -(v (Fin.last n) * q i)) (0 : R) with hg
      have hg_last : g (Fin.last n) = 0 := by rw [hg]; simp
      set E₂ : Matrix (Fin (n+1)) (Fin (n+1)) R := lastRowMat g with hE₂
      set v₂ : Fin (n+1) → R := E₂ *ᵥ v₁ with hv₂
      have hv₂c : ∀ i : Fin n, v₂ i.castSucc = w i := by
        intro i
        rw [hv₂, hE₂, lastRowMat_mulVec_castSucc, hw]
      have hv₂l : v₂ (Fin.last n) = 0 := by
        rw [hv₂, hE₂, lastRowMat_mulVec_last _ hg_last, hv₁l, Fin.sum_univ_castSucc, hg]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
        have hstep : ∀ i : Fin n, -(v (Fin.last n) * q i) * v₁ i.castSucc
            = -(v (Fin.last n) * (q i * w i)) := by
          intro i; rw [hw]; ring
        rw [Finset.sum_congr rfl (fun i _ => hstep i)]
        have hcol : ∑ i, -(v (Fin.last n) * (q i * w i))
            = -(v (Fin.last n) * ∑ i, q i * w i) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        rw [hcol, hwu]
        ring
      obtain ⟨γ', hdet', hact'⟩ := ih w ⟨q, hwu⟩
      refine ⟨extendMat γ' * (E₂ * E₁), ?_, ?_⟩
      · rw [Matrix.det_mul, Matrix.det_mul, det_extendMat, hdet', hE₂, hE₁, det_lastRowMat,
          det_lastColMat]
        ring
      · intro i
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv₁, ← hv₂]
        refine Fin.lastCases ?_ ?_ i
        · rw [extendMat_mulVec_last, hv₂l]
          have : ((Fin.last n : Fin (n+1)) : ℕ) = n := rfl
          rw [this, if_neg (by omega)]
        · intro j
          rw [extendMat_mulVec_castSucc]
          have hcoord : (fun k : Fin n => v₂ k.castSucc) = w := funext hv₂c
          rw [hcoord, hact' j]
          have : ((j.castSucc : Fin (n+1)) : ℕ) = (j : ℕ) := rfl
          rw [this]

/-! ### Extending a unimodular vector to a basis -/

/-- **A unimodular vector is the first column of a determinant-one matrix.**  Over a Dedekind
domain this is the substitute for "a primitive vector extends to a basis", and it is exactly the
inverse of the transitivity statement. -/
theorem exists_det_one_firstCol_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (n : ℕ) (hn : 2 ≤ n) (v : Fin n → R) (hv : ∃ p : Fin n → R, ∑ i, p i * v i = 1) :
    ∃ β : Matrix (Fin n) (Fin n) R, β.det = 1 ∧
      ∀ i : Fin n, β i ⟨0, by omega⟩ = v i := by
  obtain ⟨γ, hdet, hact⟩ := exists_det_one_mulVec_eq_single n hn v hv
  haveI hdetinv : Invertible γ.det := by rw [hdet]; exact invertibleOne
  haveI : Invertible γ := Matrix.invertibleOfDetInvertible γ
  refine ⟨⅟γ, ?_, ?_⟩
  · have hmul : γ * ⅟γ = 1 := mul_invOf_self γ
    have hdd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hdet, one_mul, Matrix.det_one] at hdd
    exact hdd
  · intro i
    have hcol : (⅟γ) *ᵥ (γ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]
    have hact' : (γ *ᵥ v) = fun j : Fin n => if (j : ℕ) = 0 then (1 : R) else 0 := funext hact
    rw [hact'] at hcol
    have hval := congrFun hcol i
    rw [← hval, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
    · simp
    · intro j _ hj
      have hjne : (j : ℕ) ≠ 0 := fun hcon => hj (Fin.ext hcon)
      rw [if_neg hjne, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon

end GaloisForLFunctions.HTGeometry
