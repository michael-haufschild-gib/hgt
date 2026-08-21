import GaloisForLFunctions.HTGeometry.BorelWeil.Sections

/-!
# Leading principal minors as Borel semi-invariants

The Borel–Weil sections attached to a dominant weight are built from the **leading principal
minors** of a matrix.  The `j`-th leading principal minor of `A` is realized here as the
determinant of `truncate j A`, the matrix that agrees with `A` on the top-left `j × j` block and
with the identity elsewhere; this keeps every construction inside `Matrix (Fin N) (Fin N) k` and
avoids dependent index types.

The key algebraic fact is that for `B` upper triangular the truncation is multiplicative,
`truncate j (A * B) = truncate j A * truncate j B`, because the first `j` columns of `A * B` span
the same space as the first `j` columns of `A`.  Consequently the `j`-th leading principal minor is
a `B`-semi-invariant of weight `∏_{i < j} b i i`.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.truncate`
* `GaloisForLFunctions.HTGeometry.BorelWeil.leadingMinor`

## Main results

* `truncate_mul` — multiplicativity of truncation against an upper-triangular matrix.
* `leadingMinor_mul_borel` — the semi-invariance of the leading principal minors.
* `leadingMinor_mem_regularFun` — leading principal minors are regular functions.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [CommRing k]

/-- The matrix agreeing with `A` on the top-left `j × j` block and with the identity elsewhere. -/
def truncate (j : ℕ) (A : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun i i' => if (i : ℕ) < j ∧ (i' : ℕ) < j then A i i' else if i = i' then 1 else 0

theorem truncate_apply_of_both {j : ℕ} {A : Matrix (Fin N) (Fin N) k} {i i' : Fin N}
    (hi : (i : ℕ) < j) (hi' : (i' : ℕ) < j) : truncate j A i i' = A i i' := by
  simp [truncate, hi, hi']

theorem truncate_apply_of_not_left {j : ℕ} {A : Matrix (Fin N) (Fin N) k} {i i' : Fin N}
    (hi : ¬ (i : ℕ) < j) : truncate j A i i' = if i = i' then 1 else 0 := by
  simp [truncate, hi]

theorem truncate_apply_of_not_right {j : ℕ} {A : Matrix (Fin N) (Fin N) k} {i i' : Fin N}
    (hi' : ¬ (i' : ℕ) < j) : truncate j A i i' = if i = i' then 1 else 0 := by
  simp [truncate, hi']

theorem truncate_one (j : ℕ) : truncate j (1 : Matrix (Fin N) (Fin N) k) = 1 := by
  ext i i'
  by_cases hi : (i : ℕ) < j
  · by_cases hi' : (i' : ℕ) < j
    · rw [truncate_apply_of_both hi hi']
    · rw [truncate_apply_of_not_right hi', Matrix.one_apply]
  · rw [truncate_apply_of_not_left hi, Matrix.one_apply]

/-- The truncation of an upper-triangular matrix is upper triangular. -/
theorem truncate_blockTriangular {j : ℕ} {A : Matrix (Fin N) (Fin N) k}
    (hA : A.BlockTriangular id) : (truncate j A).BlockTriangular id := by
  intro i i' h
  by_cases hi : (i : ℕ) < j
  · by_cases hi' : (i' : ℕ) < j
    · rw [truncate_apply_of_both hi hi']; exact hA h
    · rw [truncate_apply_of_not_right hi', if_neg (by rintro rfl; exact lt_irrefl _ h)]
  · rw [truncate_apply_of_not_left hi, if_neg (by rintro rfl; exact lt_irrefl _ h)]

/-- **Multiplicativity of truncation.**  If `B` is upper triangular then truncating a product is
the product of the truncations. -/
theorem truncate_mul (j : ℕ) (A B : Matrix (Fin N) (Fin N) k) (hB : B.BlockTriangular id) :
    truncate j (A * B) = truncate j A * truncate j B := by
  ext i i'
  by_cases hi : (i : ℕ) < j
  · by_cases hi' : (i' : ℕ) < j
    · rw [truncate_apply_of_both hi hi', Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : (r : ℕ) < j
      · rw [truncate_apply_of_both hi hr, truncate_apply_of_both hr hi']
      · rw [truncate_apply_of_not_right hr, if_neg (by rintro rfl; exact hr hi), zero_mul]
        have : B r i' = 0 := hB (show (i' : Fin N) < r from
          Fin.lt_def.mpr (lt_of_lt_of_le hi' (Nat.not_lt.mp hr)))
        rw [this, mul_zero]
    · have hne : i ≠ i' := by rintro rfl; exact hi' hi
      have hBd : truncate j B i' i' = 1 := by
        rw [truncate_apply_of_not_right hi', if_pos rfl]
      have hBr : ∀ r : Fin N, r ≠ i' → truncate j B r i' = 0 := fun r hr => by
        rw [truncate_apply_of_not_right hi', if_neg hr]
      have hAz : truncate j A i i' = 0 := by
        rw [truncate_apply_of_not_right hi', if_neg hne]
      have hLz : truncate j (A * B) i i' = 0 := by
        rw [truncate_apply_of_not_right hi', if_neg hne]
      rw [hLz, Matrix.mul_apply,
        Finset.sum_eq_single i' (fun r _ hr => by rw [hBr r hr, mul_zero])
          (fun h => absurd (Finset.mem_univ i') h), hBd, mul_one, hAz]
  · have hAr : ∀ r : Fin N, truncate j A i r = if i = r then 1 else 0 := fun _ =>
      truncate_apply_of_not_left hi
    have hLz : truncate j (A * B) i i' = if i = i' then 1 else 0 :=
      truncate_apply_of_not_left hi
    have hBz : truncate j B i i' = if i = i' then 1 else 0 :=
      truncate_apply_of_not_left hi
    rw [hLz, Matrix.mul_apply,
      Finset.sum_eq_single i (fun r _ hr => by rw [hAr r, if_neg (Ne.symm hr), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), hAr i, if_pos rfl, one_mul, hBz]

/-- The determinant of the truncation of an upper-triangular matrix. -/
theorem det_truncate_of_blockTriangular {j : ℕ} {B : Matrix (Fin N) (Fin N) k}
    (hB : B.BlockTriangular id) :
    (truncate j B).det = ∏ i : Fin N, (if (i : ℕ) < j then B i i else 1) := by
  rw [Matrix.det_of_upperTriangular (truncate_blockTriangular hB)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < j
  · rw [truncate_apply_of_both hi hi, if_pos hi]
  · rw [truncate_apply_of_not_left hi, if_pos rfl, if_neg hi]

/-- The `j`-th **leading principal minor** of an element of `SL(N,k)`. -/
def leadingMinor (j : ℕ) (g : SpecialLinearGroup (Fin N) k) : k :=
  (truncate j (g : Matrix (Fin N) (Fin N) k)).det

@[simp] theorem leadingMinor_one (j : ℕ) :
    leadingMinor j (1 : SpecialLinearGroup (Fin N) k) = 1 := by
  simp [leadingMinor, SpecialLinearGroup.coe_one, truncate_one]

/-- **Borel semi-invariance of the leading principal minors.** -/
theorem leadingMinor_mul_borel (j : ℕ) (g : SpecialLinearGroup (Fin N) k)
    {b : SpecialLinearGroup (Fin N) k} (hb : b ∈ borel (Fin N) k) :
    leadingMinor j (g * b) =
      leadingMinor j g * ∏ i : Fin N, (if (i : ℕ) < j then (b : Matrix (Fin N) (Fin N) k) i i
        else 1) := by
  rw [leadingMinor, SpecialLinearGroup.coe_mul, truncate_mul j _ _ hb, Matrix.det_mul,
    leadingMinor, det_truncate_of_blockTriangular hb]

/-- Leading principal minors are regular functions on `SL(N,k)`. -/
theorem leadingMinor_mem_regularFun (j : ℕ) :
    (leadingMinor j : SpecialLinearGroup (Fin N) k → k) ∈ regularFun (Fin N) k := by
  classical
  have hrepr : (leadingMinor j : SpecialLinearGroup (Fin N) k → k)
      = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : k) • ∏ i : Fin N,
          (fun g : SpecialLinearGroup (Fin N) k =>
            truncate j (g : Matrix (Fin N) (Fin N) k) (σ i) i) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    exact Matrix.det_apply' _
  rw [hrepr]
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _
    (Subalgebra.prod_mem _ fun i _ => ?_) _
  by_cases h : ((σ i : Fin N) : ℕ) < j ∧ (i : ℕ) < j
  · have hfun : (fun g : SpecialLinearGroup (Fin N) k =>
        truncate j (g : Matrix (Fin N) (Fin N) k) (σ i) i)
        = (coordFun (σ i) i : SpecialLinearGroup (Fin N) k → k) := by
      funext g
      rw [truncate_apply_of_both h.1 h.2]
      rfl
    rw [hfun]
    exact coordFun_mem_regularFun _ _
  · have hfun : (fun g : SpecialLinearGroup (Fin N) k =>
        truncate j (g : Matrix (Fin N) (Fin N) k) (σ i) i)
        = algebraMap k (SpecialLinearGroup (Fin N) k → k) (if σ i = i then 1 else 0) := by
      funext g
      rcases not_and_or.mp h with h1 | h2
      · rw [truncate_apply_of_not_left h1]; rfl
      · rw [truncate_apply_of_not_right h2]; rfl
    rw [hfun]
    exact Subalgebra.algebraMap_mem _ _

end GaloisForLFunctions.HTGeometry.BorelWeil
