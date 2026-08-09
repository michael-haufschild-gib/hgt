import GaloisForLFunctions.HTGeometry.PairGradientRecursion
import GaloisForLFunctions.HTGeometry.TopCoordinateDegree

/-!
# Degrees in the two-coordinate law

The degree layer itself is law-independent — `TopDegLE`, `TopFree`, `TopLim`, `topLim_det` and
`topLim_unique` are statements about the model alone — so only the law-specific facts need
transporting.

A factor at `j` occupies the coordinates `j` and `j+1`, so it is free of every other coordinate; the
jets below the newest level are therefore free of it, and so are the responses.  The newest jet does
involve the newest coordinate, through its last factor, and its degree there is the degree of the
placed polynomial in its *second* variable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## A factor is free of every other coordinate -/

theorem degreeOf_pairPoly_of_ne {m j : ℕ} (h0 : m ≠ j) (h1 : m ≠ j + 1)
    (q : MvPolynomial (Fin 2) ℂ) : degreeOf m (pairPoly q j) = 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [pairPoly_C]
      simp
  | add q r hq hr =>
      rw [pairPoly_add]
      have := degreeOf_add_le m (pairPoly q j) (pairPoly r j)
      omega
  | mul_X q i hq =>
      rw [pairPoly_mul_X]
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      have hX : degreeOf m (MvPolynomial.X (j + (i : ℕ)) : MvPolynomial ℕ ℂ) = 0 := by
        rw [degreeOf_X, if_neg (by rcases hi with hi | hi <;> omega)]
      have := degreeOf_mul_le m (pairPoly q j) (MvPolynomial.X (j + (i : ℕ)))
      omega

theorem topFree_pairFactor {m j : ℕ} (h0 : m ≠ j) (h1 : m ≠ j + 1)
    (q : MvPolynomial (Fin 2) ℂ) : TopFree m (pairFactor q j) :=
  topFree_algebraMap (degreeOf_pairPoly_of_ne h0 h1 q)

theorem topFree_inv_pairFactor {m j : ℕ} (h0 : m ≠ j) (h1 : m ≠ j + 1)
    (q : MvPolynomial (Fin 2) ℂ) : TopFree m ((pairFactor q j)⁻¹) := by
  rcases eq_or_ne (pairFactor q j) 0 with h | h
  · rw [h, inv_zero]
    exact topFree_zero m
  · refine ⟨1, pairPoly q j, ?_, ?_, by simp, degreeOf_pairPoly_of_ne h0 h1 q⟩
    · intro hc
      exact h (by rw [pairFactor, hc, map_zero])
    · rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField (pairPoly q j) = pairFactor q j from rfl,
        mul_inv_cancel₀ h, map_one]

/-! ## Everything below the newest level is free of it -/

/-- **The low subalgebra of a lower level is free of the newest coordinate.** -/
theorem topFree_of_mem_pairLowSub {m m' : ℕ} (hm : m' < m) {f : CascadeField}
    (hf : f ∈ pairLowSub p m') : TopFree m f := by
  classical
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · refine topFree_algebraMap ?_
        rw [degreeOf_X, if_neg (by omega : ¬ m = j)]
      · exact topFree_inv_pairFactor (by omega) (by omega) (p j)
  | algebraMap c =>
      have hc : (algebraMap ℂ CascadeField) c
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.C c) := rfl
      rw [hc]
      exact topFree_algebraMap (degreeOf_C c m)
  | add x y _ _ ihx ihy => exact TopFree.add ihx ihy
  | mul x y _ _ ihx ihy => exact TopFree.mul ihx ihy

/-- **Jets below the newest level are free of it.** -/
theorem topFree_pairJet {m k : ℕ} (h : k < m) : TopFree m (pairJet p k) :=
  topFree_of_mem_pairLowSub h (pairJet_mem_pairLowSub (le_refl k))

/-- **Responses below the newest level are free of it.** -/
theorem topFree_pairResponse {m k l : ℕ} (h : l < m) : TopFree m (pairResponse p k l) :=
  topFree_of_mem_pairLowSub h
    (fpderiv_mem_pairLowSub k (pairJet_mem_pairLowSub (le_refl l)))

/-! ## The newest jet -/

/-- Placing a two-variable polynomial puts its second-variable degree on the upper coordinate. -/
theorem degreeOf_pairPoly_top (j : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    degreeOf (j + 1) (pairPoly q j) ≤ degreeOf 1 q := by
  classical
  rw [pairPoly, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine le_trans (MvPolynomial.degreeOf_sum_le (j + 1) _ _) (Finset.sup_le fun μ hμ => ?_)
  have hsupp : (∏ i ∈ μ.support, (MvPolynomial.X (j + (i : ℕ)) : MvPolynomial ℕ ℂ) ^ μ i)
      = ∏ i : Fin 2, (MvPolynomial.X (j + (i : ℕ)) : MvPolynomial ℕ ℂ) ^ μ i :=
    Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])
  rw [hsupp, Fin.prod_univ_two]
  have hcoeff : degreeOf (j + 1)
      ((algebraMap ℂ (MvPolynomial ℕ ℂ)) (MvPolynomial.coeff μ q)) = 0 := by
    rw [show (algebraMap ℂ (MvPolynomial ℕ ℂ)) (MvPolynomial.coeff μ q)
        = MvPolynomial.C (MvPolynomial.coeff μ q) from rfl]
    exact degreeOf_C _ _
  have h0 : degreeOf (j + 1)
      ((MvPolynomial.X (j + ((0 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 0) = 0 := by
    refine Nat.le_zero.mp (le_trans (degreeOf_pow_le _ _ _) ?_)
    rw [degreeOf_X, if_neg (by simp)]
    simp
  have h1 : degreeOf (j + 1)
      ((MvPolynomial.X (j + ((1 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 1) ≤ μ 1 := by
    refine le_trans (degreeOf_pow_le _ _ _) ?_
    rw [degreeOf_X]
    split_ifs <;> omega
  have hmB := degreeOf_mul_le (j + 1)
    ((MvPolynomial.X (j + ((0 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 0)
    ((MvPolynomial.X (j + ((1 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 1)
  have hmA := degreeOf_mul_le (j + 1)
    ((algebraMap ℂ (MvPolynomial ℕ ℂ)) (MvPolynomial.coeff μ q))
    ((MvPolynomial.X (j + ((0 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 0
      * (MvPolynomial.X (j + ((1 : Fin 2) : ℕ)) : MvPolynomial ℕ ℂ) ^ μ 1)
  have hle : μ 1 ≤ degreeOf 1 q := by
    rw [MvPolynomial.degreeOf_eq_sup]
    exact Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 1) hμ
  omega

end GaloisForLFunctions.HTGeometry
