import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.FinRange

/-!
# Monomials as multilinear maps

A multi-index of total degree `k` in `n` variables lists its coordinates in increasing order as a
tuple of length `k`; the product of the coordinates selected by that tuple is a continuous
multilinear map of `k` arguments whose value on a constant tuple is the monomial of the multi-index.
These are the terms of the power series of a holomorphic function of several variables.

* `multiIndexList` : the coordinates of a multi-index, listed with multiplicity.
* `multiIndexTuple` : the same list, as a tuple of length the total degree.
* `multiIndexCMM` : the monomial of a multi-index, as a continuous multilinear map.
-/

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

section MultiIndexList

variable {n : ℕ}

/-- The coordinates of a multi-index, each listed with its multiplicity. -/
def multiIndexList (m : Fin n → ℕ) : List (Fin n) :=
  ((List.finRange n).map fun i => List.replicate (m i) i).flatten

theorem multiIndexList_length (m : Fin n → ℕ) : (multiIndexList m).length = ∑ i, m i := by
  have h1 : (multiIndexList m).length =
      ((List.finRange n).map fun i => (List.replicate (m i) i).length).sum := by
    rw [multiIndexList, List.length_flatten, List.map_map]
    rfl
  have h2 : ((List.finRange n).map fun i => (List.replicate (m i) i).length) =
      List.ofFn fun i => m i := by
    rw [List.ofFn_eq_map]
    exact List.map_congr_left fun i _ => List.length_replicate
  rw [h1, h2, List.sum_ofFn]

theorem multiIndexList_prod {M : Type*} [CommMonoid M] (m : Fin n → ℕ) (y : Fin n → M) :
    ((multiIndexList m).map y).prod = ∏ i, (y i) ^ (m i) := by
  have h1 : ((multiIndexList m).map y).prod =
      ((List.finRange n).map fun i => ((List.replicate (m i) i).map y).prod).prod := by
    rw [multiIndexList, List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
    rfl
  have h2 : ((List.finRange n).map fun i => ((List.replicate (m i) i).map y).prod) =
      List.ofFn fun i => (y i) ^ (m i) := by
    rw [List.ofFn_eq_map]
    refine List.map_congr_left fun i _ => ?_
    rw [List.map_replicate, List.prod_replicate]
  rw [h1, h2, List.prod_ofFn]

/-- The coordinates of a multi-index of total degree `k`, as a tuple of length `k`. -/
def multiIndexTuple {k : ℕ} (m : Fin n → ℕ) (hm : ∑ i, m i = k) (a : Fin k) : Fin n :=
  (multiIndexList m).get (Fin.cast (by rw [multiIndexList_length, hm]) a)

theorem multiIndexTuple_prod {M : Type*} [CommMonoid M] {k : ℕ} (m : Fin n → ℕ)
    (hm : ∑ i, m i = k) (y : Fin n → M) :
    (∏ a : Fin k, y (multiIndexTuple m hm a)) = ∏ i, (y i) ^ (m i) := by
  have hlen : (multiIndexList m).length = k := by rw [multiIndexList_length, hm]
  rw [← multiIndexList_prod m y]
  have h1 : List.ofFn (fun a : Fin (multiIndexList m).length => y ((multiIndexList m).get a)) =
      (multiIndexList m).map y := List.ofFn_getElem_eq_map _ _
  rw [← h1, List.prod_ofFn]
  exact Fin.prod_congr'
    (fun a : Fin (multiIndexList m).length => y ((multiIndexList m).get a)) hlen.symm

end MultiIndexList

section MultiIndexMap

variable {n k : ℕ}

/-- **The monomial of a multi-index, as a continuous multilinear map**: the product of the
coordinates selected by the tuple of the multi-index. -/
noncomputable def multiIndexCMM (m : Fin n → ℕ) (hm : ∑ i, m i = k) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    fun a => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (multiIndexTuple m hm a)

theorem multiIndexCMM_apply (m : Fin n → ℕ) (hm : ∑ i, m i = k) (v : Fin k → (Fin n → ℂ)) :
    multiIndexCMM m hm v = ∏ a, v a (multiIndexTuple m hm a) := by
  show (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ)
    (fun a => v a (multiIndexTuple m hm a)) = _
  rw [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

/-- **The value of the monomial map on a constant tuple is the monomial.** -/
theorem multiIndexCMM_diagonal (m : Fin n → ℕ) (hm : ∑ i, m i = k) (y : Fin n → ℂ) :
    multiIndexCMM m hm (fun _ => y) = ∏ i, (y i) ^ (m i) := by
  rw [multiIndexCMM_apply]
  exact multiIndexTuple_prod m hm y

/-- The monomial map has norm at most one. -/
theorem multiIndexCMM_norm_le (m : Fin n → ℕ) (hm : ∑ i, m i = k) :
    ‖multiIndexCMM m hm‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [multiIndexCMM_apply, one_mul, norm_prod]
  exact Finset.prod_le_prod (fun a _ => norm_nonneg _)
    fun a _ => norm_le_pi_norm (v a) (multiIndexTuple m hm a)

end MultiIndexMap

end GaloisForLFunctions.HTGeometry
