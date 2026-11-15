import GaloisForLFunctions.RepresentationLifting.Lattices.RankTwoHermite

/-!
# The split Deligne–Lusztig fan as an integral lattice subdivision

The rays `(1,0), …, (1,p), (p+1,p²+p+1)` from Lemma 3.12 of
https://arxiv.org/abs/2610.40335 have unimodular adjacent pairs. The
determinant-index formula makes each adjacent lattice the full integer
lattice. The three-ray relations give coefficients `2, …, 2, p+2`,
the same coefficients appearing in the exceptional intersection chain.
-/

open scoped Matrix
namespace GaloisForLFunctions.RepresentationLifting.DeligneLusztigFan

/-- The fan with positive parameter `p = n+1`. -/
def ray (n k : ℕ) : Fin 2 → ℤ :=
  if k ≤ n + 1 then ![1, (k : ℤ)]
  else ![(n : ℤ) + 2, ((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1]

/-- Matrix whose columns are consecutive fan rays. -/
def adjacentMatrix (n : ℕ) (k : Fin (n + 2)) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![ray n k.val 0, ray n (k.val + 1) 0],
    ![ray n k.val 1, ray n (k.val + 1) 1]]

/-- Every cone in the subdivision is unimodular. -/
theorem adjacentMatrix_det (n : ℕ) (k : Fin (n + 2)) :
    (adjacentMatrix n k).det = 1 := by
  have hk : k.val ≤ n + 1 := by omega
  rw [Matrix.det_fin_two]
  by_cases h : k.val ≤ n
  · have hs : k.val + 1 ≤ n + 1 := by omega
    simp only [adjacentMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      ray, if_pos hk, if_pos hs, Nat.cast_add, Nat.cast_one]
    ring
  · have he : k.val = n + 1 := by omega
    have hs : ¬ k.val + 1 ≤ n + 1 := by omega
    simp only [adjacentMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      ray, if_pos hk, if_neg hs, he, Nat.cast_add, Nat.cast_one]
    ring

/-- Each adjacent pair generates a lattice of index one. -/
theorem adjacent_lattice_index (n : ℕ) (k : Fin (n + 2)) :
    Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (adjacentMatrix n k).mulVecLin) = 1 := by
  rw [LinearMap.card_quotient_range_eq_natAbs_det_all]
  have hd : LinearMap.det (adjacentMatrix n k).mulVecLin = (adjacentMatrix n k).det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℤ (Fin 2))]
    congr 1
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rw [hd, adjacentMatrix_det, Int.natAbs_one]

/-- Interior exceptional rays satisfy the coefficient-two relation. -/
theorem interior_ray_relation (n : ℕ) (k : Fin n) :
    ray n k.val + ray n (k.val + 2) = (2 : ℤ) • ray n (k.val + 1) := by
  have h₀ : k.val ≤ n + 1 := by omega
  have h₁ : k.val + 1 ≤ n + 1 := by omega
  have h₂ : k.val + 2 ≤ n + 1 := by omega
  simp only [ray, if_pos h₀, if_pos h₁, if_pos h₂]
  ext i
  fin_cases i <;> simp <;> ring

/-- The last exceptional ray carries the larger coefficient `p+2`. -/
theorem last_ray_relation (n : ℕ) :
    ray n n + ray n (n + 2) = ((n : ℤ) + 3) • ray n (n + 1) := by
  have h₀ : n ≤ n + 1 := by omega
  have h₂ : ¬ n + 2 ≤ n + 1 := by omega
  simp only [ray, if_pos h₀, if_neg h₂, if_pos le_rfl]
  ext i
  fin_cases i <;> simp <;> ring

#print axioms adjacentMatrix_det
#print axioms adjacent_lattice_index
#print axioms interior_ray_relation
#print axioms last_ray_relation

end GaloisForLFunctions.RepresentationLifting.DeligneLusztigFan
