import Mathlib

/-!
# Subadditivity of matrix rank

The rank of a sum is at most the sum of the ranks, and scaling cannot raise the rank.  Mathlib has
the rank of a single outer product but neither of these two closure properties, which are what
bounds the rank of an explicitly presented finite Gram sum.

Both are read off the column space: the range of the matrix action of a sum lies in the join of the
two ranges, and the join has finite rank at most the sum of the two ranks by the modular law.
-/

namespace GaloisForLFunctions
namespace HTGeometry

open Matrix

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

/-- **Rank is subadditive.** -/
theorem rank_add_le_rank_add_rank (A B : Matrix ι ι K) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rintro _ ⟨y, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨y, rfl⟩ ⟨y, rfl⟩
  have h1 : Module.finrank K (LinearMap.range (Matrix.mulVecLin (A + B)))
      ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin A) ⊔
        LinearMap.range (Matrix.mulVecLin B) : Submodule K (ι → K)) :=
    Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.mulVecLin A)) (LinearMap.range (Matrix.mulVecLin B))
  simp only [Matrix.rank]
  omega

/-- **Scaling cannot raise the rank.** -/
theorem rank_smul_le (c : K) (A : Matrix ι ι K) : (c • A).rank ≤ A.rank := by
  have hle : LinearMap.range (Matrix.mulVecLin (c • A)) ≤
      LinearMap.range (Matrix.mulVecLin A) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨c • y, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    funext i
    simp [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm]
  simpa only [Matrix.rank] using Submodule.finrank_mono hle

/-- **Rank is subadditive over finite sums.**  An explicitly presented finite Gram sum has rank at
most the total rank of its terms. -/
theorem rank_sum_le {α : Type*} (s : Finset α) (A : α → Matrix ι ι K) :
    (∑ a ∈ s, A a).rank ≤ ∑ a ∈ s, (A a).rank := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hzero : Matrix.mulVecLin (0 : Matrix ι ι K) = 0 := by
        ext x i
        simp
      rw [Finset.sum_empty, Matrix.rank, hzero, LinearMap.range_zero, finrank_bot,
        Finset.sum_empty]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (rank_add_le_rank_add_rank _ _) (Nat.add_le_add_left ih _)

/-! ### The exact rank of a two-term Gram sum

Rank subadditivity bounds a presented Gram sum from above.  For a sum of two outer products the
bound is attained exactly when the two feature vectors are independent, and the mechanism is the
strict positivity of their Gram determinant.
-/

variable {ι : Type*} [Fintype ι]

/-- A real self dot product is nonnegative. -/
theorem dotProduct_self_nonneg (u : ι → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- A real self dot product vanishes only at the zero vector. -/
theorem dotProduct_self_pos {u : ι → ℝ} (hu : u ≠ 0) : 0 < u ⬝ᵥ u := by
  rcases (dotProduct_self_nonneg u).lt_or_eq with h | h
  · exact h
  · exact absurd (funext fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (u j))).mp h.symm i (Finset.mem_univ i)
      simpa using mul_self_eq_zero.mp this) hu

/-- **The Gram determinant of an independent pair is strictly positive.**  Completing the square in
`t ↦ (v + t • u) ⬝ᵥ (v + t • u)`, which is strictly positive because independence forbids the
vanishing of every translate, gives the strict Cauchy--Schwarz inequality. -/
theorem gramDet_pos_of_linearIndependent {u v : ι → ℝ}
    (h : LinearIndependent ℝ ![u, v]) :
    0 < (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ) := by
  have hpair := LinearIndependent.pair_iff.mp h
  have hu : u ≠ 0 := by
    intro h0
    exact one_ne_zero (hpair 1 0 (by simp [h0])).1
  have ha : 0 < u ⬝ᵥ u := dotProduct_self_pos hu
  have hne : (u ⬝ᵥ u) ≠ 0 := ne_of_gt ha
  have hw : v + (-(u ⬝ᵥ v) / (u ⬝ᵥ u)) • u ≠ 0 := by
    intro h0
    exact one_ne_zero (hpair (-(u ⬝ᵥ v) / (u ⬝ᵥ u)) 1 (by rw [one_smul, add_comm]; exact h0)).2
  have hpos := dotProduct_self_pos hw
  have hexp : ∀ t : ℝ, (v + t • u) ⬝ᵥ (v + t • u)
      = (v ⬝ᵥ v) + 2 * t * (u ⬝ᵥ v) + t ^ (2 : ℕ) * (u ⬝ᵥ u) := by
    intro t
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm v u]
    ring
  rw [hexp] at hpos
  have hid : (v ⬝ᵥ v) + 2 * (-(u ⬝ᵥ v) / (u ⬝ᵥ u)) * (u ⬝ᵥ v)
        + (-(u ⬝ᵥ v) / (u ⬝ᵥ u)) ^ (2 : ℕ) * (u ⬝ᵥ u)
      = ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ)) / (u ⬝ᵥ u) := by
    field_simp
    ring
  rw [hid] at hpos
  exact (div_pos_iff_of_pos_right ha).mp hpos

/-- The action of a Cauchy outer product is a multiple of its feature vector. -/
theorem vecMulVec_mulVec_self (u y : ι → ℝ) :
    Matrix.mulVec (Matrix.vecMulVec u u) y = (u ⬝ᵥ y) • u := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The action of a two-term Gram sum on a vector. -/
theorem gramPair_mulVec (u v y : ι → ℝ) :
    Matrix.mulVec (Matrix.vecMulVec u u + Matrix.vecMulVec v v) y
      = (u ⬝ᵥ y) • u + (v ⬝ᵥ y) • v := by
  rw [Matrix.add_mulVec, vecMulVec_mulVec_self, vecMulVec_mulVec_self]

/-- The inverse of a nonsingular symmetric two-by-two Gram matrix. -/
theorem gram_two_by_two_solve {a b c D : ℝ} (hD : D = a * c - b ^ (2 : ℕ)) (hDne : D ≠ 0) :
    (c / D) * a + (-b / D) * b = 1 ∧ (c / D) * b + (-b / D) * c = 0 ∧
      (-b / D) * a + (a / D) * b = 0 ∧ (-b / D) * b + (a / D) * c = 1 := by
  subst hD
  have hDne' : c * a - b ^ (2 : ℕ) ≠ 0 := by rw [mul_comm c a]; exact hDne
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **An independent pair is recovered from its Gram sum.**  Both feature vectors lie in the column
space, because the inverse of their Gram matrix produces the required coefficients. -/
theorem span_pair_le_range_gramPair {u v : ι → ℝ} (h : LinearIndependent ℝ ![u, v]) :
    Submodule.span ℝ {u, v}
      ≤ LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec u u + Matrix.vecMulVec v v)) := by
  have hD : 0 < (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ) := gramDet_pos_of_linearIndependent h
  obtain ⟨e1, e2, e3, e4⟩ := gram_two_by_two_solve (a := u ⬝ᵥ u) (b := u ⬝ᵥ v) (c := v ⬝ᵥ v)
    (D := (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ)) rfl (ne_of_gt hD)
  have hmem : ∀ α β : ℝ,
      Matrix.mulVecLin (Matrix.vecMulVec u u + Matrix.vecMulVec v v) (α • u + β • v)
        = (α * (u ⬝ᵥ u) + β * (u ⬝ᵥ v)) • u + (α * (u ⬝ᵥ v) + β * (v ⬝ᵥ v)) • v := by
    intro α β
    rw [Matrix.mulVecLin_apply, gramPair_mulVec]
    have h1 : u ⬝ᵥ (α • u + β • v) = α * (u ⬝ᵥ u) + β * (u ⬝ᵥ v) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h2 : v ⬝ᵥ (α • u + β • v) = α * (u ⬝ᵥ v) + β * (v ⬝ᵥ v) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        dotProduct_comm v u]
    rw [h1, h2]
  have hu : u ∈ LinearMap.range
      (Matrix.mulVecLin (Matrix.vecMulVec u u + Matrix.vecMulVec v v)) := by
    refine ⟨((v ⬝ᵥ v) / ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ))) • u
      + (-(u ⬝ᵥ v) / ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ))) • v, ?_⟩
    rw [hmem, e1, e2, one_smul, zero_smul, add_zero]
  have hv : v ∈ LinearMap.range
      (Matrix.mulVecLin (Matrix.vecMulVec u u + Matrix.vecMulVec v v)) := by
    refine ⟨(-(u ⬝ᵥ v) / ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ))) • u
      + ((u ⬝ᵥ u) / ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ (2 : ℕ))) • v, ?_⟩
    rw [hmem, e3, e4, one_smul, zero_smul, zero_add]
  refine Submodule.span_le.mpr ?_
  rintro w (rfl | rfl)
  · exact hu
  · simpa using hv

/-- **A two-term Gram sum of independent features has rank exactly two.** -/
theorem rank_gramPair_eq_two [DecidableEq ι] {u v : ι → ℝ} (h : LinearIndependent ℝ ![u, v]) :
    (Matrix.vecMulVec u u + Matrix.vecMulVec v v).rank = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (rank_add_le_rank_add_rank _ _) ?_
    have h1 := Matrix.rank_vecMulVec_le u u
    have h2 := Matrix.rank_vecMulVec_le v v
    omega
  · have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range ![u, v])) = 2 := by
      simpa using finrank_span_eq_card h
    have hset : Set.range ![u, v] = ({u, v} : Set (ι → ℝ)) := by
      ext w
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    rw [hset] at hspan
    calc (2 : ℕ) = Module.finrank ℝ (Submodule.span ℝ ({u, v} : Set (ι → ℝ))) := hspan.symm
      _ ≤ Module.finrank ℝ (LinearMap.range
            (Matrix.mulVecLin (Matrix.vecMulVec u u + Matrix.vecMulVec v v))) :=
          Submodule.finrank_mono (span_pair_le_range_gramPair h)
      _ = (Matrix.vecMulVec u u + Matrix.vecMulVec v v).rank := rfl

/-- **Scaling by a nonzero scalar preserves the rank.** -/
theorem rank_smul_eq {K : Type*} [Field K] {c : K} (hc : c ≠ 0) (A : Matrix ι ι K) :
    (c • A).rank = A.rank := by
  refine le_antisymm (rank_smul_le c A) ?_
  have h : A = c⁻¹ • (c • A) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  calc A.rank = (c⁻¹ • (c • A)).rank := by rw [← h]
    _ ≤ (c • A).rank := rank_smul_le _ _

end HTGeometry
end GaloisForLFunctions
