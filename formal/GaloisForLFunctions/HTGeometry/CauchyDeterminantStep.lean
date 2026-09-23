import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# The consecutive Cauchy determinant relation

Peeling the last index off both products in the Cauchy determinant gives a division-free relation
between consecutive determinants of a symmetric Cauchy matrix:

`det Cₙ₊₁ · (∏ᵢ (xᵢ + t))² · (2t) = det Cₙ · (∏ᵢ (xᵢ - t))²`,

where `t` is the last node.  Combined with the Gram-determinant recursion this is the exact squared
distance from one half-line exponential to the span of the earlier ones.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- The strict upper set of a `castSucc` index. -/
theorem Ioi_castSucc {N : ℕ} (i : Fin N) :
    Finset.Ioi (Fin.castSucc i) =
      insert (Fin.last N) (Finset.map Fin.castSuccEmb (Finset.Ioi i)) := by
  ext j
  simp only [Finset.mem_Ioi, Finset.mem_insert, Finset.mem_map, Fin.castSuccEmb_apply,
    Finset.mem_Ioi]
  constructor
  · revert j
    refine Fin.lastCases ?_ ?_
    · intro _
      exact Or.inl rfl
    · intro j' hj'
      exact Or.inr ⟨j', by simpa using hj', rfl⟩
  · rintro (rfl | ⟨j', hj', rfl⟩)
    · exact Fin.castSucc_lt_last i
    · simpa using hj'

theorem prod_Ioi_castSucc {M : Type*} [CommMonoid M] {N : ℕ} (i : Fin N)
    (f : Fin (N + 1) → M) :
    ∏ j ∈ Finset.Ioi (Fin.castSucc i), f j =
      f (Fin.last N) * ∏ j ∈ Finset.Ioi i, f (Fin.castSucc j) := by
  rw [Ioi_castSucc, Finset.prod_insert, Finset.prod_map]
  · rfl
  · simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists]
    intro j
    rintro ⟨-, hj⟩
    exact absurd hj (Fin.ne_of_lt (Fin.castSucc_lt_last j))

theorem Ioi_last_eq_empty (N : ℕ) :
    Finset.Ioi (Fin.last N) = (∅ : Finset (Fin (N + 1))) := by
  ext j
  simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, not_lt]
  exact Fin.le_last j

/-- **The consecutive Cauchy determinant relation.** -/
theorem det_cauchyMatrix_castSucc {N : ℕ} (x : Fin (N + 1) → K)
    (hx : ∀ i j, x i + x j ≠ 0) :
    (cauchyMatrix x x).det *
        ((∏ i : Fin N, (x i.castSucc + x (Fin.last N))) ^ (2 : ℕ) *
          (x (Fin.last N) + x (Fin.last N))) =
      (cauchyMatrix (fun i : Fin N => x i.castSucc)
          (fun j : Fin N => x j.castSucc)).det *
        (∏ i : Fin N, (x i.castSucc - x (Fin.last N))) ^ (2 : ℕ) := by
  classical
  set t : K := x (Fin.last N) with ht
  set D : K := ∏ i : Fin N, ∏ j : Fin N, (x i.castSucc + x j.castSucc) with hD
  set A : K := ∏ i : Fin N, (x i.castSucc + t) with hA
  have hfull := det_cauchyMatrix x x hx
  have hsmall := det_cauchyMatrix (fun i : Fin N => x i.castSucc)
    (fun j : Fin N => x j.castSucc) (fun i j => hx _ _)
  have hDne : D ≠ 0 := by
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hx _ _))
  have hdenom : (∏ i, ∏ j, (x i + x j)) = D * (A ^ (2 : ℕ) * (t + t)) := by
    rw [hD, hA, Fin.prod_univ_castSucc]
    have hlast : (∏ j, (x (Fin.last N) + x j)) =
        (∏ j : Fin N, (t + x j.castSucc)) * (t + t) := by
      rw [Fin.prod_univ_castSucc]
    rw [hlast]
    have hrow : ∀ i : Fin N, (∏ j, (x i.castSucc + x j)) =
        (∏ j : Fin N, (x i.castSucc + x j.castSucc)) * (x i.castSucc + t) := by
      intro i
      rw [Fin.prod_univ_castSucc]
    rw [Finset.prod_congr rfl (fun i _ => hrow i), Finset.prod_mul_distrib]
    have hcomm : (∏ j : Fin N, (t + x j.castSucc)) = ∏ j : Fin N, (x j.castSucc + t) :=
      Finset.prod_congr rfl (fun j _ => add_comm _ _)
    rw [hcomm]
    ring
  have hnum : (∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (x i - x j))) =
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        ((x i.castSucc - x j.castSucc) * (x i.castSucc - x j.castSucc))) *
      (∏ i : Fin N, (x i.castSucc - t)) ^ (2 : ℕ) := by
    rw [Fin.prod_univ_castSucc, Ioi_last_eq_empty, Finset.prod_empty, mul_one]
    have hrow : ∀ i : Fin N,
        (∏ j ∈ Finset.Ioi (Fin.castSucc i),
          ((x i.castSucc - x j) * (x i.castSucc - x j))) =
        ((x i.castSucc - t) * (x i.castSucc - t)) *
          ∏ j ∈ Finset.Ioi i,
            ((x i.castSucc - x j.castSucc) * (x i.castSucc - x j.castSucc)) := by
      intro i
      rw [prod_Ioi_castSucc]
    have hsq : (∏ i : Fin N, ((x i.castSucc - t) * (x i.castSucc - t))) =
        (∏ i : Fin N, (x i.castSucc - t)) ^ (2 : ℕ) := by
      rw [Finset.prod_mul_distrib, sq]
    rw [Finset.prod_congr rfl (fun i _ => hrow i), Finset.prod_mul_distrib, hsq, mul_comm]
  rw [hdenom, hnum] at hfull
  refine mul_right_cancel₀ hDne ?_
  calc (cauchyMatrix x x).det * (A ^ (2 : ℕ) * (t + t)) * D
      = (cauchyMatrix x x).det * (D * (A ^ (2 : ℕ) * (t + t))) := by ring
    _ = (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          ((x i.castSucc - x j.castSucc) * (x i.castSucc - x j.castSucc))) *
        (∏ i : Fin N, (x i.castSucc - t)) ^ (2 : ℕ) := hfull
    _ = ((cauchyMatrix (fun i : Fin N => x i.castSucc)
          (fun j : Fin N => x j.castSucc)).det * D) *
        (∏ i : Fin N, (x i.castSucc - t)) ^ (2 : ℕ) := by rw [← hsmall, ← hD]
    _ = (cauchyMatrix (fun i : Fin N => x i.castSucc)
          (fun j : Fin N => x j.castSucc)).det *
        (∏ i : Fin N, (x i.castSucc - t)) ^ (2 : ℕ) * D := by ring

end GaloisForLFunctions.HTGeometry
