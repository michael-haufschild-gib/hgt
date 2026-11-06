import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.InvariantForms

/-!
# Nonzero invariant forms in every even degree

Products of determinants on disjoint pairs of vectors give invariant multilinear
forms of every even degree. Evaluation on repeated standard bases is one, so the
invariant determinant-weight law is nonvacuous in every even degree.
-/

open Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

private def pairIndexEquiv (k : ℕ) : (Σ _ : Fin k, Fin 2) ≃ Fin (2 * k) :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

/-- Product of the volume forms on a fixed pairing of the tensor slots. -/
def determinantPairs (k : ℕ) : TensorForm (2 * k) :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compMultilinearMap
    (fun _ => (Matrix.detRowAlternating : Plane [⋀^Fin 2]→ₗ[ℂ] ℂ).toMultilinearMap)).domDomCongr
      (pairIndexEquiv k)

theorem determinantPairs_apply (k : ℕ) (v : Fin (2 * k) → Plane) :
    determinantPairs k v = ∏ i : Fin k,
      Matrix.det (fun j : Fin 2 => v (pairIndexEquiv k ⟨i, j⟩)) := rfl

private theorem det_pair_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → Plane) :
    Matrix.det (fun i => A.mulVec (v i)) = A.det * Matrix.det v := by
  simp only [Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- A paired volume form transforms by the determinant character, including at singular frames. -/
theorem determinantPairs_mulVec (k : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin (2 * k) → Plane) :
    determinantPairs k (fun i => A.mulVec (v i)) = A.det ^ k * determinantPairs k v := by
  simp only [determinantPairs_apply, det_pair_mulVec, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem determinantPairs_mem (k : ℕ) : determinantPairs k ∈ invariantForms (2 * k) := by
  intro A hA v
  rw [determinantPairs_mulVec, hA, one_pow, one_mul]

theorem determinantPairs_ne_zero (k : ℕ) : determinantPairs k ≠ 0 := by
  let v : Fin (2 * k) → Plane := fun i => (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ((pairIndexEquiv k).symm i).2
  have hpair (i : Fin k) :
      (fun j : Fin 2 => v (pairIndexEquiv k ⟨i, j⟩)) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext j
    dsimp only [v]
    rw [Equiv.symm_apply_apply]
  have hv : determinantPairs k v = 1 := by
    simp only [determinantPairs_apply, hpair, Matrix.det_one, Finset.prod_const_one]
  intro h
  rw [h] at hv
  exact zero_ne_one hv

/-- Every even invariant space contains a nonzero form. -/
theorem exists_nonzero_even_invariant (k : ℕ) :
    ∃ f : invariantForms (2 * k), f.val ≠ 0 :=
  ⟨⟨determinantPairs k, determinantPairs_mem k⟩, determinantPairs_ne_zero k⟩

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
