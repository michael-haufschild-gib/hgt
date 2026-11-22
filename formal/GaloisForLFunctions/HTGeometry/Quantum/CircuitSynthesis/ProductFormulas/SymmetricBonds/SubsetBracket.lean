import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.NestedMass

/-! # Nested commutators of partial sums of path terms -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open LocalPatches
variable {R : Type*} [CStarAlgebra R]

private theorem sum_left {ι : Type*} (s : Finset ι) (f : ι→R) (a : R) :
    bracketStep (∑ i∈s,f i) a=∑ i∈s,bracketStep (f i) a := by
  simp only [bracketStep,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]

private theorem sum_right {ι : Type*} (s : Finset ι) (f : ι→R) (a : R) :
    bracketStep a (∑ i∈s,f i)=∑ i∈s,bracketStep a (f i) := by
  simp only [bracketStep,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]

private theorem bracket_sums {ι : Type*} [Fintype ι] (I J K : Finset ι) (X : ι→R) :
    ‖bracketStep (∑ i∈I,X i) (bracketStep (∑ j∈J,X j) (∑ k∈K,X k))‖ ≤
      ∑ j, ∑ k, ∑ i, ‖bracketStep (X i) (bracketStep (X j) (X k))‖ := by
  let f j k i := bracketStep (X i) (bracketStep (X j) (X k))
  have he : bracketStep (∑ i∈I,X i) (bracketStep (∑ j∈J,X j) (∑ k∈K,X k))=
      ∑ j∈J, ∑ k∈K, ∑ i∈I, f j k i := by
    rw [sum_left J,sum_right J]
    apply Finset.sum_congr rfl
    intro j _
    rw [sum_right K,sum_right K]
    exact Finset.sum_congr rfl fun k _ => sum_left I X _
  rw [he]
  have hs {s : Finset ι} (g : ι→ℝ) (hg : ∀ i, 0≤g i) : ∑ i∈s, g i ≤ ∑ i,g i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => hg i
  apply (norm_sum_le _ _).trans
  apply le_trans _ (hs _ fun j => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => norm_nonneg (f j k i))
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply le_trans _ (hs _ fun k => Finset.sum_nonneg fun i _ => norm_nonneg (f j k i))
  exact Finset.sum_le_sum fun k _ => (norm_sum_le ..).trans (hs _ fun i => norm_nonneg (f j k i))

local instance (N : ℕ) : CStarAlgebra (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) where

/-- A uniform estimate for any three subsets, including the repeated
parity layers; no disjointness convention for the subsets is required. -/
theorem subset_nested_mass {n : ℕ} (u : PathShell n) (I J K : Finset (PathLabel n)) :
    let X := pathTermGenerator u
    ‖bracketStep (∑ i∈I,X i) (bracketStep (∑ j∈J,X j) (∑ k∈K,X k))‖ ≤ (24*42^2)*∑ i, |u i|^3 :=
  (bracket_sums I J K (pathTermGenerator u)).trans (path_nested_mass u)

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
