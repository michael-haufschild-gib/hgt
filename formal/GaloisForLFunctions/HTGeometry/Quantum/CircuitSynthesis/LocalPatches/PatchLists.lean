import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.RangeLocality
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.AllOrders

/-! # Interaction words in a finite interval of sites -/
open Finset
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- All elementary interactions of a site interval, in a fixed order. -/
def patchList (Z : ℕ → List A) (l r : ℕ) := (Ico l r).toList.flatMap Z

private theorem sum_flat_sites (Z : ℕ → List A) (s : List ℕ) :
    (s.flatMap Z).sum = (s.map fun i => (Z i).sum).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simp [ih]

private theorem mass_flat_sites (Z : ℕ → List A) (s : List ℕ) :
    ProductFormula.mass (s.flatMap Z) = (s.map fun i => ProductFormula.mass (Z i)).sum := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [ProductFormula.mass_append,ih]

theorem sum_patchList (Z : ℕ → List A) (l r : ℕ) :
    (patchList Z l r).sum = intervalSum (fun i => (Z i).sum) l r := by
  simp [patchList,sum_flat_sites,intervalSum]

theorem mass_patchList (Z : ℕ → List A) (l r : ℕ) :
    ProductFormula.mass (patchList Z l r) = ∑ i ∈ Ico l r, ProductFormula.mass (Z i) := by
  simp [patchList,mass_flat_sites]

omit [CStarAlgebra A] in
theorem length_patchList (Z : ℕ → List A) (l r : ℕ) :
    (patchList Z l r).length = ∑ i ∈ Ico l r, (Z i).length := by
  simp [patchList]

omit [CStarAlgebra A] in
theorem mem_patchList {Z : ℕ → List A} {l r : ℕ} {x : A} :
    x ∈ patchList Z l r ↔ ∃ i ∈ Ico l r, x ∈ Z i := by simp [patchList]

theorem mass_patchList_le (Z : ℕ → List A) {M : ℝ} (h : ∀ i, ProductFormula.mass (Z i) ≤ M)
    (l r : ℕ) : ProductFormula.mass (patchList Z l r) ≤ ((r-l:ℕ):ℝ)*M := by
  rw [mass_patchList]
  simpa [Nat.card_Ico] using sum_le_sum (s := Ico l r) (fun i _ => h i)

omit [CStarAlgebra A] in
theorem length_patchList_le (Z : ℕ → List A) {m : ℕ} (h : ∀ i, (Z i).length ≤ m)
    (l r : ℕ) : (patchList Z l r).length ≤ (r-l)*m := by
  rw [length_patchList]
  simpa [Nat.card_Ico] using sum_le_sum (s := Ico l r) (fun i _ => h i)

end
end GaloisForLFunctions.HTGeometry.LocalPatches
