import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Inserting a leaf into an ordered energy-denominator word -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.DirectedHopping

variable {K : Type*} [Field K]

/-- The entries are the old cut energies before the neighbour is reached,
listed backwards. Appending the last possible insertion duplicates its
cut. All earlier insertions acquire the shifted denominator. -/
def leafWeights (g : K) : List K → List K
  | [] => [g⁻¹]
  | s :: tail => (leafWeights g tail).map (· / (s+g)) ++
      [((s :: tail).prod)⁻¹ / (s+g)]

/-- Numerators for the same insertions over the common denominator
g times the products of the old and shifted cut energies. -/
def clearedWeights (g : K) : List K → List K
  | [] => [1]
  | s :: tail => (clearedWeights g tail).map (s * ·) ++
      [g * ((tail.map (· + g)).prod)]

private theorem sum_scaled (a : K) (xs : List K) :
    (xs.map (a * ·)).sum = a * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

/-- The cleared identity holds even if some energy differences vanish. -/
theorem cleared_leaf_sum (g : K) (xs : List K) :
    (clearedWeights g xs).sum = (xs.map (· + g)).prod := by
  induction xs with
  | nil => simp [clearedWeights]
  | cons s tail ih =>
    simp only [clearedWeights,List.sum_append,sum_scaled,ih,List.sum_cons,List.sum_nil,
      add_zero,List.map_cons,List.prod_cons,add_mul]

private theorem sum_divided (a : K) (xs : List K) :
    (xs.map (· / a)).sum = xs.sum / a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,add_div]

/-- Summing all possible positions of a leaf contributes precisely its
own inverse edge energy, independently of the position of its neighbour.
No sign restriction is needed on the intermediate energy differences. -/
theorem leaf_sum (g : K) (hg : g ≠ 0) (xs : List K)
    (h : ∀ s ∈ xs, s ≠ 0 ∧ s+g ≠ 0) :
    (leafWeights g xs).sum = xs.prod⁻¹ / g := by
  induction xs with
  | nil => simp [leafWeights]
  | cons s tail ih =>
    obtain ⟨hs,hshift⟩ := h s List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [leafWeights,List.sum_append,sum_divided,ht,List.sum_cons,List.sum_nil,
      add_zero,List.prod_cons,mul_inv_rev]
    field_simp [hg,hs,hshift]
    <;> ring

#print axioms cleared_leaf_sum
#print axioms leaf_sum

end GaloisForLFunctions.HTGeometry.SpectralJets.DirectedHopping
