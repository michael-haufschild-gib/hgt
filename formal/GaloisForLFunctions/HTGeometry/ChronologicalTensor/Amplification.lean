import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Fusion
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Reversal

/-!
# Collective response beyond the capacity of every expansion term

The normalized independent product expands over Boolean choices of separated or
rainbow blocks. Every one of these `2^n` terms has capacity exactly one, with a
constructive maximizing probe for every choice. Their sum has the exponentially
larger exact capacity `sixCapacity^n`, by the fusion theorems.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def chosenResponse (choice : Bool) (a b c d e : ℝ) : ℝ :=
  if choice then 27*separatedThree a b c d e else rainbowThree a b c d e

def normalizedTerm (n : ℕ) (choice : Fin n → Bool) (a b c d e : Fin n → ℝ) : ℝ :=
  (n : ℝ)^(3*n) * ∏ i, chosenResponse (choice i) (a i) (b i) (c i) (d i) (e i)

theorem chosenResponse_bound (choice : Bool) (a b c d e : ℝ) :
    |chosenResponse choice a b c d e| ≤ sixCost a b c d e ^ (3 : ℕ) := by
  cases choice
  · exact rainbow_bound a b c d e
  · exact normalized_separated_bound a b c d e

theorem normalizedTerm_bound (n : ℕ) (choice : Fin n → Bool) (a b c d e : Fin n → ℝ) :
    |normalizedTerm n choice a b c d e| ≤ blockCost n a b c d e ^ (3*n) := by
  have hc : ∀ i, 0 ≤ sixCost (a i) (b i) (c i) (d i) (e i) := by
    intro i; unfold sixCost; positivity
  have hp := prod_le_prod (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      abs_nonneg (chosenResponse (choice i) (a i) (b i) (c i) (d i) (e i)))
    (fun i _ => chosenResponse_bound (choice i) (a i) (b i) (c i) (d i) (e i))
  have hm := mass_product_bound n (fun i => sixCost (a i) (b i) (c i) (d i) (e i))
  simp only [abs_of_nonneg (hc _)] at hm
  have hm3 := pow_le_pow_left₀ (show 0 ≤ (n : ℝ)^n *
    ∏ i, sixCost (a i) (b i) (c i) (d i) (e i) by
      exact mul_nonneg (by positivity) (prod_nonneg (fun i _ => hc i))) hm 3
  calc
    _ = (n : ℝ)^(3*n) * ∏ i, |chosenResponse (choice i) (a i) (b i) (c i) (d i) (e i)| := by
      rw [normalizedTerm, abs_mul, abs_of_nonneg (by positivity), Finset.abs_prod]
    _ ≤ (n : ℝ)^(3*n) * ∏ i, sixCost (a i) (b i) (c i) (d i) (e i)^(3 : ℕ) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((n : ℝ)^n * ∏ i, sixCost (a i) (b i) (c i) (d i) (e i))^(3 : ℕ) := by
      rw [prod_pow, mul_pow, ← pow_mul, Nat.mul_comm n 3]
    _ ≤ ((∑ i, sixCost (a i) (b i) (c i) (d i) (e i))^n)^(3 : ℕ) := hm3
    _ = _ := by rw [← pow_mul, Nat.mul_comm n 3]; rfl

theorem chosenResponse_scale (choice : Bool) (t a b c d e : ℝ) :
    chosenResponse choice (t*a) (t*b) (t*c) (t*d) (t*e) =
      t^(3 : ℕ) * chosenResponse choice a b c d e := by
  cases choice <;> simp only [chosenResponse, Bool.false_eq_true, if_false, if_true,
    separatedThree, rainbowThree] <;> ring

def chosenA (choice : Bool) : ℝ := if choice then 1/3 else 0
def chosenC (choice : Bool) : ℝ := if choice then 1/3 else 1

theorem chosen_witness (choice : Bool) :
    sixCost (chosenA choice) 0 (chosenC choice) 0 (chosenA choice) = 1 ∧
    chosenResponse choice (chosenA choice) 0 (chosenC choice) 0 (chosenA choice) = 1 := by
  cases choice <;> constructor <;>
    simp [sixCost, chosenA, chosenC, chosenResponse, separatedThree, rainbowThree] <;> ring

theorem normalizedTerm_attained (n : ℕ) (choice : Fin (n+1) → Bool) :
    ∃ a b c d e : Fin (n+1) → ℝ,
      blockCost (n+1) a b c d e = 1 ∧ normalizedTerm (n+1) choice a b c d e = 1 := by
  let t : ℝ := 1/(n+1)
  have hn : (0 : ℝ) < n+1 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let a : Fin (n+1) → ℝ := fun i => t*chosenA (choice i)
  let c : Fin (n+1) → ℝ := fun i => t*chosenC (choice i)
  have hcost (i : Fin (n+1)) : sixCost (a i) 0 (c i) 0 (a i) = t := by
    have h := sixCost_scale t (chosenA (choice i)) 0 (chosenC (choice i)) 0 (chosenA (choice i))
    simpa only [mul_zero, (chosen_witness (choice i)).1, abs_of_nonneg ht, mul_one] using h
  have hval (i : Fin (n+1)) : chosenResponse (choice i) (a i) 0 (c i) 0 (a i) = t^(3 : ℕ) := by
    have h := chosenResponse_scale (choice i) t (chosenA (choice i)) 0 (chosenC (choice i)) 0 (chosenA (choice i))
    simpa only [mul_zero, (chosen_witness (choice i)).2, mul_one] using h
  refine ⟨a, fun _ => 0, c, fun _ => 0, a, ?_, ?_⟩
  · simp only [blockCost, hcost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, t]
    field_simp
  · simp only [normalizedTerm, hval, prod_const, card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one, t, one_div, inv_pow, ← pow_mul]
    field_simp

theorem fused_expansion (n : ℕ) (a b c d e : Fin n → ℝ) :
    fusedResponse n a b c d e = ∑ choice : Fin n → Bool, normalizedTerm n choice a b c d e := by
  have h := Fintype.prod_sum (fun (i : Fin n) (choice : Bool) =>
    chosenResponse choice (a i) (b i) (c i) (d i) (e i))
  simp only [Fintype.sum_bool, chosenResponse, Bool.false_eq_true, if_false, if_true] at h
  simp only [fusedResponse, normalizedTerm, ← mul_sum]
  congr 1

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
