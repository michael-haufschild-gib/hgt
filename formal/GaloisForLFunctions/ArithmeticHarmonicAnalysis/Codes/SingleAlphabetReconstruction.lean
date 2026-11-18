import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementPolynomial
import Mathlib.Algebra.BigOperators.Fin

/-!
# Recovering a face vector from a single point count

The coefficient of each torus dimension counts a family of subsets of the
vertex set. At any base larger than its power set, these coefficients are
already digits. A single alphabet therefore determines every face number.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section

private theorem radix_injective (b : ℕ) (hb : 0 < b) (n : ℕ) :
    Function.Injective (fun a : Fin n → Fin b => ∑ i, (a i).val * b ^ i.val) := by
  induction n with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro a c h
    change (∑ i, (a i).val * b ^ i.val) = ∑ i, (c i).val * b ^ i.val at h
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc,
      ← sum_mul] at h
    have h₀ := congrArg (fun k => k % b) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (a 0).isLt,
      Nat.mod_eq_of_lt (c 0).isLt] at h₀
    rw [h₀] at h
    have ht := Nat.eq_of_mul_eq_mul_right hb (Nat.add_left_cancel h)
    have hf : (fun i : Fin n => a i.succ) = (fun i => c i.succ) := ih ht
    funext i
    exact Fin.cases (Fin.ext h₀) (fun i => congrFun hf i) i

variable {ι : Type*} [Fintype ι]

private def layer (K : Finset (Finset ι)) (d : ℕ) : Finset (Finset ι) :=
  K.filter fun s => Fintype.card ι - s.card = d

private theorem regroup_layers (K : Finset (Finset ι)) (b : ℕ) :
    (∑ d : Fin (Fintype.card ι + 1), (layer K d).card * b ^ d.val) =
      ∑ s ∈ K, b ^ (Fintype.card ι - s.card) := by
  have hl (d : Fin (Fintype.card ι + 1)) : (layer K d).card * b ^ d.val =
      ∑ s ∈ K, if Fintype.card ι - s.card = d.val then b ^ d.val else 0 := by
    rw [← sum_filter]
    simp [layer]
  simp_rw [hl]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  let j : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι - s.card, by omega⟩
  rw [sum_eq_single j]
  · simp [j]
  · intro i _ hij
    exact if_neg (fun h => hij (Fin.ext h.symm))
  · simp

/-- Ordinary positional uniqueness for two face polynomials whose layer
sizes are all digits in the specified base. -/
private theorem layer_digits_reconstruct (K L : Finset (Finset ι)) (b : ℕ) (hb : 0 < b)
    (hbound : ∀ (S : Finset (Finset ι)) (d : ℕ), (layer S d).card < b) :
    (arrangementWords (fun _ : ι => ({0} : Finset (Fin (b+1)))) K).card =
      (arrangementWords (fun _ : ι => ({0} : Finset (Fin (b+1)))) L).card ↔
      arrangementPolynomial K = arrangementPolynomial L := by
  let digits (S : Finset (Finset ι)) (i : Fin (Fintype.card ι+1)) : Fin b :=
    ⟨(layer S i).card, hbound S i⟩
  rw [card_pointArrangement, card_pointArrangement, Fintype.card_fin, Nat.add_sub_cancel,
    ← regroup_layers, ← regroup_layers, arrangementPolynomial_eq_iff]
  constructor
  · intro h d
    have hd : digits K = digits L := radix_injective b hb (Fintype.card ι + 1) h
    by_cases hdim : d ≤ Fintype.card ι
    · exact congrArg Fin.val (congrFun hd ⟨d, by omega⟩)
    · have he (S : Finset (Finset ι)) : layer S d = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have ht := (mem_filter.mp hs).2
        omega
      change (layer K d).card = (layer L d).card
      rw [he, he]
  · intro h
    exact sum_congr rfl fun i _ => congrArg (· * b ^ i.val) (h i.val)

/-- An alphabet with more than `2^n` nondistinguished letters determines
the entire counting polynomial from one point count. -/
theorem singleAlphabet_eq_iff (K L : Finset (Finset ι)) (extra : ℕ) :
    let b := 2 ^ Fintype.card ι + extra + 1
    let D := fun _ : ι => ({0} : Finset (Fin (b+1)))
    (arrangementWords D K).card = (arrangementWords D L).card ↔
      arrangementPolynomial K = arrangementPolynomial L := by
  apply layer_digits_reconstruct K L _ (Nat.succ_pos _)
  intro S d
  have h := (layer S d).card_le_univ
  rw [Fintype.card_finset] at h
  omega

#print axioms singleAlphabet_eq_iff

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
