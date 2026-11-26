import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Patterns

/-! # Unordered squarefree occupations as independent draws conditioned to be distinct -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset _root_.RHTower
variable {α : Type*} [Fintype α] [LinearOrder α]

def productWeight (q : α → ℝ) {m : ℕ} (R : BreadthSubset m α) := ∏ p ∈ R.val, q p

def upperCount (H : Finset α) {m : ℕ} (R : BreadthSubset m α) := (R.val.filter (· ∈ H)).card

/-- The count-law of weighted unordered occupations. -/
def subsetRead (q : α → ℝ) (H : Finset α) (m : ℕ) (B : Finset ℕ) :=
  (∑ R : BreadthSubset m α, if upperCount H R ∈ B then productWeight q R else 0) /
    ∑ R : BreadthSubset m α, productWeight q R

private theorem marked_enum (q : α → ℝ) (H : Finset α) (m : ℕ) (B : Finset ℕ) :
    (∑ y ∈ counts m H B, injectiveTupleWeight q y) =
      (m.factorial:ℝ)*∑ R : BreadthSubset m α, if upperCount H R ∈ B then productWeight q R else 0 := by
  classical
  let f (y : Fin m → α) := if (pattern H y).card ∈ B then tupleWeight q y else 0
  have one (y : Fin m → α) :
      (if (pattern H y).card ∈ B then injectiveTupleWeight q y else 0) =
        if Function.Injective y then f y else 0 := by
    by_cases hi : Function.Injective y <;> simp [hi,f,injectiveTupleWeight]
  have sub : (∑ y : Fin m → α, if Function.Injective y then f y else 0) =
      ∑ e : Fin m ↪ α, f e := by
    rw [← sum_filter]
    have hs := sum_subtype_eq_sum_filter (s := (univ : Finset (Fin m → α))) (p := Function.Injective) f
    calc _ = ∑ y : {y : Fin m → α // Function.Injective y}, f y.val := by simpa using hs.symm
         _ = _ := Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin m) α) _ _ (fun _ => rfl)
  let E := embeddingRangePermEquiv m α
  let g (e : Fin m ↪ α) := f e
  have each (R : BreadthSubset m α) (π : Equiv.Perm (Fin m)) :
      g (E.symm (R,π)) = if upperCount H R ∈ B then productWeight q R else 0 := by
    let e := π.trans (R.val.orderIsoOfFin R.property).toEquiv
    have same : (pattern H (E.symm (R,π))).card = upperCount H R := by
      simp only [pattern,upperCount,card_filter]
      calc _ = ∑ p : ↥R.val, if (p:α) ∈ H then 1 else 0 :=
                  Fintype.sum_equiv e _ _ (fun _ => rfl)
           _ = _ := sum_coe_sort R.val (fun p => if p ∈ H then (1:ℕ) else 0)
    change (if (pattern H (E.symm (R,π))).card ∈ B then tupleWeight q _ else 0) = _
    rw [same]
    exact congrArg (fun z : ℝ => if upperCount H R ∈ B then z else 0) (prod_embedding_eq_prod_range m α q R π)
  rw [counts,sum_filter]
  simp only [one,sub]
  change (∑ e, g e) = _
  rw [← E.symm.sum_comp g,Fintype.sum_prod_type]
  simp only [each,sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,mul_sum]

/-- Uniform event error between the physical exclusion law and the binomial experiment. -/
theorem subset_error (q : α → ℝ) (hq : ∀ x, 0 ≤ q x) (hn : ∑ x, q x = 1) (H : Finset α) (m : ℕ) (B : Finset ℕ) :
    |subsetRead q H m B-binEvent m B (∑ x ∈ H, q x)| ≤ repeatMass q m := by
  classical
  have good (y : Fin m → α) : 0 ≤ injectiveTupleWeight q y ∧ injectiveTupleWeight q y ≤ tupleWeight q y := by
    by_cases hi : Function.Injective y <;> simp [injectiveTupleWeight,hi,tupleWeight_nonneg q hq y]
  have total : (∑ y : Fin m → α, tupleWeight q y) = 1 := by rw [sum_tupleWeight,hn,one_pow]
  have h := conditioning_error (tupleWeight q) (injectiveTupleWeight q) (fun y => (good y).1)
    (fun y => (good y).2) total (counts m H B)
  change _ ≤ repeatMass q m at h
  rw [marked_enum,sum_injectiveTupleWeight,iid_count q hn,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial:ℝ) ≠ 0)] at h
  exact h

#print axioms subset_error

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
