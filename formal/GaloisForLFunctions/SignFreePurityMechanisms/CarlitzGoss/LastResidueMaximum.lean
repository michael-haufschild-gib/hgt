import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.LastBlockOperations

/-!
# Largest powers and equal labels in the last part

Increasing allocation puts a largest available power of every occupied residue
class in the last part. Labels distinguishing equal powers can be exchanged
without changing numerical values, optimality, or greediness. Deleting the
same final block from two compositions preserves equality of their value vectors.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

omit [NeZero s] in
/-- Weight optimality depends only on numerical part values. -/
theorem isOptimal_congr_values {C D : DigitComposition p s m S} (h : C.value = D.value) :
    C.IsOptimal ↔ D.IsOptimal := by
  have hw : C.weight = D.weight := by simp only [weight, h]
  simp only [IsOptimal, hw]

omit [NeZero s] in
/-- Greediness depends only on numerical part values. -/
theorem isGreedy_congr_values {C D : DigitComposition p s m S} (h : C.value = D.value) :
    C.IsGreedy ↔ D.IsGreedy := by
  have hr : C.reverseValues = D.reverseValues := by simp only [reverseValues, h]
  simp only [IsGreedy, hr]

omit [NeZero s] in
/-- Deleting the same final block preserves equality and inequality of numerical compositions. -/
theorem removeLast_values_eq_iff {T : Finset (Digit p)}
    (C D : DigitComposition p s (m + 1) S)
    (hTC : T ⊆ C.parts (Fin.last m)) (hTD : T ⊆ D.parts (Fin.last m))
    (hneC : (C.parts (Fin.last m) \ T).Nonempty) (hneD : (D.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hTC hneC).value = (D.removeLast hTD hneD).value ↔ C.value = D.value := by
  constructor
  · intro hv
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hh := congrFun hv (Fin.last m)
      rw [removeLast_values, removeLast_values, Fin.snoc_last, Fin.snoc_last] at hh
      linarith only [hh]
    · have hh := congrFun hv j.castSucc
      rw [removeLast_values, removeLast_values, Fin.snoc_castSucc, Fin.snoc_castSucc] at hh
      exact hh
  · intro hv
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [removeLast_values, removeLast_values, Fin.snoc_last, Fin.snoc_last, hv]
    · rw [removeLast_values, removeLast_values, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact congrFun hv j.castSucc

omit [NeZero s] in
/-- An occupied residue class in the last part contains one of its largest available powers. -/
theorem TauMonotone.exists_last_max {C : DigitComposition p s (m + 1) S}
    (hC : C.TauMonotone) {h : ZMod s}
    (hne : ((C.parts (Fin.last m)).filter fun x => (x.1 : ZMod s) = h).Nonempty) :
    ∃ y ∈ C.parts (Fin.last m), (y.1 : ZMod s) = h ∧
      ∀ x ∈ S, (x.1 : ZMod s) = h → x.1 ≤ y.1 := by
  obtain ⟨y, hy, hmax⟩ :=
    ((C.parts (Fin.last m)).filter fun x => (x.1 : ZMod s) = h).exists_max_image Prod.fst hne
  refine ⟨y, (mem_filter.mp hy).1, (mem_filter.mp hy).2, ?_⟩
  intro x hx hxh
  obtain ⟨i, hi⟩ := C.cover x hx
  by_cases he : i = Fin.last m
  · exact hmax x (mem_filter.mpr ⟨he ▸ hi, hxh⟩)
  · have hilast : i < Fin.last m := by
      change i.val < m
      have hilt := i.isLt
      have hine : i.val ≠ m := fun hh => he (Fin.ext hh)
      omega
    exact hC i (Fin.last m) hilast x hi y (mem_filter.mp hy).1
      (hxh.trans (mem_filter.mp hy).2.symm)

/-- Relabelling equal powers changes no numerical part value. -/
theorem relabel_value_eq (C : DigitComposition p s m S) (hp : 2 ≤ p)
    (e : Equiv.Perm (Digit p)) (hS : ∀ x, x ∈ S ↔ e x ∈ S)
    (hc : ∀ x, ((e x).1 : ZMod s) = (x.1 : ZMod s))
    (he : ∀ x, (e x).1 = x.1) : (C.relabel hp e hS hc).value = C.value := by
  funext i
  change (∑ x ∈ (C.parts i).image e, (p : ℤ) ^ x.1) = ∑ x ∈ C.parts i, (p : ℤ) ^ x.1
  rw [sum_image]
  · exact sum_congr rfl fun x _ => congrArg (fun n => (p : ℤ) ^ n) (he x)
  · exact fun x _ y _ h => e.injective h

/-- Equal exponent occurrences can exchange labels without changing any part value. -/
theorem swapDigits_values_eq_of_exponent_eq (C : DigitComposition p s m S) (hp : 2 ≤ p)
    {x y : Digit p} (hx : x ∈ S) (hy : y ∈ S) (he : x.1 = y.1) :
    (C.swapDigits hp hx hy (congrArg (fun n : ℕ => (n : ZMod s)) he)).value = C.value := by
  apply C.relabel_value_eq
  exact Equiv.apply_swap_eq_self (v := fun t : Digit p => t.1) he

/-- A prescribed label of an existing last-part power can be moved there without changing values. -/
theorem exists_same_values_last_mem (C : DigitComposition p s (m + 1) S) (hp : 2 ≤ p)
    {x y : Digit p} (hx : x ∈ S) (hy : y ∈ C.parts (Fin.last m)) (he : x.1 = y.1) :
    ∃ D : DigitComposition p s (m + 1) S, D.value = C.value ∧ x ∈ D.parts (Fin.last m) := by
  let D := C.swapDigits hp hx (C.subset _ hy) (congrArg (fun n : ℕ => (n : ZMod s)) he)
  refine ⟨D, C.swapDigits_values_eq_of_exponent_eq hp hx (C.subset _ hy) he, ?_⟩
  change x ∈ (C.parts (Fin.last m)).image (Equiv.swap x y)
  exact mem_image.mpr ⟨y, hy, Equiv.swap_apply_right x y⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.TauMonotone.exists_last_max
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_same_values_last_mem
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.removeLast_values_eq_iff
