import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentMatrixRealization
import Mathlib.Order.Fin.Tuple

/-!
# Realizing nested inverse-content prefixes

Integral inverse-prefix increments at least one give divisible positive
columns. Nested contents and a positive terminal remainder yield an actual
increasing digit allocation with exactly the prescribed cumulative contents.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

theorem sum_fin_prefix_differences (f : ℕ → ℤ) (m : ℕ) :
    (∑ i : Fin m, (f (i.val + 1) - f i.val)) = f m - f 0 := by
  induction m with
  | zero => simp only [Finset.univ_eq_empty, sum_empty, sub_self]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

namespace DigitComposition
variable {p s : ℕ} [NeZero s]

omit [NeZero s] in
/-- Consecutive digit-prefix contents differ by the intervening part content. -/
theorem prefix_content_succ {m : ℕ} {S : Finset (Digit p)}
    (C : DigitComposition p s m S) (i : Fin m) (h : ZMod s) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (i.val + 1)) h =
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits i.val) h + C.content i h := by
  have hsets : univ.filter (fun j : Fin m => j.val < i.val + 1) =
      insert i (univ.filter fun j : Fin m => j.val < i.val) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hj
      by_cases he : j = i
      · exact Or.inl he
      · right
        have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
        omega
    · rintro (rfl | hj) <;> omega
  rw [C.content_prefix, C.content_prefix, hsets, sum_insert]
  · exact add_comm _ _
  · simp only [mem_filter, mem_univ, true_and, lt_self_iff_false, not_false_eq_true]

/-- Integral inverse prefixes with positive increments and nested content
are realized by an increasing composition of the actual digit collection. -/
theorem exists_tauMonotone_inverse_prefixes (hp : 2 ≤ p) (m : ℕ) (S : Finset (Digit p))
    (d : ℕ → ZMod s → ℤ) (hzero : ∀ h, d 0 h = 0)
    (hstep : ∀ j < m, ∀ h, 1 ≤ d (j + 1) h - d j h)
    (hcounts : ∀ j < m, ∀ h, cyclicDifference (p : ℤ) (d j) h ≤
      cyclicDifference (p : ℤ) (d (j + 1)) h)
    (hlast : PositiveContent (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S -
      cyclicDifference (p : ℤ) (d m))) :
    ∃ C : DigitComposition p s (m + 1) S, C.TauMonotone ∧
      ∀ j ≤ m, tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) =
        cyclicDifference (p : ℤ) (d j) := by
  let c := fun j => cyclicDifference (p : ℤ) (d j)
  let last := tokenContent (fun t : Digit p => (t.1 : ZMod s)) S - c m
  let u : Fin (m + 1) → ZMod s → ℤ := Fin.snoc (fun i : Fin m => c (i.val + 1) - c i.val) last
  have hc0 (h : ZMod s) : c 0 h = 0 := by simp only [c, cyclicDifference, hzero, mul_zero, sub_self]
  have hproper (i : Fin m) : DivisibleContent p (c (i.val + 1) - c i.val) := by
    have he : cyclicDifference (p : ℤ) (d (i.val + 1) - d i.val) = c (i.val + 1) - c i.val := by
      funext h
      simp only [cyclicDifference, Pi.sub_apply, c]
      ring
    rw [← he]
    apply divisibleContent_of_cyclicDifference p hp
    · exact hstep i.val i.isLt
    · intro h
      rw [he]
      exact sub_nonneg.mpr (hcounts i.val i.isLt h)
  have hu (i : Fin (m + 1)) : PositiveContent (u i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [u, Fin.snoc_last, last, c] using hlast
    · simpa only [u, Fin.snoc_castSucc] using (hproper j).1
  have hdiv (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) : DivisibleContent p (u i) := by
    have hj : i.val < m := by omega
    let j : Fin m := ⟨i.val, hj⟩
    have he : i = j.castSucc := Fin.ext rfl
    rw [he]
    simpa only [u, Fin.snoc_castSucc] using hproper j
  have hsum (h : ZMod s) : ∑ i, u i h = tokenContent (fun t : Digit p => (t.1 : ZMod s)) S h := by
    rw [Fin.sum_univ_castSucc]
    simp only [u, Fin.snoc_castSucc, Fin.snoc_last, Pi.sub_apply, last]
    rw [sum_fin_prefix_differences (fun j => c j h), hc0]
    ring
  obtain ⟨C, hC, hmono⟩ := exists_tauMonotone_content_matrix hp m S u hu hdiv hsum
  refine ⟨C, hmono, ?_⟩
  intro j
  induction j with
  | zero =>
    intro _
    funext h
    rw [C.content_prefix]
    simp only [Nat.not_lt_zero, filter_false, sum_empty, cyclicDifference, hzero,
      mul_zero, sub_self]
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    let i : Fin m := ⟨j, hjm⟩
    funext h
    have he := C.prefix_content_succ i.castSucc h
    have hi := congrFun (ih (by omega)) h
    have hval : i.castSucc.val = j := rfl
    rw [hval, hi, hC] at he
    simp only [u, Fin.snoc_castSucc, Pi.sub_apply] at he
    change _ = _ + (c (j + 1) h - c j h) at he
    change _ = c (j + 1) h
    linarith only [he]

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_tauMonotone_inverse_prefixes
