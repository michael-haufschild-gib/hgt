import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IncreasingAllocations

/-!
# Realizing a prescribed digit-content matrix

Nonnegative positive columns summing to the available digit content can be
allocated to actual digits. Divisibility of the proper columns produces an
admissible composition; maximizing within the content fibre gives increasing
allocations in each residue class.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s : ℕ} [NeZero s]

/-- Every admissible content matrix is realized by a partition of the actual digits. -/
theorem exists_content_matrix (hp : 2 ≤ p) (m : ℕ) (S : Finset (Digit p))
    (u : Fin (m + 1) → ZMod s → ℤ) (hu : ∀ i, PositiveContent (u i))
    (hdiv : ∀ i, i.val + 1 < m + 1 → DivisibleContent p (u i))
    (hsum : ∀ h, ∑ i, u i h = tokenContent (fun x : Digit p => (x.1 : ZMod s)) S h) :
    ∃ C : DigitComposition p s (m + 1) S, C.content = u := by
  induction m generalizing S with
  | zero =>
    have he : tokenContent (fun x : Digit p => (x.1 : ZMod s)) S = u 0 := by
      funext h
      simpa only [Fin.sum_univ_one] using (hsum h).symm
    have hS : S.Nonempty := (positive_tokenContent_iff _ _).mp (he.symm ▸ hu 0)
    refine ⟨single hS, ?_⟩
    funext i h
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
    change tokenContent (fun x : Digit p => (x.1 : ZMod s)) S h = u i h
    rw [hi]
    exact congrFun he h
  | succ m ih =>
    have hle (h : ZMod s) : u 0 h ≤ tokenContent (fun x : Digit p => (x.1 : ZMod s)) S h := by
      rw [← hsum h]
      exact single_le_sum (fun i _ => (hu i).1 h) (mem_univ 0)
    obtain ⟨T, hT, ht⟩ := exists_subset_tokenContent
      (fun x : Digit p => (x.1 : ZMod s)) S (u 0) (hu 0).1 hle
    have hJ : DivisibleContent p (tokenContent (fun x : Digit p => (x.1 : ZMod s)) T) := by
      rw [ht]
      exact hdiv 0 (by simp)
    obtain ⟨hne, hdvd⟩ := (divisibleContent_tokens_iff p hp Prod.fst T).mp hJ
    have hs (h : ZMod s) : ∑ i : Fin (m + 1), u i.succ h =
        tokenContent (fun x : Digit p => (x.1 : ZMod s)) (S \ T) h := by
      have he := hsum h
      rw [Fin.sum_univ_succ] at he
      rw [tokenContent_sdiff _ hT, ht]
      dsimp only [Pi.sub_apply]
      linarith only [he]
    obtain ⟨C, hc⟩ := ih (S \ T) (fun i => u i.succ) (fun i => hu i.succ)
      (fun i hi => hdiv i.succ (by simpa only [Fin.val_succ] using Nat.add_lt_add_right hi 1)) hs
    refine ⟨prepend hT hne hdvd C, ?_⟩
    funext i h
    cases i using Fin.cases with
    | zero => exact congrFun ht h
    | succ i => exact congrFun (congrFun hc i) h

/-- A prescribed admissible content matrix has an increasing digit allocation. -/
theorem exists_tauMonotone_content_matrix (hp : 2 ≤ p) (m : ℕ) (S : Finset (Digit p))
    (u : Fin (m + 1) → ZMod s → ℤ) (hu : ∀ i, PositiveContent (u i))
    (hdiv : ∀ i, i.val + 1 < m + 1 → DivisibleContent p (u i))
    (hsum : ∀ h, ∑ i, u i h = tokenContent (fun x : Digit p => (x.1 : ZMod s)) S h) :
    ∃ C : DigitComposition p s (m + 1) S, C.content = u ∧ C.TauMonotone := by
  obtain ⟨C, hc⟩ := exists_content_matrix hp m S u hu hdiv hsum
  obtain ⟨D, hd, hm⟩ := C.exists_tauMonotone_same_content hp
  exact ⟨D, hd.trans hc, hm⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_tauMonotone_content_matrix
