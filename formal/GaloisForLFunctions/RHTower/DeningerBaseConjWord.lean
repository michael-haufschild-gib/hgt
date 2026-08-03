import GaloisForLFunctions.RHTower.DeningerAbsorbRight
import GaloisForLFunctions.RHTower.DeningerTransversalForm
import GaloisForLFunctions.RHTower.DeningerPushoutPower

/-!
# Base conjugates of cyclically reduced words

Conjugating a word by an element of the base group does not change the sequence of factors it runs
through: the base element is absorbed into the first letter and its inverse into the last, and both
absorptions preserve reducedness.  So a base conjugate of a cyclically reduced word is again the
product of a cyclically reduced word of the same length.

* `deningerCyc_of_map_fst` : the cyclic condition depends only on the indices.
* `deningerBaseConj_word` : the base conjugate of a word, as a word.
* `deningerBaseConj_cycRed` : the base conjugate of a cyclically reduced word is cyclically reduced.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The cyclic condition depends only on the indices.** -/
theorem deningerCyc_of_map_fst (L M : List (Σ i, G i))
    (hmap : M.map Sigma.fst = L.map Sigma.fst)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) :
    ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1 := by
  intro p hp q hq
  have h1 : M.getLast?.map Sigma.fst = L.getLast?.map Sigma.fst := by
    rw [← List.getLast?_map, ← List.getLast?_map, hmap]
  have h2 : M.head?.map Sigma.fst = L.head?.map Sigma.fst := by
    rw [← List.head?_map, ← List.head?_map, hmap]
  rw [Option.mem_def] at hp hq
  rw [hp] at h1
  rw [hq] at h2
  cases hL : L.getLast? with
  | none => rw [hL] at h1; simp at h1
  | some p' =>
    cases hL' : L.head? with
    | none => rw [hL'] at h2; simp at h2
    | some q' =>
      rw [hL] at h1
      rw [hL'] at h2
      have hp1 : p.1 = p'.1 := by simpa using h1
      have hq1 : q.1 = q'.1 := by simpa using h2
      rw [hp1, hq1]
      exact hcyc p' (by rw [hL]; rfl) q' (by rw [hL']; rfl)

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The base conjugate of a word, as a word.**  Its letters run through the same factors, so it is
cyclically reduced whenever the original is. -/
theorem deningerBaseConj_word (V : List (Σ i, G i)) (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V) (h : H) :
    ∃ L : List (Σ i, G i), L.map Sigma.fst = V.map Sigma.fst ∧
      (∀ p ∈ L, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L ∧
      PushoutI.base φ h * deningerLetterProd (φ := φ) V * (PushoutI.base φ h)⁻¹ =
        deningerLetterProd (φ := φ) L := by
  classical
  obtain ⟨M, q, hV⟩ : ∃ M q, V = M ++ [q] := by
    obtain ⟨w, hw⟩ : ∃ w, V.getLast? = some w := by
      cases hVg : V.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hVg) hVne
      | some w => exact ⟨w, rfl⟩
    exact ⟨V.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
  subst hV
  set V₁ : List (Σ i, G i) := M ++ [(⟨q.1, q.2 * φ q.1 h⁻¹⟩ : Σ i, G i)] with hV₁
  have hV₁ne : V₁ ≠ [] := by
    rw [hV₁]
    exact List.append_ne_nil_of_right_ne_nil M (by simp)
  have hV₁red : ∀ p ∈ V₁, p.2 ∉ (φ p.1).range :=
    deningerAbsorbRight_reduced M q h⁻¹ hVred
  have hV₁map : V₁.map Sigma.fst = (M ++ [q]).map Sigma.fst :=
    deningerAbsorbRight_map_fst M q h⁻¹
  refine ⟨deningerAbsorb φ h V₁, ?_, ?_, ?_, ?_⟩
  · rw [deningerAbsorb_map_fst, hV₁map]
  · exact deningerAbsorb_reduced h V₁ hV₁red
  · refine deningerIsChain_of_map_fst (M ++ [q]) (deningerAbsorb φ h V₁) ?_ hValt
    rw [deningerAbsorb_map_fst, hV₁map]
  · have hright : deningerLetterProd (φ := φ) (M ++ [q]) * (PushoutI.base φ h)⁻¹ =
        deningerLetterProd (φ := φ) V₁ := by
      rw [hV₁, ← deningerLetterProd_mul_base_snoc M q h⁻¹, map_inv]
    rw [mul_assoc, hright, deningerBase_mul_letterProd h V₁ hV₁ne]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The base conjugate of a cyclically reduced word is the product of a cyclically reduced word of
the same length.** -/
theorem deningerBaseConj_cycRed (V : List (Σ i, G i)) (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) (h : H) :
    ∃ L : List (Σ i, G i), L.length = V.length ∧ L ≠ [] ∧
      (∀ p ∈ L, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L ∧
      (∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) ∧
      PushoutI.base φ h * deningerLetterProd (φ := φ) V * (PushoutI.base φ h)⁻¹ =
        deningerLetterProd (φ := φ) L := by
  obtain ⟨L, hmap, hred, halt, hprod⟩ := deningerBaseConj_word V hVne hVred hValt h
  have hlen : L.length = V.length := by
    have := congrArg List.length hmap
    simpa using this
  refine ⟨L, hlen, ?_, hred, halt, deningerCyc_of_map_fst V L hmap hVcyc, hprod⟩
  intro hnil
  rw [hnil] at hlen
  exact hVne (List.length_eq_zero_iff.1 (by simpa using hlen.symm))

end RHTower
