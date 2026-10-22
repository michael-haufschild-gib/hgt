import GaloisForLFunctions.RHTower.Deninger.DeningerPrefixTransferGen

/-!
# Reassembling the cyclic reduction data after a step

Given the data of the word obtained by one cyclic reduction step, the data of the original word is
obtained by prepending the stripped letter to the conjugator and taking the corresponding suffix as
the tail.  The step may replace the last letter by one letter or by two; only the first letter of
the replacement matters.

* `deningerCycData_reassemble` : the reassembly.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The reassembly.** -/
theorem deningerCycData_reassemble (j : ι) (z : G j) (M T C₁ R₁ V : List (Σ i, G i))
    (a : Σ i, G i)
    (hstep : deningerLetterProd (φ := φ) (M ++ [a]) =
      (PushoutI.of j z)⁻¹ *
        deningerLetterProd (φ := φ) ((⟨j, z⟩ : Σ i, G i) :: (M ++ T)) * PushoutI.of j z)
    (hsplit : C₁ ++ R₁ = M ++ [a]) (hR₁ : R₁ ≠ [])
    (hhead : V.head?.map Sigma.fst = R₁.head?.map Sigma.fst)
    (hprod : deningerLetterProd (φ := φ) R₁ =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C₁)⁻¹)
    (hT : T.head?.map Sigma.fst = ([a] : List (Σ i, G i)).head?.map Sigma.fst)
    (hTne : T ≠ []) :
    ((⟨j, z⟩ : Σ i, G i) :: (M ++ T) = ((⟨j, z⟩ : Σ i, G i) :: C₁) ++ ((M ++ T).drop C₁.length)) ∧
      ((M ++ T).drop C₁.length ≠ []) ∧
      (V.head?.map Sigma.fst = ((M ++ T).drop C₁.length).head?.map Sigma.fst) ∧
      deningerLetterProd (φ := φ) ((M ++ T).drop C₁.length) =
        deningerLetterProd (φ := φ) V *
          (deningerLetterProd (φ := φ) ((⟨j, z⟩ : Σ i, G i) :: C₁))⁻¹ := by
  have hle : C₁.length ≤ M.length := deningerPrefix_le C₁ R₁ M a hsplit hR₁
  have htake : C₁ = M.take C₁.length := deningerPrefix_take C₁ R₁ M [a] hsplit hle
  have hMT : C₁ ++ ((M ++ T).drop C₁.length) = M ++ T :=
    deningerPrefix_transfer' C₁ M T hle htake
  have hRne : (M ++ T).drop C₁.length ≠ [] := by
    intro hnil
    have hlen : ((M ++ T).drop C₁.length).length = (M ++ T).length - C₁.length :=
      List.length_drop (l := M ++ T) (i := C₁.length)
    rw [hnil] at hlen
    simp only [List.length_nil, List.length_append] at hlen
    have hTpos : 0 < T.length := List.length_pos_iff.2 hTne
    omega
  refine ⟨by rw [List.cons_append, hMT], hRne, ?_, ?_⟩
  · rw [hhead]
    exact deningerHead_map_fst_of_append' C₁ R₁ _ M [a] T hsplit hMT hle hT.symm
  · refine deningerCycData_step (⟨j, z⟩ : Σ i, G i) C₁ V R₁ _ hprod ?_
    have hL : deningerLetterProd (φ := φ) ((⟨j, z⟩ : Σ i, G i) :: (M ++ T)) =
        PushoutI.of j z * (deningerLetterProd (φ := φ) C₁ *
          deningerLetterProd (φ := φ) ((M ++ T).drop C₁.length)) := by
      rw [deningerLetterProd_cons, ← deningerLetterProd_append, hMT]
    have hstep' : deningerLetterProd (φ := φ) (C₁ ++ R₁) =
        (PushoutI.of j z)⁻¹ * (PushoutI.of j z * (deningerLetterProd (φ := φ) C₁ *
          deningerLetterProd (φ := φ) ((M ++ T).drop C₁.length))) * PushoutI.of j z := by
      rw [hsplit, hstep, hL]
    rw [deningerLetterProd_append] at hstep'
    have hcancel : deningerLetterProd (φ := φ) C₁ * deningerLetterProd (φ := φ) R₁ =
        deningerLetterProd (φ := φ) C₁ *
          (deningerLetterProd (φ := φ) ((M ++ T).drop C₁.length) * PushoutI.of j z) := by
      rw [hstep']
      group
    have hRR := mul_left_cancel hcancel
    rw [hRR]
    group

end RHTower
