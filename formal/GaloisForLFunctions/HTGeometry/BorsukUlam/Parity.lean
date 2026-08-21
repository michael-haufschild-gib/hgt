import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Parity lemmas for finite sets carrying free involutions

Two counting facts used by the combinatorial core of the Borsuk–Ulam theorem.

* `freeInvolution_sum_odd_parity`:  if a fixed-point-free involution `ι` stabilises a finset `N`
  and `f` is `ι`-invariant on `N`, then `∑ f` is twice a number `T`, the number of `a ∈ N` with
  `f a` odd is twice a number `U`, and `T ≡ U [MOD 2]`.  Both halves count `ι`-orbits.
* `card_four_dvd_of_klein`:  a finset carrying a free action of the Klein four-group (two
  commuting involutions whose product is also fixed-point free) has cardinality divisible by `4`.

Together they give: for a finite graph with a free involutive automorphism moving every edge,
the number of odd-degree vertices is divisible by `4`.

All hypotheses are localised to the finset in question, so that the maps involved need only be
involutive and fixed-point-free where it matters.
-/

set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset

section FreeInvolution

variable {α : Type*} [DecidableEq α]

/-- Sum/odd-count pairing for a fixed-point-free involution.  `T` counts the orbit sum and `U`
counts the orbits with odd value; they have the same parity. -/
theorem freeInvolution_sum_odd_parity {ι : α → α} {f : α → ℕ} :
    ∀ N : Finset α, (∀ a ∈ N, ι a ∈ N) → (∀ a ∈ N, ι (ι a) = a) → (∀ a ∈ N, ι a ≠ a) →
      (∀ a ∈ N, f (ι a) = f a) →
      ∃ T U : ℕ, (∑ a ∈ N, f a) = 2 * T ∧
        (N.filter (fun a => f a % 2 = 1)).card = 2 * U ∧ T % 2 = U % 2 := by
  intro N
  induction N using Finset.strongInduction with
  | _ N ih =>
    intro hstab hinv hfree hf
    rcases N.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, 0, by simp, by simp, rfl⟩
    · have hia : ι a ∈ N := hstab a ha
      have hane : ι a ≠ a := hfree a ha
      set N' : Finset α := (N.erase a).erase (ι a) with hN'def
      have hiaerase : ι a ∈ N.erase a := mem_erase.mpr ⟨hane, hia⟩
      have hinsert1 : insert (ι a) N' = N.erase a := insert_erase hiaerase
      have hinsert2 : insert a (N.erase a) = N := insert_erase ha
      have hnotmem1 : ι a ∉ N' := notMem_erase _ _
      have hnotmem2 : a ∉ N.erase a := notMem_erase _ _
      have hsubN : N' ⊆ N := fun x hx => mem_of_mem_erase (mem_of_mem_erase hx)
      have hsub : N' ⊂ N := by
        refine ⟨hsubN, ?_⟩
        intro hcon
        exact hnotmem2 (mem_of_mem_erase (hcon ha))
      have hstab' : ∀ b ∈ N', ι b ∈ N' := by
        intro b hb
        have hb1 : b ∈ N.erase a := mem_of_mem_erase hb
        have hbN : b ∈ N := mem_of_mem_erase hb1
        have hbne1 : b ≠ ι a := (mem_erase.mp hb).1
        have hbne2 : b ≠ a := (mem_erase.mp hb1).1
        refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hstab b hbN⟩⟩
        · intro hcon
          apply hbne2
          rw [← hinv b hbN, hcon, hinv a ha]
        · intro hcon
          apply hbne1
          rw [← hinv b hbN, hcon]
      obtain ⟨T, U, hsum, hcard, hpar⟩ := ih N' hsub hstab' (fun b hb => hinv b (hsubN hb))
        (fun b hb => hfree b (hsubN hb)) (fun b hb => hf b (hsubN hb))
      have hsumN : (∑ b ∈ N, f b) = f a + (f (ι a) + ∑ b ∈ N', f b) := by
        rw [← hinsert2, sum_insert hnotmem2, ← hinsert1, sum_insert hnotmem1]
      refine ⟨f a + T, U + (if f a % 2 = 1 then 1 else 0), ?_, ?_, ?_⟩
      · rw [hsumN, hf a ha, hsum]; ring
      · have hfilter : N.filter (fun b => f b % 2 = 1) =
            if f a % 2 = 1 then
              insert a (insert (ι a) (N'.filter (fun b => f b % 2 = 1)))
            else N'.filter (fun b => f b % 2 = 1) := by
          rw [← hinsert2, filter_insert, ← hinsert1, filter_insert, hf a ha]
          by_cases h : f a % 2 = 1 <;> simp [h]
        rw [hfilter]
        by_cases h : f a % 2 = 1
        · rw [if_pos h, if_pos h, card_insert_of_notMem, card_insert_of_notMem, hcard]
          · ring
          · exact fun hcon => hnotmem1 (mem_of_mem_filter _ hcon)
          · intro hcon
            rcases mem_insert.mp hcon with h1 | h1
            · exact hane h1.symm
            · exact hnotmem2 (mem_of_mem_erase (mem_of_mem_filter _ h1))
        · rw [if_neg h, if_neg h, hcard]; ring
      · by_cases h : f a % 2 = 1
        · rw [if_pos h]; omega
        · rw [if_neg h]; omega

end FreeInvolution

section Klein

variable {β : Type*} [DecidableEq β]

/-- A finset carrying a free action of the Klein four-group has cardinality divisible by `4`. -/
theorem card_four_dvd_of_klein {σ τ : β → β} :
    ∀ P : Finset β, (∀ b ∈ P, σ b ∈ P) → (∀ b ∈ P, τ b ∈ P) →
      (∀ b ∈ P, σ (σ b) = b) → (∀ b ∈ P, τ (τ b) = b) → (∀ b ∈ P, σ (τ b) = τ (σ b)) →
      (∀ b ∈ P, σ b ≠ b) → (∀ b ∈ P, τ b ≠ b) → (∀ b ∈ P, σ (τ b) ≠ b) → 4 ∣ P.card := by
  intro P
  induction P using Finset.strongInduction with
  | _ P ih =>
    intro hsP htP hσ hτ hcomm hσf hτf hστf
    rcases P.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · have hσb : σ b ∈ P := hsP b hb
      have hτb : τ b ∈ P := htP b hb
      have hστb : σ (τ b) ∈ P := hsP _ hτb
      set O : Finset β := {b, σ b, τ b, σ (τ b)} with hOdef
      have h1 : b ≠ σ b := fun h => hσf b hb h.symm
      have h2 : b ≠ τ b := fun h => hτf b hb h.symm
      have h3 : b ≠ σ (τ b) := fun h => hστf b hb h.symm
      have h4 : σ b ≠ τ b := by
        intro h
        exact hστf b hb (by rw [← h, hσ b hb])
      have h5 : σ b ≠ σ (τ b) := by
        intro h
        apply h2
        have := congrArg σ h
        rwa [hσ b hb, hσ _ hτb] at this
      have h6 : τ b ≠ σ (τ b) := fun h => hσf _ hτb h.symm
      have hOcard : O.card = 4 := by
        rw [hOdef, card_insert_of_notMem (by simp [h1, h2, h3]),
          card_insert_of_notMem (by simp [h4, h5]), card_insert_of_notMem (by simp [h6])]
        simp
      have hOP : O ⊆ P := by
        intro x hx
        simp only [hOdef, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hb
        · exact hσb
        · exact hτb
        · exact hστb
      set P' : Finset β := P \ O with hP'def
      have hsubP : P' ⊆ P := sdiff_subset
      have hsub : P' ⊂ P := by
        refine ⟨hsubP, ?_⟩
        intro hcon
        have hbP' : b ∈ P' := hcon hb
        rw [hP'def, mem_sdiff] at hbP'
        exact hbP'.2 (by simp [hOdef])
      have hmemO : ∀ x, x ∈ O ↔ (x = b ∨ x = σ b ∨ x = τ b ∨ x = σ (τ b)) := by
        intro x; simp [hOdef]
      have hsP' : ∀ x ∈ P', σ x ∈ P' := by
        intro x hx
        rw [hP'def, mem_sdiff] at hx ⊢
        have hxP : x ∈ P := hx.1
        refine ⟨hsP x hxP, ?_⟩
        intro hcon
        apply hx.2
        rw [hmemO] at hcon ⊢
        rcases hcon with h | h | h | h
        · refine Or.inr (Or.inl ?_)
          have := congrArg σ h
          rwa [hσ x hxP] at this
        · refine Or.inl ?_
          have := congrArg σ h
          rwa [hσ x hxP, hσ b hb] at this
        · refine Or.inr (Or.inr (Or.inr ?_))
          have := congrArg σ h
          rwa [hσ x hxP] at this
        · refine Or.inr (Or.inr (Or.inl ?_))
          have := congrArg σ h
          rwa [hσ x hxP, hσ _ hτb] at this
      have htP' : ∀ x ∈ P', τ x ∈ P' := by
        intro x hx
        rw [hP'def, mem_sdiff] at hx ⊢
        have hxP : x ∈ P := hx.1
        refine ⟨htP x hxP, ?_⟩
        intro hcon
        apply hx.2
        rw [hmemO] at hcon ⊢
        rcases hcon with h | h | h | h
        · refine Or.inr (Or.inr (Or.inl ?_))
          have := congrArg τ h
          rwa [hτ x hxP] at this
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hh := congrArg τ h
          rw [hτ x hxP] at hh
          rw [hh, hcomm b hb]
        · refine Or.inl ?_
          have := congrArg τ h
          rwa [hτ x hxP, hτ b hb] at this
        · refine Or.inr (Or.inl ?_)
          have hh := congrArg τ h
          rw [hτ x hxP] at hh
          rw [hh, ← hcomm _ hτb, hτ b hb]
      obtain ⟨k, hk⟩ := ih P' hsub hsP' htP' (fun x hx => hσ x (hsubP hx))
        (fun x hx => hτ x (hsubP hx)) (fun x hx => hcomm x (hsubP hx))
        (fun x hx => hσf x (hsubP hx)) (fun x hx => hτf x (hsubP hx))
        (fun x hx => hστf x (hsubP hx))
      have hcardP : P.card = O.card + P'.card := by
        have hh := card_sdiff_add_card_eq_card hOP
        rw [hP'def]
        omega
      exact ⟨1 + k, by rw [hcardP, hOcard, hk]; ring⟩

end Klein

end GaloisForLFunctions.BorsukUlam
