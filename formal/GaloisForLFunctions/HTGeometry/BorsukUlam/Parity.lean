import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring


/-!
# Parity lemmas for finite sets carrying free involutions

Two counting facts used by the combinatorial core of the Borsuk–Ulam theorem.

* `freeInvolution_sum_odd_parity`:  if a fixed-point-free involution `ι` stabilises a finset `N`
  and `f` is `ι`-invariant, then `∑ f` is twice a number `T`, the number of `a ∈ N` with `f a`
  odd is twice a number `U`, and `T ≡ U [MOD 2]`.  Both halves count `ι`-orbits.
* `card_four_dvd_of_klein`:  a finset carrying a free action of the Klein four-group (two
  commuting involutions whose product is also fixed-point free) has cardinality divisible by `4`.

Together they give: for a finite graph with a free involutive automorphism moving every edge,
the number of odd-degree vertices is divisible by `4`.
-/

namespace GaloisForLFunctions.BorsukUlam

open Finset

section FreeInvolution

variable {α : Type*} [DecidableEq α]

/-- Sum/odd-count pairing for a fixed-point-free involution.  `T` counts the orbit sum and `U`
counts the orbits with odd value; they have the same parity. -/
theorem freeInvolution_sum_odd_parity {ι : α → α} (hinv : ∀ a, ι (ι a) = a)
    (hfree : ∀ a, ι a ≠ a) {f : α → ℕ} (hf : ∀ a, f (ι a) = f a) :
    ∀ N : Finset α, (∀ a ∈ N, ι a ∈ N) →
      ∃ T U : ℕ, (∑ a ∈ N, f a) = 2 * T ∧
        (N.filter (fun a => f a % 2 = 1)).card = 2 * U ∧ T % 2 = U % 2 := by
  intro N
  induction N using Finset.strongInduction with
  | _ N ih =>
    intro hstab
    rcases N.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, 0, by simp, by simp, rfl⟩
    · have hia : ι a ∈ N := hstab a ha
      have hane : ι a ≠ a := hfree a
      set N' : Finset α := (N.erase a).erase (ι a) with hN'def
      have hiaerase : ι a ∈ N.erase a := mem_erase.mpr ⟨hane, hia⟩
      have hinsert1 : insert (ι a) N' = N.erase a := insert_erase hiaerase
      have hinsert2 : insert a (N.erase a) = N := insert_erase ha
      have hnotmem1 : ι a ∉ N' := notMem_erase _ _
      have hnotmem2 : a ∉ N.erase a := notMem_erase _ _
      have hsub : N' ⊂ N := by
        refine ⟨fun x hx => mem_of_mem_erase (mem_of_mem_erase hx), ?_⟩
        intro hcon
        exact hnotmem2 (mem_of_mem_erase (hcon ha))
      have hstab' : ∀ b ∈ N', ι b ∈ N' := by
        intro b hb
        have hb1 : b ∈ N.erase a := mem_of_mem_erase hb
        have hbN : b ∈ N := mem_of_mem_erase hb1
        have hbne1 : b ≠ ι a := (mem_erase.mp hb).1
        have hbne2 : b ≠ a := (mem_erase.mp hb1).1
        have hιinj : Function.Injective ι := Function.LeftInverse.injective hinv
        refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hstab b hbN⟩⟩
        · intro hcon
          exact hbne2 (hιinj hcon)
        · intro hcon
          exact hbne1 (by rw [← hinv b, hcon])
      obtain ⟨T, U, hsum, hcard, hpar⟩ := ih N' hsub hstab'
      -- the sum splits off the orbit `{a, ι a}`
      have hsumN : (∑ b ∈ N, f b) = f a + (f (ι a) + ∑ b ∈ N', f b) := by
        rw [← hinsert2, sum_insert hnotmem2, ← hinsert1, sum_insert hnotmem1]
      refine ⟨f a + T, U + (if f a % 2 = 1 then 1 else 0), ?_, ?_, ?_⟩
      · rw [hsumN, hf, hsum]; ring
      · have hfilter : N.filter (fun b => f b % 2 = 1) =
            if f a % 2 = 1 then
              insert a (insert (ι a) (N'.filter (fun b => f b % 2 = 1)))
            else N'.filter (fun b => f b % 2 = 1) := by
          rw [← hinsert2, filter_insert, ← hinsert1, filter_insert, hf]
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
        · rw [if_pos h]
          omega
        · rw [if_neg h]
          omega

end FreeInvolution

section Klein

variable {β : Type*} [DecidableEq β]

/-- A finset carrying a free action of the Klein four-group has cardinality divisible by `4`. -/
theorem card_four_dvd_of_klein {σ τ : β → β} (hσ : ∀ b, σ (σ b) = b) (hτ : ∀ b, τ (τ b) = b)
    (hcomm : ∀ b, σ (τ b) = τ (σ b)) (hσf : ∀ b, σ b ≠ b) (hτf : ∀ b, τ b ≠ b)
    (hστf : ∀ b, σ (τ b) ≠ b) :
    ∀ P : Finset β, (∀ b ∈ P, σ b ∈ P) → (∀ b ∈ P, τ b ∈ P) → 4 ∣ P.card := by
  intro P
  induction P using Finset.strongInduction with
  | _ P ih =>
    intro hsP htP
    rcases P.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · set O : Finset β := {b, σ b, τ b, σ (τ b)} with hOdef
      have hσinj : Function.Injective σ := Function.LeftInverse.injective hσ
      have hτinj : Function.Injective τ := Function.LeftInverse.injective hτ
      have h1 : b ≠ σ b := fun h => hσf b h.symm
      have h2 : b ≠ τ b := fun h => hτf b h.symm
      have h3 : b ≠ σ (τ b) := fun h => hστf b h.symm
      have h4 : σ b ≠ τ b := by
        intro h
        exact hστf b (by rw [← h, hσ])
      have h5 : σ b ≠ σ (τ b) := fun h => h2 (hσinj h)
      have h6 : τ b ≠ σ (τ b) := fun h => hσf (τ b) h.symm
      have hOcard : O.card = 4 := by
        rw [hOdef]
        rw [card_insert_of_notMem (by simp [h1, h2, h3]),
          card_insert_of_notMem (by simp [h4, h5]),
          card_insert_of_notMem (by simp [h6])]
        simp
      have hOP : O ⊆ P := by
        intro x hx
        simp only [hOdef, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hb
        · exact hsP b hb
        · exact htP b hb
        · exact hsP _ (htP b hb)
      set P' : Finset β := P \ O with hP'def
      have hsub : P' ⊂ P := by
        refine ⟨sdiff_subset, ?_⟩
        intro hcon
        have hbP' : b ∈ P' := hcon hb
        rw [hP'def, mem_sdiff] at hbP'
        exact hbP'.2 (by simp [hOdef])
      have hmemO : ∀ x, x ∈ O ↔ (x = b ∨ x = σ b ∨ x = τ b ∨ x = σ (τ b)) := by
        intro x; simp [hOdef]
      have hsP' : ∀ x ∈ P', σ x ∈ P' := by
        intro x hx
        rw [hP'def, mem_sdiff] at hx ⊢
        refine ⟨hsP x hx.1, ?_⟩
        intro hcon
        apply hx.2
        rw [hmemO] at hcon ⊢
        rcases hcon with h | h | h | h
        · exact Or.inr (Or.inl (by rw [← h, hσ]))
        · exact Or.inl (hσinj h)
        · exact Or.inr (Or.inr (Or.inr (by rw [← h, hσ])))
        · exact Or.inr (Or.inr (Or.inl (hσinj h)))
      have htP' : ∀ x ∈ P', τ x ∈ P' := by
        intro x hx
        rw [hP'def, mem_sdiff] at hx ⊢
        refine ⟨htP x hx.1, ?_⟩
        intro hcon
        apply hx.2
        rw [hmemO] at hcon ⊢
        rcases hcon with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [← h, hτ])))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [hcomm, ← h, hτ]
        · exact Or.inl (hτinj h)
        · refine Or.inr (Or.inl ?_)
          have : τ (σ (τ b)) = σ b := by rw [← hcomm, hτ]
          rw [← this, ← h, hτ]
      obtain ⟨k, hk⟩ := ih P' hsub hsP' htP'
      have hcardP : P.card = O.card + P'.card := by
        have := card_sdiff_add_card_eq_card hOP
        rw [hP'def]
        omega
      exact ⟨1 + k, by rw [hcardP, hOcard, hk]; ring⟩

end Klein

end GaloisForLFunctions.BorsukUlam
