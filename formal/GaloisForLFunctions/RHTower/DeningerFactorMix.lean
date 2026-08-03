import GaloisForLFunctions.RHTower.DeningerRootFactor

/-!
# Roots of elements of the factors, over a mixing hypothesis

Isolation of the base group in every factor is more than uniqueness of roots for elements of the
factors needs.  What the argument uses is only this: when two elements of different factors have
the same power and that power lies in the base group, both elements lie in the base group.  Stating
the hypothesis in that form makes it available to amalgams in which one factor is not isolated over
its base, which is the case for a root adjunction.

* `deningerPow_eq_of_factors_mix` : uniqueness of roots for elements of the factors.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Uniqueness of roots for elements of the factors**, over a hypothesis on the elements of two
different factors whose common power lies in the base group. -/
theorem deningerPow_eq_of_factors_mix (hφ : ∀ i, Function.Injective (φ i))
    (hH : ∀ (a b : H) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (hG : ∀ (i : ι) (a b : G i) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (hmix : ∀ (i j : ι), i ≠ j → ∀ (a : G i) (b : G j) (n : ℕ), 0 < n →
      a ^ n ∈ (φ i).range → b ^ n ∈ (φ j).range →
      PushoutI.of (φ := φ) i (a ^ n) = PushoutI.of (φ := φ) j (b ^ n) →
      a ∈ (φ i).range ∧ b ∈ (φ j).range)
    (i j : ι) (a : G i) (b : G j) (n : ℕ) (hn : 0 < n)
    (h : (PushoutI.of (φ := φ) i a) ^ n = (PushoutI.of (φ := φ) j b) ^ n) :
    PushoutI.of (φ := φ) i a = PushoutI.of (φ := φ) j b := by
  classical
  have hpow : PushoutI.of (φ := φ) i (a ^ n) = PushoutI.of (φ := φ) j (b ^ n) := by
    rw [map_pow, map_pow]
    exact h
  by_cases hij : i = j
  · subst hij
    have hab : a ^ n = b ^ n := PushoutI.of_injective hφ i hpow
    rw [hG i a b n hn hab]
  · by_cases hmem : a ^ n ∈ (φ i).range
    · have hbmem : b ^ n ∈ (φ j).range := by
        refine (deningerMem_baseRange_iff (φ := φ) hφ j (b ^ n)).1 ?_
        rw [← hpow]
        exact (deningerMem_baseRange_iff (φ := φ) hφ i (a ^ n)).2 hmem
      obtain ⟨ha, hb⟩ := hmix i j hij a b n hn hmem hbmem hpow
      obtain ⟨s, hs⟩ := ha
      obtain ⟨t, ht⟩ := hb
      have hx : deningerLen d (PushoutI.of (φ := φ) i a) = 0 := by
        rw [← hs, PushoutI.of_apply_eq_base, deningerLen_base]
      have hy : deningerLen d (PushoutI.of (φ := φ) j b) = 0 := by
        rw [← ht, PushoutI.of_apply_eq_base, deningerLen_base]
      exact deningerPow_eq_of_len_zero (d := d) hφ hH _ _ hx hy n hn h
    · exfalso
      by_cases hmem' : b ^ n ∈ (φ j).range
      · refine hmem ?_
        refine (deningerMem_baseRange_iff (φ := φ) hφ i (a ^ n)).1 ?_
        rw [hpow]
        exact (deningerMem_baseRange_iff (φ := φ) hφ j (b ^ n)).2 hmem'
      · refine hij ?_
        have hprod : deningerLetterProd (φ := φ) [(⟨i, a ^ n⟩ : Σ i, G i)] =
            deningerLetterProd (φ := φ) [(⟨j, b ^ n⟩ : Σ i, G i)] := by
          rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one,
            deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
          exact hpow
        have := deningerWords_map_fst_eq (d := d)
          [(⟨i, a ^ n⟩ : Σ i, G i)] [(⟨j, b ^ n⟩ : Σ i, G i)]
          (by simpa using hmem) (List.isChain_singleton _) (by simpa using hmem')
          (List.isChain_singleton _) hprod
        simpa using this

end RHTower
